//! The RPC command surface, part one: the dispatch table plus the state,
//! abort, new-session, compaction, refinement, and settings-toggle
//! handlers (TS `rpc-mode.ts`'s `handleCommand` cases). Prompting lives in
//! [`super::prompt_commands`], model/thinking/queue switches in
//! [`super::model_commands`], session-level and scheduling commands in
//! [`super::session_commands`].

use std::sync::Arc;

use eukhe_core::durable::goals::goal_state;
use eukhe_core::durable::rlm::{refine_now, RefineRequest};
use eukhe_core::durable::EukheSession;
use eukhe_core::settings::QueueModeSetting;
use eukhe_core::settings::SettingsManager;
use eukhe_durable::harness::types::ConversationAbortOptions;
use eukhe_durable::harness::InboxItem;
use serde_json::{json, Value};

use super::model_commands;
use super::prompt_commands;
use super::protocol::{self, ResponseData};
use super::reads::{
    agent_model, content_preview, context_messages, inbox_state, is_busy, live_state, main_agent,
    rpc_context,
};
use super::session::{RpcEngineRequest, RpcSession};
use super::session_commands;
use super::LineWriter;
use crate::compaction::durable::{run_manual_compaction, ManualCompactionError};
use crate::worker::durable_host::meta::read_session_meta;

/// The shared handler state: the live session plus the command lanes.
pub struct RpcState {
    pub session: Arc<RpcSession>,
    pub writer: LineWriter,
    /// The model-selection commands' serialization lane (TS runs every
    /// command on one loop: `set_model`/`cycle_model` and the thinking
    /// switches serialize read-then-apply instead of racing).
    pub model_ops: tokio::sync::Mutex<()>,
    /// The context-rebuilding commands' serialization lane (`compact`,
    /// `refine`, and the prompt-admitted session commands).
    pub session_ops: tokio::sync::Mutex<()>,
}

/// A settings manager over the live session's project (TS builds every
/// session's `SettingsManager` over the session's own cwd): the settings
/// writes follow it, so after a `switch_session`/`fork` adopts another
/// project the persisted defaults land there, not under the CLI startup
/// directory. The session's settings source re-reads the files when they
/// change, so a write here is the live change too.
pub(crate) fn settings_for(session: &EukheSession) -> SettingsManager {
    let deps = session.deps();
    SettingsManager::create(&deps.cwd, &deps.agent_dir)
}

/// Dispatch one command to its handler; the unknown-type error answers
/// with no id (TS `handleCommand`'s default arm).
pub async fn handle_command(state: &Arc<RpcState>, command: protocol::RpcCommand) -> Value {
    let id = command.id.clone();
    let payload = command.payload.clone();
    let name = command.command.as_str();
    let outcome: Result<ResponseData, String> = match name {
        "prompt" => prompt_commands::prompt(state, &payload).await,
        "steer" | "follow_up" => prompt_commands::steer_or_follow_up(state, &payload, name).await,
        "abort" => state.session.abort().await.map(|()| ResponseData::Absent),
        "new_session" => new_session(state).await,
        "get_state" => get_state(state).await,
        "set_model" => model_commands::set_model(state, &payload).await,
        "cycle_model" => model_commands::cycle_model(state).await,
        "get_available_models" => model_commands::get_available_models(state).await,
        "set_thinking_level" => model_commands::set_thinking_level(state, &payload).await,
        "cycle_thinking_level" => model_commands::cycle_thinking_level(state).await,
        "set_steering_mode" | "set_follow_up_mode" => {
            model_commands::set_queue_mode(state, &payload, name).await
        }
        "compact" => compact(state, &payload).await,
        "refine" => refine(state, &payload).await,
        "set_auto_compaction" => set_auto_compaction(state, &payload).await,
        "set_auto_retry" => set_auto_retry(state, &payload).await,
        // TS `abortRetry` always answers success (it aborts only an
        // in-flight retry; the durable retry backoff ends with the abort
        // of its run).
        "abort_retry" => Ok(ResponseData::Absent),
        other => session_commands::handle(state, other, &payload).await,
    };
    match outcome {
        Ok(data) => protocol::success(id.as_ref(), name, data),
        Err(message) => protocol::error(id.as_ref(), name, &message),
    }
}

/// `new_session` (TS `runtimeHost.newSession`): a fresh session over the
/// ACTIVE session's project. A `parentSession` is accepted for protocol
/// compatibility but has no durable record to land in (durable storage
/// carries no session header with a parent link).
async fn new_session(state: &Arc<RpcState>) -> Result<ResponseData, String> {
    // Serialize the cwd sample with the replacement it seeds: a
    // `switch_session` landing between them would build the session over
    // the retired session's project.
    let lease = state.session.replacement_lease().await;
    let cwd = state.session.session().await.deps().cwd.clone();
    let outcome = state
        .session
        .replace_locked(RpcEngineRequest::New { cwd: Some(cwd) })
        .await;
    drop(lease);
    outcome?;
    Ok(ResponseData::Present(json!({ "cancelled": false })))
}

/// The wire name of a queue mode setting (TS `"all"`/`"one-at-a-time"`).
pub(crate) fn queue_mode_wire_name(mode: QueueModeSetting) -> &'static str {
    match mode {
        QueueModeSetting::All => "all",
        QueueModeSetting::OneAtATime => "one-at-a-time",
    }
}

/// `get_state` (TS `RpcSessionState`) over the main conversation.
async fn get_state(state: &Arc<RpcState>) -> Result<ResponseData, String> {
    let handle = state.session.handle().await;
    let session = &handle.session;
    let harness = session.harness();
    let deps = session.deps();
    let cx = rpc_context();
    let main = session.main();
    let agent = main_agent(session, &cx).await?;
    let live = live_state(harness, main.id(), &cx).await?;
    let inbox = inbox_state(harness, main.id(), &cx).await?;
    let messages = context_messages(&main, &cx).await?;
    let meta = read_session_meta(harness, &cx)
        .await
        .map_err(|error| error.to_string())?;
    let goal = goal_state(harness, main.id(), &cx)
        .await
        .map_err(|error| error.to_string())?;
    let settings = deps.settings.manager();

    let mut object = serde_json::Map::new();
    if let Some(model) = agent_model(session, &agent) {
        object.insert(
            "model".to_string(),
            serde_json::to_value(model).map_err(|error| error.to_string())?,
        );
    }
    object.insert(
        "thinkingLevel".to_string(),
        json!(agent.thinking_level.as_str()),
    );
    let streaming = live.run.is_some();
    object.insert("isStreaming".to_string(), json!(streaming));
    object.insert(
        "isCompacting".to_string(),
        json!(live
            .compactions
            .as_ref()
            .is_some_and(|compactions| !compactions.is_empty())),
    );
    object.insert(
        "steeringMode".to_string(),
        json!(queue_mode_wire_name(settings.get_steering_mode())),
    );
    object.insert(
        "followUpMode".to_string(),
        json!(queue_mode_wire_name(settings.get_follow_up_mode())),
    );
    if let Some(dir) = &deps.storage_dir {
        object.insert("sessionFile".to_string(), json!(dir.display().to_string()));
    }
    object.insert("sessionId".to_string(), json!(deps.session_id));
    if let Some(name) = meta.name {
        object.insert("sessionName".to_string(), json!(name));
    }
    object.insert(
        "autoCompactionEnabled".to_string(),
        json!(settings.get_compaction_enabled()),
    );
    object.insert("messageCount".to_string(), json!(messages.len()));
    object.insert(
        "sessionActions".to_string(),
        session_actions_snapshot(&inbox.items, streaming),
    );
    object.insert(
        "goal".to_string(),
        serde_json::to_value(goal).map_err(|error| error.to_string())?,
    );
    Ok(ResponseData::Present(Value::Object(object)))
}

/// The TS `SessionActionSnapshot` over the conversation's inbox: one
/// preview per queued input, the total, and the running turn as the
/// active action. Queued passive writes are not session actions.
fn session_actions_snapshot(items: &[InboxItem], streaming: bool) -> Value {
    let mut steering = Vec::new();
    let mut follow_ups = Vec::new();
    for item in items {
        match item {
            InboxItem::Steer { content, .. } => steering.push(content_preview(content)),
            InboxItem::FollowUp { content, .. } => follow_ups.push(content_preview(content)),
            InboxItem::Write { .. } => {}
        }
    }
    let mut snapshot = json!({
        "queuedCount": steering.len() + follow_ups.len(),
        "steering": steering,
        "followUps": follow_ups,
    });
    if streaming {
        snapshot["active"] = json!({ "kind": "turn", "phase": "running" });
    }
    snapshot
}

/// `compact` (TS `session.compact(customInstructions)`): abort the
/// running turn, run a manual durable compaction and answer with the TS
/// `CompactionResult`; a skip answers the TS `CompactionSkippedError`
/// message with the compaction frames around it (a compaction that ran
/// publishes its own frames through the event pump).
async fn compact(state: &Arc<RpcState>, payload: &Value) -> Result<ResponseData, String> {
    let instructions = payload
        .get("customInstructions")
        .and_then(Value::as_str)
        .map(str::to_string);
    // The handle guard stays held through the compaction: a concurrent
    // whole-session replacement cannot close the session mid-compaction.
    let handle = state.session.handle().await;
    let session = &handle.session;
    let main = session.main();
    let cx = rpc_context();
    let _ops = state.session_ops.lock().await;
    // TS `session.compact` aborts the running turn before the snapshot:
    // the compaction summarizes a settled transcript.
    if !matches!(is_busy(session.harness(), main.id(), &cx).await, Ok(false)) {
        main.abort(ConversationAbortOptions::default(), &cx)
            .await
            .map_err(|error| error.to_string())?;
    }
    match run_manual_compaction(
        session.harness(),
        session.deps(),
        &main,
        instructions.clone(),
        &cx,
    )
    .await
    {
        Ok(result) => Ok(ResponseData::Present(result)),
        Err(ManualCompactionError::Skipped(message)) => {
            let outputs = state.session.outputs();
            outputs.write(compaction_frame(
                "compaction_start",
                instructions.as_deref(),
                None,
            ));
            outputs.write(compaction_frame(
                "compaction_end",
                instructions.as_deref(),
                None,
            ));
            Err(message.to_string())
        }
        Err(error) => Err(error.to_string()),
    }
}

/// One manual-compaction frame (pi-durable's `manual` reason, as the
/// translated compaction events carry it) in the TS key order, omitting the
/// optional fields that are absent (TS `JSON.stringify`'s `undefined`
/// handling): `compaction_start {type, reason, customInstructions?}` and
/// `compaction_end {type, reason, result?, aborted, willRetry,
/// customInstructions?}`.
#[must_use]
pub fn compaction_frame(kind: &str, instructions: Option<&str>, result: Option<&Value>) -> Value {
    let mut frame = json!({ "type": kind, "reason": "manual" });
    if kind != "compaction_start" {
        if let Some(result) = result {
            frame["result"] = result.clone();
        }
        frame["aborted"] = json!(false);
        frame["willRetry"] = json!(false);
    }
    if let Some(instructions) = instructions {
        frame["customInstructions"] = json!(instructions);
    }
    frame
}

/// `refine` (TS `session.refine`): run the refinement on the main
/// conversation and answer with the `RefinementResult`.
async fn refine(state: &Arc<RpcState>, payload: &Value) -> Result<ResponseData, String> {
    let request = RefineRequest {
        global: payload
            .get("global")
            .and_then(Value::as_bool)
            .unwrap_or(false),
        instructions: payload
            .get("instructions")
            .and_then(Value::as_str)
            .map(str::to_string),
        rollback_id: payload
            .get("rollbackId")
            .and_then(Value::as_str)
            .map(str::to_string),
    };
    let handle = state.session.handle().await;
    let session = &handle.session;
    let _ops = state.session_ops.lock().await;
    let result = refine_now(session.deps(), &session.main(), request, &rpc_context())
        .await
        .map_err(|error| format!("{error:#}"))?;
    Ok(ResponseData::Present(
        serde_json::to_value(result).map_err(|error| error.to_string())?,
    ))
}

/// `set_auto_compaction` (TS `session.setAutoCompactionEnabled`): the
/// settings default the session's compaction policy reads.
async fn set_auto_compaction(
    state: &Arc<RpcState>,
    payload: &Value,
) -> Result<ResponseData, String> {
    let enabled = payload
        .get("enabled")
        .and_then(Value::as_bool)
        .ok_or_else(|| "set_auto_compaction requires enabled".to_string())?;
    settings_for(&*state.session.session().await)
        .set_compaction_enabled(enabled)
        .map_err(|error| error.to_string())?;
    Ok(ResponseData::Absent)
}

/// `set_auto_retry` (TS `session.setAutoRetryEnabled`): the settings
/// toggle the session retry policy reads.
async fn set_auto_retry(state: &Arc<RpcState>, payload: &Value) -> Result<ResponseData, String> {
    let enabled = payload
        .get("enabled")
        .and_then(Value::as_bool)
        .ok_or_else(|| "set_auto_retry requires enabled".to_string())?;
    settings_for(&*state.session.session().await)
        .set_retry_enabled(enabled)
        .map_err(|error| error.to_string())?;
    Ok(ResponseData::Absent)
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_durable::types::SubmissionId;
    use eukhe_types::pi_ai::UserContent;

    #[test]
    fn session_actions_preview_queued_inputs_only() {
        let items = vec![
            InboxItem::Steer {
                id: SubmissionId::from_number(1),
                content: UserContent::Text("steer this".into()),
            },
            InboxItem::Write {
                id: SubmissionId::from_number(2),
                entry: eukhe_chord::json::JsonValue::Null,
            },
            InboxItem::FollowUp {
                id: SubmissionId::from_number(3),
                content: UserContent::Text("fu this".into()),
            },
        ];
        assert_eq!(
            session_actions_snapshot(&items, true),
            json!({
                "queuedCount": 2,
                "steering": ["steer this"],
                "followUps": ["fu this"],
                "active": { "kind": "turn", "phase": "running" },
            })
        );
        assert_eq!(
            session_actions_snapshot(&[], false),
            json!({ "queuedCount": 0, "steering": [], "followUps": [] })
        );
    }

    #[test]
    fn compaction_frames_keep_the_ts_key_order() {
        let start = compaction_frame("compaction_start", Some("focus"), None);
        assert_eq!(
            serde_json::to_string(&start).unwrap(),
            r#"{"type":"compaction_start","reason":"manual","customInstructions":"focus"}"#
        );
        let end = compaction_frame("compaction_end", None, None);
        assert_eq!(
            serde_json::to_string(&end).unwrap(),
            r#"{"type":"compaction_end","reason":"manual","aborted":false,"willRetry":false}"#
        );
    }
}
