//! The RPC command surface, part one: the dispatch table plus the state,
//! abort, new-session, compaction, refinement, and settings-toggle
//! handlers (TS `rpc-mode.ts`'s `handleCommand` cases). Prompting lives in
//! [`super::prompt_commands`], model/thinking/queue switches in
//! [`super::model_commands`], session-level and scheduling commands in
//! [`super::session_commands`].

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_core::durable::acceptance::acceptance_state;
use eukhe_core::durable::cvar_agent::{run_cvar_line, CvarLineScope};
use eukhe_core::durable::goals::goal_state;
use eukhe_core::durable::loop_mode::{
    hold_loop_for_compaction, loop_status, resume_loop_after_compaction,
};
use eukhe_core::durable::rlm::{refine_now, RefineRequest};
use eukhe_core::durable::EukheSession;
use eukhe_core::settings::cvar::{table, Decl};
use eukhe_core::settings::QueueModeSetting;
use eukhe_core::settings::SettingsManager;
use eukhe_durable::harness::{Conversation, InboxItem};
use eukhe_types::cvar::Command;
use eukhe_types::daemon::{CompactionReason, SessionEvent};
use serde_json::{json, Value};

use super::budget_commands;
use super::error::RpcCommandError;
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
use crate::compaction::durable::{
    interrupt_turn, resumes_interrupted_turn, run_manual_compaction, submit_auto_continue,
    ManualCompactionError,
};
use crate::worker::durable_host::bridge::resubmit_queued;
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
    let outcome: Result<ResponseData, RpcCommandError> = match name {
        "prompt" => prompt_commands::prompt(state, &payload).await,
        "steer" | "follow_up" => prompt_commands::steer_or_follow_up(state, &payload, name).await,
        "abort" => state
            .session
            .abort()
            .await
            .map(|()| ResponseData::Absent)
            .map_err(RpcCommandError::from),
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
        "get_budget" => budget_commands::get_budget(state).await,
        "set_budget" => budget_commands::set_budget(state, &payload).await,
        "add_budget" => budget_commands::add_budget(state, &payload).await,
        "audit_budget" => budget_commands::audit_budget(state).await,
        // TS `abortRetry` always answers success (it aborts only an
        // in-flight retry; the durable retry backoff ends with the abort
        // of its run).
        "abort_retry" => Ok(ResponseData::Absent),
        other => session_commands::handle(state, other, &payload).await,
    };
    match outcome {
        Ok(data) => protocol::success(id.as_ref(), name, data),
        Err(error) => protocol::error(id.as_ref(), name, &error.to_string()),
    }
}

/// `new_session` (TS `runtimeHost.newSession`): a fresh session over the
/// ACTIVE session's project. A `parentSession` is accepted for protocol
/// compatibility but has no durable record to land in (durable storage
/// carries no session header with a parent link).
async fn new_session(state: &Arc<RpcState>) -> Result<ResponseData, RpcCommandError> {
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
async fn get_state(state: &Arc<RpcState>) -> Result<ResponseData, RpcCommandError> {
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
    let meta = read_session_meta(harness, &cx).await?;
    let goal = goal_state(harness, main.id(), &cx).await?;
    let loop_mode = loop_status(harness, main.id(), &cx).await?;
    let acceptance = acceptance_state(harness, main.id(), &cx).await?;
    let settings = deps.settings.manager();

    let mut object = serde_json::Map::new();
    if let Some(model) = agent_model(session, &agent) {
        object.insert("model".to_string(), serde_json::to_value(model)?);
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
    object.insert("goal".to_string(), serde_json::to_value(goal)?);
    object.insert("loop".to_string(), serde_json::to_value(loop_mode)?);
    object.insert("acceptance".to_string(), serde_json::to_value(acceptance)?);
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

/// `compact`: interrupt the running turn, run a manual durable compaction
/// and answer with the TS `CompactionResult`; a skip answers the TS
/// `CompactionSkippedError` message with the compaction frames around it
/// (a compaction that ran publishes its own frames through the event
/// pump). The interrupted turn gets its queued inputs back and resumes
/// when the compaction compacted or was a no-op. A loop whose turn the
/// interrupt cuts is held across the compaction and takes its work up
/// again whatever the compaction did (the worker's `compact` alike).
async fn compact(state: &Arc<RpcState>, payload: &Value) -> Result<ResponseData, RpcCommandError> {
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
    let (interrupted, held) =
        if matches!(is_busy(session.harness(), main.id(), &cx).await, Ok(false)) {
            (None, false)
        } else {
            // The interrupt is the compaction's, not the user's: a loop
            // with a turn in flight is held, not paused.
            let held = hold_loop_for_compaction(session.harness(), &main, &cx).await?;
            match interrupt_turn(session.harness(), &main, &cx).await {
                Ok(queued) => (Some(queued), held),
                Err(error) => {
                    // No compaction follows: the held loop is released here.
                    resume_loop(session, &main, &cx).await;
                    return Err(error.into());
                }
            }
        };
    let outcome = run_manual_compaction(
        session.harness(),
        session.deps(),
        &main,
        instructions.clone(),
        &cx,
    )
    .await;
    // The compaction settled, whatever it did: a held loop takes its work
    // up again, its cut turn sent again ahead of the inputs queued behind
    // it. The loop's own queued iteration is that turn, never resubmitted.
    resume_loop(session, &main, &cx).await;
    // The queued inputs drive the resume; without them the auto-continue
    // prompt does, unless the held loop's turn resumes it.
    let resume = interrupted.is_some() && resumes_interrupted_turn(&outcome);
    let mut queued = interrupted.unwrap_or_default();
    if held {
        queued.retain(|input| {
            !matches!(
                input.origin,
                eukhe_types::input_origin::InputOrigin::Loop { .. }
            )
        });
    }
    let restored = !queued.is_empty();
    resubmit_queued(&main, queued, &cx).await?;
    if resume && !restored && !held {
        submit_auto_continue(&main, &cx).await?;
    }
    match outcome {
        Ok(result) => Ok(ResponseData::Present(serde_json::to_value(result)?)),
        Err(skipped @ ManualCompactionError::Skipped(_)) => {
            state.session.outputs().write_events([
                SessionEvent::CompactionStart {
                    reason: CompactionReason::Manual,
                    custom_instructions: instructions.clone(),
                },
                SessionEvent::CompactionEnd {
                    reason: CompactionReason::Manual,
                    result: None,
                    aborted: false,
                    will_retry: false,
                    error_message: None,
                    error_severity: None,
                    custom_instructions: instructions,
                },
            ]);
            Err(skipped.into())
        }
        Err(error) => Err(error.into()),
    }
}

/// After a manual compaction settled (or could not start): a loop held
/// for it takes its work up again. A failure is reported, not the
/// command's: the compaction's answer stands.
async fn resume_loop(session: &EukheSession, main: &Conversation, cx: &Context) {
    if let Err(error) = resume_loop_after_compaction(session.deps(), main, cx).await {
        eprintln!("eukhe-daemon: resuming the loop after the compaction failed: {error}");
    }
}

/// `refine` (TS `session.refine`): run the refinement on the main
/// conversation and answer with the `RefinementResult`.
async fn refine(state: &Arc<RpcState>, payload: &Value) -> Result<ResponseData, RpcCommandError> {
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
        .map_err(|source| RpcCommandError::Refine { source })?;
    Ok(ResponseData::Present(serde_json::to_value(result)?))
}

/// `set_auto_compaction` (TS `session.setAutoCompactionEnabled`): the
/// session's own `compaction.enabled`, which its compaction policy reads.
async fn set_auto_compaction(
    state: &Arc<RpcState>,
    payload: &Value,
) -> Result<ResponseData, RpcCommandError> {
    let enabled = payload
        .get("enabled")
        .and_then(Value::as_bool)
        .ok_or_else(|| RpcCommandError::missing("set_auto_compaction", "enabled"))?;
    set_session_cvar(state, &table::COMPACTION_ENABLED, &enabled.to_string()).await
}

/// `set_auto_retry` (TS `session.setAutoRetryEnabled`): the session's own
/// `retry.enabled`, which its retry policy reads.
async fn set_auto_retry(
    state: &Arc<RpcState>,
    payload: &Value,
) -> Result<ResponseData, RpcCommandError> {
    let enabled = payload
        .get("enabled")
        .and_then(Value::as_bool)
        .ok_or_else(|| RpcCommandError::missing("set_auto_retry", "enabled"))?;
    set_session_cvar(state, &table::RETRY_ENABLED, &enabled.to_string()).await
}

/// Set `decl` to `value` in the session's own cvar layer (committed with
/// its main conversation; never a settings.json write).
#[tracing::instrument(skip(state))]
pub(crate) async fn set_session_cvar(
    state: &Arc<RpcState>,
    decl: &Decl,
    value: &str,
) -> Result<ResponseData, RpcCommandError> {
    let line = Command::Set {
        id: decl.id.to_string(),
        value: value.to_string(),
    }
    .to_string();
    let session = state.session.session().await;
    run_cvar_line(&session, &line, CvarLineScope::Session, &rpc_context()).await?;
    Ok(ResponseData::Absent)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::durable_test_support::{loop_sends, Fixture, SESSION_ID};
    use crate::rpc::session::{ConnectionOutputs, RpcEngineError, RpcEngineHandle};
    use eukhe_ai::providers::faux::FauxResponseStep;
    use eukhe_durable::types::SubmissionId;
    use eukhe_types::loop_mode::LoopStatus;
    use eukhe_types::pi_ai::UserContent;
    use futures::FutureExt;

    /// The RPC state over one fixture session, and the frames it writes.
    async fn rpc_state(
        fixture: &Fixture,
    ) -> (Arc<RpcState>, tokio::sync::mpsc::UnboundedReceiver<Value>) {
        let opened = std::sync::Mutex::new(Some(RpcEngineHandle {
            session: Arc::new(fixture.open(SESSION_ID).await),
            session_lease: None,
        }));
        let factory: crate::rpc::session::RpcEngineFactory = Arc::new(move |_request| {
            let handle = opened
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .take();
            Box::pin(async move {
                handle.ok_or_else(|| RpcEngineError::new("the fixture opens one session"))
            })
        });
        let (writer, frames) = LineWriter::channel();
        let session = RpcSession::start(factory, ConnectionOutputs::new(writer.clone()))
            .await
            .expect("the rpc session starts");
        let state = Arc::new(RpcState {
            session: Arc::new(session),
            writer,
            model_ops: tokio::sync::Mutex::new(()),
            session_ops: tokio::sync::Mutex::new(()),
        });
        (state, frames)
    }

    /// The `loop` field of `get_state`.
    async fn state_loop(state: &Arc<RpcState>) -> Value {
        match get_state(state).await.expect("get_state") {
            ResponseData::Present(data) => data["loop"].clone(),
            ResponseData::Absent => panic!("get_state answers data"),
        }
    }

    /// The next `loop_update` frame the connection writes.
    async fn next_loop_update(frames: &mut tokio::sync::mpsc::UnboundedReceiver<Value>) -> Value {
        loop {
            let frame = frames.recv().await.expect("the writer stays open");
            if frame["type"] == "loop_update" {
                return frame;
            }
        }
    }

    /// `get_state` carries the loop (off on a fresh session), and the
    /// connection publishes a `loop_update` only when the loop changed:
    /// the watch's first value (the off loop the connection started
    /// with) publishes nothing, so the first frame is the armed loop,
    /// and the stop is the second.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn get_state_and_loop_update_carry_the_loop() {
        let fixture = Fixture::new();
        let (state, mut frames) = rpc_state(&fixture).await;
        assert_eq!(state_loop(&state).await, json!(LoopStatus::default()));

        prompt_commands::prompt(&state, &json!({ "message": "/loop 3" }))
            .await
            .expect("/loop 3");
        let armed = next_loop_update(&mut frames).await;
        assert_eq!(
            armed,
            json!({ "type": "loop_update", "loop": state_loop(&state).await })
        );
        assert_eq!(armed["loop"]["phase"], json!({ "state": "armed" }));

        prompt_commands::prompt(&state, &json!({ "message": "/loop --stop" }))
            .await
            .expect("/loop --stop");
        let stopped = next_loop_update(&mut frames).await;
        assert_eq!(
            stopped,
            json!({ "type": "loop_update", "loop": state_loop(&state).await })
        );
        assert_eq!(
            stopped["loop"]["phase"],
            json!({ "state": "ended", "end": "stopped" })
        );
        state.session.dispose().await;
    }

    const DEADLINE: std::time::Duration = std::time::Duration::from_secs(20);

    /// A model request that never answers: `reached` turns true once it
    /// is asked, and only a cancel ends it.
    fn stuck() -> (FauxResponseStep, tokio::sync::watch::Receiver<bool>) {
        let (reached, reached_rx) = tokio::sync::watch::channel(false);
        let step = FauxResponseStep::Factory(Arc::new(move |_, options, _, _| {
            reached.send_replace(true);
            let signal = options.and_then(|options| options.stream.request.signal.clone());
            async move {
                match signal {
                    Some(signal) => Err(signal.cancelled().await),
                    None => futures::future::pending().await,
                }
            }
            .boxed()
        }));
        (step, reached_rx)
    }

    /// A `compact` that cuts a loop's turn holds the loop across the
    /// compaction: the loop is not paused, and the cut turn is sent again
    /// as the same iteration. The user's `abort` of that turn pauses it.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn compact_sends_a_cut_loop_turn_again_and_abort_pauses_the_loop() {
        let fixture = Fixture::new();
        let (cut, mut cut_reached) = stuck();
        let (resent, mut resent_reached) = stuck();
        fixture.faux.append_responses(vec![cut, resent]);
        let (state, mut frames) = rpc_state(&fixture).await;
        let main = state.session.session().await.main();

        prompt_commands::prompt(&state, &json!({ "message": "/loop 3 go" }))
            .await
            .expect("/loop 3 go");
        cut_reached
            .wait_for(|reached| *reached)
            .await
            .expect("the loop's turn runs");
        // Nothing before the cut turn to summarize: the compaction skips,
        // and the held loop takes its turn up again all the same.
        let compacted = compact(&state, &json!({})).await;
        assert!(
            matches!(
                compacted,
                Err(RpcCommandError::Compaction(ManualCompactionError::Skipped(
                    _
                )))
            ),
            "{compacted:?}"
        );
        // A paused loop never sends it: bound the wait.
        tokio::time::timeout(DEADLINE, resent_reached.wait_for(|reached| *reached))
            .await
            .expect("the held loop never sent the cut turn again")
            .expect("the cut turn is sent again");
        let held = state_loop(&state).await;
        assert_eq!(
            (&held["phase"], &held["iteration"]),
            (&json!({ "state": "turn" }), &json!(1))
        );
        let resent = vec![("go".to_owned(), Some(1)), ("go".to_owned(), Some(1))];
        assert_eq!(loop_sends(&main).await, resent);
        while let Ok(frame) = frames.try_recv() {
            assert_ne!(
                frame["loop"]["phase"],
                json!({ "state": "paused" }),
                "the compaction paused the loop: {frame}"
            );
        }

        state.session.abort().await.expect("abort");
        let paused = json!({ "state": "paused" });
        tokio::time::timeout(DEADLINE, async {
            while next_loop_update(&mut frames).await["loop"]["phase"] != paused {}
        })
        .await
        .expect("the abort never paused the loop");
        assert_eq!(state_loop(&state).await["phase"], paused);
        assert_eq!(loop_sends(&main).await, resent);
        state.session.dispose().await;
    }

    #[test]
    fn session_actions_preview_queued_inputs_only() {
        let items = vec![
            InboxItem::Steer {
                id: SubmissionId::from_number(1),
                content: UserContent::Text("steer this".into()),
                entry: None,
                origin: eukhe_types::input_origin::InputOrigin::User,
            },
            InboxItem::Write {
                id: SubmissionId::from_number(2),
                entry: eukhe_chord::json::JsonValue::Null,
            },
            InboxItem::FollowUp {
                id: SubmissionId::from_number(3),
                content: UserContent::Text("fu this".into()),
                entry: None,
                origin: eukhe_types::input_origin::InputOrigin::User,
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
}
