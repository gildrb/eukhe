//! The `rlm.*` kernel host requests over the durable children registry:
//! `rlm.run` (`rlm.spawn`),
//! `rlm.create_session`, `rlm.find_models`, `rlm.list_subagents`,
//! `rlm.delete_subagent`, `rlm.collect`, `rlm.answer`, and
//! `rlm.progress.note`
//! (`rlm.rename` lives in [`super::rename`]).

use std::future::Future;
use std::sync::Arc;
use std::time::Duration;

use anyhow::{anyhow, bail};
use eukhe_ai::auth::AuthOperationOptions;
use eukhe_bend::rules::family;
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::to_json;
use eukhe_durable::harness::types::ToolExecutionApiExt;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult, Tx};
use eukhe_durable::types::{
    ConversationId, DocumentObserverExt, TaskId, TaskOptions, TaskOutcome, TaskOwnership,
    TaskState, TaskStatus, ROOT_CONVERSATION_ID,
};
use futures::FutureExt;
use serde_json::{json, Map, Value};
use tokio::sync::Notify;

use super::depth::read_max_depth_override;
use super::host::{
    RlmChildDeleteRequest, RlmChildListing, RlmCreateSessionRequest, RlmSubagentHost,
};
use super::notice::{rlm_child_label, DELETED_BY_PARENT};
use super::progress::{tx_note, utf16_length, NoteOutcome, RLM_PROGRESS_NOTE_MAX_LENGTH};
use super::registry::{
    child_identity, read_children, resolve, tx_children, tx_put_row, tx_update_row, ChildDeletion,
    ChildRow, ChildStatus, HandbackOutcome, Resolved, CHILDREN_DOC,
};
use super::task::{ChildTaskInput, ReportMode};
use super::wire::{
    RlmChildResult, RlmDeleteSubagentResult, RlmSpawnHandle, RlmSubagentActivity, RlmSubagentEntry,
};
use super::Children;
use crate::agent_messaging::assert_direct_agent_message_target;
use crate::child_workspace::WorkspaceMode;
use crate::durable::deps::{HostCall, HostRequestRegistry};
use crate::kernel::rlm_runtime::{
    create_default_rlm_subagent_session_name, find_rlm_model_matches, kwargs_from_payload,
    normalize_requested_rlm_subagent_model, normalize_requested_rlm_subagent_session_name,
    normalize_requested_rlm_subagent_thinking_level, RlmModelInfo, DEFAULT_RLM_MODEL_SEARCH_LIMIT,
    MAX_RLM_MODEL_SEARCH_LIMIT,
};

const NO_SPAWN_RUNTIME: &str =
    "rlm.spawn requires a daemon-backed session: this session has no RLM child runtime";

/// Register every `rlm.*` handler of `children` onto `registry`.
pub(super) fn register(registry: &HostRequestRegistry, children: &Arc<Children>) {
    macro_rules! handler {
        ($request_type:literal, $function:path) => {{
            let children = Arc::clone(children);
            registry.register(
                $request_type,
                Arc::new(move |call: HostCall| $function(Arc::clone(&children), call).boxed()),
            );
        }};
    }
    handler!("rlm.find_models", find_models);
    handler!("rlm.progress.note", progress_note);
    handler!("rlm.run", run);
    handler!("rlm.run_batch", run_batch);
    handler!("rlm.create_session", create_session);
    handler!("rlm.list_subagents", list_subagents);
    handler!("rlm.delete_subagent", delete_subagent);
    handler!("rlm.collect", collect);
    handler!("rlm.answer", answer);
    handler!("rlm.rename", super::rename::rename);
}

pub(super) fn cx() -> Context {
    BACKGROUND_CONTEXT.clone()
}

pub(super) fn session_error(error: SessionError) -> anyhow::Error {
    anyhow::Error::new(error)
}

/// The conversation a request acts on: the calling tool's, else the root.
pub(super) fn conversation_of(call: &HostCall) -> ConversationId {
    call.call
        .as_ref()
        .map_or(ROOT_CONVERSATION_ID, |api| api.conversation_id())
}

#[expect(
    clippy::cast_precision_loss,
    reason = "epoch milliseconds stay below 2^53"
)]
pub(super) fn now_ms() -> f64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0.0, |elapsed| elapsed.as_millis() as f64)
}

#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "a non-negative whole number of milliseconds"
)]
fn whole_ms(value: f64) -> u64 {
    value.max(0.0) as u64
}

/// Commit through the conversation `conversation_id` of the open Harness.
pub(super) async fn commit<T, F, Fut>(
    harness: &Harness,
    conversation_id: ConversationId,
    change: F,
) -> anyhow::Result<T>
where
    T: Send + 'static,
    F: FnOnce(Tx) -> Fut + Send + 'static,
    Fut: Future<Output = SessionResult<T>> + Send + 'static,
{
    let conversation = harness
        .conversation(conversation_id, &cx())
        .await
        .map_err(session_error)?
        .ok_or_else(|| anyhow!("Conversation {conversation_id} does not exist"))?;
    conversation
        .commit(change, &cx())
        .await
        .map_err(session_error)
}

// ---------------------------------------------------------------------------
// rlm.find_models / rlm.progress.note
// ---------------------------------------------------------------------------

async fn find_models(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let data = &call.data;
    let Some(query) = data.get("query").and_then(Value::as_str) else {
        bail!("rlm.find_models query must be a string");
    };
    let limit = match data.get("limit") {
        None | Some(Value::Null) => Some(DEFAULT_RLM_MODEL_SEARCH_LIMIT as u64),
        Some(value) => value
            .as_u64()
            .filter(|limit| (1..=MAX_RLM_MODEL_SEARCH_LIMIT as u64).contains(limit)),
    };
    let Some(limit) = limit else {
        bail!("rlm.find_models limit must be an integer from 1 to {MAX_RLM_MODEL_SEARCH_LIMIT}");
    };
    let available = children
        .models
        .get_available(None, AuthOperationOptions::default())
        .await
        .map_err(|error| anyhow!("{error}"))?;
    let models: Vec<RlmModelInfo> = available
        .into_iter()
        .map(|model| RlmModelInfo {
            name: if model.name.is_empty() {
                model.id.clone()
            } else {
                model.name.clone()
            },
            provider: model.provider,
            id: model.id,
        })
        .collect();
    let limit = usize::try_from(limit)?;
    Ok(json!({ "models": find_rlm_model_matches(query, &models, limit) }))
}

async fn progress_note(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let Some(raw) = call.data.get("message").and_then(Value::as_str) else {
        bail!("rlm.progress.note message must be a non-empty string");
    };
    let message = raw.trim().to_owned();
    if message.is_empty() {
        bail!("rlm.progress.note message must be a non-empty string");
    }
    if utf16_length(&message) > RLM_PROGRESS_NOTE_MAX_LENGTH {
        bail!(
            "rlm.progress.note message must be at most {RLM_PROGRESS_NOTE_MAX_LENGTH} characters"
        );
    }
    let harness = children.harness.require().map_err(session_error)?;
    let conversation_id = conversation_of(&call);
    let now = now_ms();
    let noted = message.clone();
    let outcome = commit(&harness, conversation_id, move |tx| async move {
        tx_note(&tx, conversation_id, &noted, now).await
    })
    .await?;
    Ok(match outcome {
        NoteOutcome::Accepted => {
            if let Some(sink) = &children.progress_note {
                sink(&message, now);
            }
            json!({ "accepted": true })
        }
        NoteOutcome::Throttled { retry_after_ms } => json!({
            "accepted": false,
            "retry_after_ms": retry_after_ms
        }),
    })
}

// ---------------------------------------------------------------------------
// rlm.run (rlm.spawn)
// ---------------------------------------------------------------------------

/// Validated `rlm.spawn` kwargs.
struct SpawnKwargs {
    /// The reason the spawn names (`why`); the compiled core decides
    /// whether it is allowed (`eukhe_bend::rules::family`).
    why: Option<String>,
    name: Option<String>,
    model: Option<String>,
    thinking: Option<String>,
    /// `None` when the caller did not choose (the shared workspace).
    workspace: Option<WorkspaceMode>,
    /// The roster label; `None`: derived from the prompt.
    label: Option<String>,
    /// The workflow phase the child serves.
    phase: Option<String>,
    report: ReportMode,
}

/// Unsupported keys are rejected with the sorted key list; name, model, and
/// thinking normalize through the pure helpers.
fn spawn_kwargs(data: &Value) -> anyhow::Result<SpawnKwargs> {
    const OPERATION: &str = "rlm.spawn";
    let kwargs = kwargs_from_payload(data);
    reject_unsupported_kwargs(
        &kwargs,
        OPERATION,
        &[
            "why",
            "name",
            "model",
            "thinking",
            "workspace",
            "label",
            "phase",
            "report",
        ],
    )?;
    let why = optional_string_kwarg(&kwargs, "why", OPERATION)?.map(str::to_owned);
    let name = optional_string_kwarg(&kwargs, "name", OPERATION)?;
    let name = normalize_requested_rlm_subagent_session_name(name, OPERATION)?;
    if let Some(name) = &name {
        assert_direct_agent_message_target(name)?;
    }
    let model = optional_string_kwarg(&kwargs, "model", OPERATION)?;
    let model = normalize_requested_rlm_subagent_model(model, OPERATION)?;
    let thinking = optional_string_kwarg(&kwargs, "thinking", OPERATION)?;
    let thinking =
        normalize_requested_rlm_subagent_thinking_level(thinking, OPERATION)?.map(String::from);
    let workspace = match optional_string_kwarg(&kwargs, "workspace", OPERATION)? {
        None => None,
        Some("shared") => Some(WorkspaceMode::Shared),
        Some("isolated") => Some(WorkspaceMode::Isolated),
        Some(_) => bail!("{OPERATION} workspace must be \"shared\" or \"isolated\""),
    };
    let text = |key: &str| -> anyhow::Result<Option<String>> {
        Ok(optional_string_kwarg(&kwargs, key, OPERATION)?
            .map(str::trim)
            .filter(|value| !value.is_empty())
            .map(str::to_owned))
    };
    let label = text("label")?;
    let phase = text("phase")?;
    let report = match optional_string_kwarg(&kwargs, "report", OPERATION)? {
        None | Some("inbox") => ReportMode::Inbox,
        Some("silent") => ReportMode::Silent,
        Some(_) => bail!("{OPERATION} report must be \"inbox\" or \"silent\""),
    };
    Ok(SpawnKwargs {
        why,
        name,
        model,
        thinking,
        workspace,
        label,
        phase,
        report,
    })
}

/// The spawn-name-unavailability error (TS
/// `formatAgentSessionNameUnavailable`).
pub(super) fn spawn_name_unavailable(name: &str, depth: u32) -> String {
    format!(
        "Agent name \"{name}\" is unavailable: an agent of that name already exists at depth {depth} under this parent"
    )
}

/// One validated spawn of an `rlm.run` / `rlm.run_batch` request.
struct SpawnSpec {
    prompt: String,
    kwargs: SpawnKwargs,
}

/// Validate one `{prompt, kwargs}` spawn payload.
fn spawn_spec(data: &Value) -> anyhow::Result<SpawnSpec> {
    let Some(prompt) = data.get("prompt").and_then(Value::as_str) else {
        bail!("rlm.spawn prompt must be a string");
    };
    Ok(SpawnSpec {
        prompt: prompt.to_owned(),
        kwargs: spawn_kwargs(data)?,
    })
}

/// `rlm.spawn`: admit one `eukhe.rlm.child` task (see [`admit_spawns`]).
async fn run(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let spec = spawn_spec(&call.data)?;
    let handles = admit_spawns(&children, &call, vec![spec]).await?;
    let handle = handles
        .into_iter()
        .next()
        .ok_or_else(|| anyhow!("rlm.spawn admitted no child"))?;
    Ok(serde_json::to_value(&handle)?)
}

/// `rlm.spawn_batch`: admit every `{prompt, kwargs}` of `tasks` together
/// or none of them (see [`admit_spawns`]).
async fn run_batch(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let Some(tasks) = call.data.get("tasks").and_then(Value::as_array) else {
        bail!("rlm.spawn_batch tasks must be a non-empty list");
    };
    if tasks.is_empty() {
        bail!("rlm.spawn_batch tasks must be a non-empty list");
    }
    let specs = tasks
        .iter()
        .map(spawn_spec)
        .collect::<anyhow::Result<Vec<_>>>()?;
    let handles = admit_spawns(&children, &call, specs).await?;
    Ok(json!({ "handles": handles }))
}

/// One admitted spawn: its name, label, phase, and task input.
type Admitted = (
    Option<String>,
    Option<String>,
    Option<String>,
    ChildTaskInput,
);

/// Admit `specs` as `eukhe.rlm.child` tasks in the calling tool's commit,
/// together with their registry rows, then wait for each task's `spawn`
/// phase to create its child. The compiled core decides admission
/// (`eukhe_bend::rules::family`, entry 431): first on the reasons and the
/// depth (no family count yet, no cap), then inside the commit on the
/// family's running or starting subagents (the host's view unioned with
/// this session's not-yet-visible children) against
/// `subagentMaxConcurrency`. The name checks, that decision, and the rows
/// land atomically, so parallel same-name spawns cannot both admit and a
/// batch is all-or-nothing.
async fn admit_spawns(
    children: &Arc<Children>,
    call: &HostCall,
    specs: Vec<SpawnSpec>,
) -> anyhow::Result<Vec<RlmSpawnHandle>> {
    if !children.has_runtime {
        bail!("{NO_SPAWN_RUNTIME}");
    }
    // The runtime bound (`set_rlm_max_depth`) of the calling conversation
    // overrides the configured one; without an open Harness or a calling
    // tool there is none to read, and the errors below keep their order.
    let depth_override = match (children.harness.get(), call.call.as_ref()) {
        (Some(harness), Some(api)) => {
            read_max_depth_override(&harness, api.conversation_id(), &cx())
                .await
                .map_err(session_error)?
        }
        _ => None,
    };
    let depth = children.services.rlm_depth;
    let max_depth = depth_override.unwrap_or(children.services.rlm_max_depth);
    let whys: Vec<Option<String>> = specs.iter().map(|spec| spec.kwargs.why.clone()).collect();
    let decide = move |running: u32, cap: u32| {
        let whys: Vec<Option<&str>> = whys.iter().map(Option::as_deref).collect();
        family::admit(&family::Batch {
            depth,
            max_depth,
            running,
            cap,
            whys: &whys,
        })
    };
    let child_depth = match decide(0, 0) {
        family::Admission::Admit { child_depth } => child_depth,
        family::Admission::Refuse(text) => bail!("{text}"),
    };
    let Some(api) = call.call.clone() else {
        bail!("rlm.spawn must run inside a tool call");
    };
    let capacity = children.services.host.spawn_capacity().await?;
    let harness = children.harness.require().map_err(session_error)?;
    let conversation_id = api.conversation_id();
    // The spawn anchors to the parent's in-flight model request (TS
    // `spawnedByRequestId` from the semantic-edge recorder); the tool call
    // id stands in when no recorder carries one.
    let spawned_by_request_id = children
        .services
        .semantic_edges
        .as_ref()
        .and_then(|recorder| recorder.last_turn_request_id())
        .or_else(|| Some(api.call_id().to_owned()));
    let admitted: Vec<Admitted> = specs
        .into_iter()
        .map(|spec| {
            (
                spec.kwargs.name,
                spec.kwargs.label,
                spec.kwargs.phase,
                ChildTaskInput {
                    prompt: spec.prompt,
                    model: spec.kwargs.model,
                    thinking: spec.kwargs.thinking,
                    spawned_by_request_id: spawned_by_request_id.clone(),
                    max_depth: Some(max_depth),
                    workspace: spec.kwargs.workspace,
                    owed: None,
                    report: spec.kwargs.report,
                },
            )
        })
        .collect();
    let task = children.task.as_definition_ref();
    let parent_session_id = children.services.parent_session_id.clone();
    let started_at = now_ms();
    let task_ids = api
        .commit(
            move |tx| async move {
                let state = tx_children(&tx, conversation_id).await?;
                let mut active: std::collections::HashSet<&str> = capacity
                    .active_session_ids
                    .iter()
                    .map(String::as_str)
                    .collect();
                active.extend(
                    state
                        .children
                        .values()
                        .filter(|row| !row.is_deleted() && !row.status.is_terminal())
                        .map(|row| row.session_id.as_str()),
                );
                let running = u32::try_from(active.len()).unwrap_or(u32::MAX);
                if let family::Admission::Refuse(text) = decide(running, capacity.max_concurrency) {
                    return Err(SessionError::error(text));
                }
                let mut batch_names: Vec<&str> = Vec::new();
                for name in admitted.iter().filter_map(|(name, ..)| name.as_deref()) {
                    let taken = batch_names.contains(&name)
                        || state
                            .children
                            .values()
                            .any(|row| !row.is_deleted() && row.session_name == name);
                    if taken {
                        return Err(SessionError::error(spawn_name_unavailable(
                            name,
                            child_depth,
                        )));
                    }
                    batch_names.push(name);
                }
                let mut task_ids = Vec::with_capacity(admitted.len());
                for (name, label, phase, input) in admitted {
                    let task_id = tx
                        .create_task(
                            task.clone(),
                            to_json(&input)?,
                            TaskOptions {
                                ownership: TaskOwnership::Conversation,
                                conversation_id: Some(conversation_id),
                                background: Some(true),
                                abandon_on_restart: None,
                            },
                        )
                        .await?;
                    let identity = child_identity(&parent_session_id, task_id);
                    let session_name = name.unwrap_or_else(|| {
                        create_default_rlm_subagent_session_name(
                            &input.prompt,
                            &identity.rlm_child_id,
                        )
                    });
                    let row = ChildRow {
                        task_id: task_id.get(),
                        rlm_child_id: identity.rlm_child_id,
                        session_id: identity.session_id,
                        session_name,
                        label: label.unwrap_or_else(|| rlm_child_label(&input.prompt)),
                        started_at,
                        status: ChildStatus::Spawning,
                        active_session_id: None,
                        session_dir: None,
                        model: None,
                        answer_preview: None,
                        error: None,
                        failure: None,
                        replied_since_task: false,
                        deletion: None,
                        settled: false,
                        usage: None,
                        progress: None,
                        reporter: None,
                        handback: None,
                        phase,
                        answer: None,
                    };
                    tx_put_row(&tx, conversation_id, &row).await?;
                    task_ids.push(task_id);
                }
                Ok(task_ids)
            },
            &cx(),
        )
        .await
        .map_err(|error| anyhow!("{error}"))?;
    // Every task is admitted; a child whose create fails reports its own
    // error (the batch's other children stay admitted and listed).
    let mut handles = Vec::with_capacity(task_ids.len());
    for task_id in task_ids {
        let row = wait_for_admission(&harness, conversation_id, task_id).await?;
        handles.push(RlmSpawnHandle {
            rlm_child_id: row.rlm_child_id,
            name: row.session_name,
            session_dir: row.session_dir.unwrap_or_default(),
            model: row.model.unwrap_or_default(),
        });
    }
    Ok(handles)
}

/// The message of a terminal child task that left no admitted child.
fn admission_failure(task_id: TaskId, state: &TaskState) -> Option<anyhow::Error> {
    let TaskState::Terminal { outcome } = state else {
        return None;
    };
    Some(match outcome {
        TaskOutcome::Failed { error, .. } | TaskOutcome::Faulted { error } => {
            anyhow!("{}", error.message)
        }
        TaskOutcome::Orphaned { reason } => anyhow!("{reason}"),
        TaskOutcome::Completed { .. } | TaskOutcome::Aborted { .. } => {
            anyhow!("RLM child task {task_id} ended before its child was created")
        }
    })
}

/// Wait until the `spawn` phase of `task_id` admitted its child (the row
/// leaves `spawning`) or the task ended without one.
async fn wait_for_admission(
    harness: &Harness,
    conversation_id: ConversationId,
    task_id: TaskId,
) -> anyhow::Result<ChildRow> {
    let changed = Arc::new(Notify::new());
    let watch = harness
        .watch_doc(&CHILDREN_DOC, conversation_id, &cx())
        .await
        .map_err(session_error)?;
    if let Some(watch) = &watch {
        let changed = Arc::clone(&changed);
        watch
            .start(Arc::new(move |_value, _ops, _cx| {
                changed.notify_one();
                futures::future::ready(Ok(())).boxed()
            }))
            .map_err(session_error)?;
    }
    let key = task_id.to_string();
    let outcome = loop {
        let state = read_children(harness, conversation_id, &cx())
            .await
            .map_err(session_error)?;
        let row = state.children.get(&key);
        if let Some(row) = row.filter(|row| row.status != ChildStatus::Spawning) {
            break Ok(row.clone());
        }
        let record = harness
            .get_task(task_id, &cx())
            .await
            .map_err(session_error)?;
        if let Some(failure) = record.and_then(|record| admission_failure(task_id, &record.state)) {
            break Err(failure);
        }
        tokio::select! {
            () = changed.notified() => {}
            settled = harness.wait_for_task(task_id, &cx()) => {
                settled.map_err(session_error)?;
            }
        }
    };
    if let Some(watch) = watch {
        watch.stop().await;
    }
    outcome
}

// ---------------------------------------------------------------------------
// rlm.create_session
// ---------------------------------------------------------------------------

async fn create_session(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    const OPERATION: &str = "rlm.create_session";
    let data = &call.data;
    let Some(prompt) = data.get("prompt").and_then(Value::as_str) else {
        bail!("rlm.create_session prompt must be a string");
    };
    if prompt.trim().is_empty() {
        bail!("rlm.create_session prompt must not be empty");
    }
    let kwargs = kwargs_from_payload(data);
    reject_unsupported_kwargs(&kwargs, OPERATION, &["name", "model", "thinking", "cwd"])?;
    let name = optional_string_kwarg(&kwargs, "name", OPERATION)?;
    let name = normalize_requested_rlm_subagent_session_name(name, OPERATION)?;
    if let Some(name) = &name {
        assert_direct_agent_message_target(name)?;
    }
    let model = optional_string_kwarg(&kwargs, "model", OPERATION)?;
    let model = normalize_requested_rlm_subagent_model(model, OPERATION)?;
    let thinking = optional_string_kwarg(&kwargs, "thinking", OPERATION)?;
    let thinking =
        normalize_requested_rlm_subagent_thinking_level(thinking, OPERATION)?.map(String::from);
    let cwd = match kwargs.get("cwd") {
        None => None,
        Some(Value::String(cwd)) if !cwd.trim().is_empty() => Some(cwd.trim().to_owned()),
        Some(_) => bail!("rlm.create_session cwd must be a non-empty string"),
    };
    if children.has_runtime && children.services.rlm_depth != 0 {
        bail!("rlm.create_session is available only from a depth-0 session");
    }
    // One resident session per request: the key names this request only.
    let origin = call
        .call
        .as_ref()
        .map_or_else(|| "host".to_owned(), |api| api.task_id().to_string());
    let request = RlmCreateSessionRequest {
        idempotency_key: format!("rlm:create_session:{origin}:{}", uuid::Uuid::now_v7()),
        prompt: prompt.to_owned(),
        name,
        model,
        thinking,
        cwd,
    };
    let handle = children.services.host.create_session(request).await?;
    Ok(serde_json::to_value(&handle)?)
}

// ---------------------------------------------------------------------------
// rlm.list_subagents / rlm.delete_subagent / rlm.collect
// ---------------------------------------------------------------------------

/// The roster row of `row`, overlaid with the host's live facts.
pub(super) fn entry(
    row: &ChildRow,
    listing: Option<&RlmChildListing>,
    now: f64,
) -> RlmSubagentEntry {
    let running = !row.status.is_terminal();
    let activity = running.then(|| RlmSubagentActivity {
        kind: listing
            .and_then(|listing| listing.activity)
            .map_or("executing", |kind| kind.as_str()),
        tool_name: listing.and_then(|listing| listing.tool_name.clone()),
    });
    RlmSubagentEntry {
        rlm_child_id: row.rlm_child_id.clone(),
        active_session_id: row.active_session_id.clone(),
        session_id: Some(row.session_id.clone()),
        session_name: row.session_name.clone(),
        session_dir: row.session_dir.clone().unwrap_or_default(),
        status: row.status.roster_status(),
        activity,
        tool_use_count: listing.and_then(|listing| listing.tool_use_count),
        duration_ms: Some(whole_ms(now - row.started_at)),
        answer_preview: row.answer_preview.clone(),
        replied_since_task: None,
        progress_note: listing.and_then(|listing| listing.progress_note.clone()),
        label: (!row.label.is_empty()).then(|| row.label.clone()),
        last_activity_at: Some(
            listing
                .and_then(|listing| listing.last_activity_at)
                .unwrap_or_else(|| whole_ms(row.started_at)),
        ),
        activity_stale_ms: None,
        handback: row.handback.as_ref().map(HandbackOutcome::text),
    }
}

async fn list_subagents(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let harness = children.harness.require().map_err(session_error)?;
    let state = read_children(&harness, conversation_of(&call), &cx())
        .await
        .map_err(session_error)?;
    let listings = children.services.host.list().await?;
    let now = now_ms();
    let subagents: Vec<RlmSubagentEntry> = state
        .children
        .values()
        .filter(|row| !row.is_deleted())
        .map(|row| {
            let listing = listings
                .iter()
                .find(|listing| listing.session_id == row.session_id);
            let mut entry = entry(row, listing, now);
            // A spawned child the host has no live facts about was spawned
            // by an earlier process of this session (a restarted parent):
            // its recorded routing id named a worker that is gone, so the
            // row carries the durable session id, the selector that
            // reaches the child resident or not (TS relists a passive
            // child by its session id).
            if listing.is_none() && entry.active_session_id.is_some() {
                entry.active_session_id = Some(row.session_id.clone());
            }
            entry
        })
        .collect();
    Ok(json!({ "subagents": subagents }))
}

/// The one live (not deleted) row `target` selects, or the TS selector
/// errors.
fn resolve_live<'a>(
    rows: impl Iterator<Item = &'a ChildRow>,
    target: &str,
    kind: &str,
) -> anyhow::Result<&'a ChildRow> {
    match resolve(rows.filter(|row| !row.is_deleted()), target) {
        Resolved::One(row) => Ok(row),
        Resolved::None => {
            bail!("No direct RLM {kind} matches \"{target}\" in the current parent session")
        }
        Resolved::Ambiguous => {
            bail!("RLM {kind} selector \"{target}\" is ambiguous in the current parent session")
        }
    }
}

/// `rlm.delete_subagent`: abort a live child's task (its abort delivers the
/// cancelled notice a running child is owed), tear the session down at the
/// host, then leave a tombstone `rlm.collect` answers with a settled
/// cancelled envelope. A failed teardown keeps the child selectable so the
/// caller can retry.
async fn delete_subagent(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let Some(target) = call
        .data
        .get("target")
        .and_then(Value::as_str)
        .map(str::trim)
        .filter(|target| !target.is_empty())
    else {
        bail!("rlm.delete_subagent target must be a non-empty string");
    };
    let harness = children.harness.require().map_err(session_error)?;
    let result = delete_child_row(
        &harness,
        children.services.host.as_ref(),
        conversation_of(&call),
        target,
        &cx(),
    )
    .await?;
    Ok(serde_json::to_value(&result)?)
}

/// Delete the live child `target` selects in `conversation_id` (the body of
/// `rlm.delete_subagent`, shared with the host's `delete_rlm_subagent`
/// command).
pub(super) async fn delete_child_row(
    harness: &Harness,
    host: &dyn RlmSubagentHost,
    conversation_id: ConversationId,
    target: &str,
    cx: &Context,
) -> anyhow::Result<RlmDeleteSubagentResult> {
    let state = read_children(harness, conversation_id, cx)
        .await
        .map_err(session_error)?;
    let row = resolve_live(state.children.values(), target, "subagent")?.clone();
    let task_id = row.task_id();
    if !row.settled {
        commit(harness, conversation_id, move |tx| async move {
            tx_update_row(&tx, conversation_id, task_id, |row| {
                row.deletion = Some(ChildDeletion::Requested);
            })
            .await
            .map(drop)
        })
        .await?;
        harness
            .abort_task(task_id, cx)
            .await
            .map_err(session_error)?;
        harness
            .wait_for_task(task_id, cx)
            .await
            .map_err(session_error)?;
    }
    host.delete(RlmChildDeleteRequest {
        idempotency_key: format!("rlm:{task_id}:delete"),
        session_id: row.session_id.clone(),
        rlm_child_id: row.rlm_child_id.clone(),
    })
    .await
    .map_err(|error| error.context(format!("kill RLM child \"{target}\"")))?;
    let deleted = commit(harness, conversation_id, move |tx| async move {
        tx_update_row(&tx, conversation_id, task_id, |row| {
            row.deletion = Some(ChildDeletion::Deleted);
            if row.error.is_none() {
                row.error = Some(DELETED_BY_PARENT.to_owned());
            }
        })
        .await
    })
    .await?;
    Ok(RlmDeleteSubagentResult {
        subagent: entry(&deleted, None, now_ms()),
        outcome: Some("deleted"),
    })
}

fn collect_result(row: &ChildRow, now: f64) -> RlmChildResult {
    if row.is_deleted() {
        // TS `_rlmDeletedCollectEntryForRun`: the delete accepted the
        // cancellation, so the entry reports it as a settled answer.
        return RlmChildResult {
            rlm_child_id: row.rlm_child_id.clone(),
            session_name: Some(row.session_name.clone()),
            session_dir: row.session_dir.clone(),
            status: "cancelled",
            settled: true,
            answer_preview: row.answer_preview.clone(),
            error: Some(
                row.error
                    .clone()
                    .unwrap_or_else(|| DELETED_BY_PARENT.to_owned()),
            ),
            duration_ms: Some(whole_ms(now - row.started_at)),
            tool_use_count: None,
            replied_since_task: None,
            handback: row.handback.as_ref().map(HandbackOutcome::text),
        };
    }
    RlmChildResult {
        rlm_child_id: row.rlm_child_id.clone(),
        session_name: Some(row.session_name.clone()),
        session_dir: row.session_dir.clone(),
        status: row.status.collect_status(),
        settled: row.status.is_terminal(),
        answer_preview: row.answer_preview.clone(),
        error: row.error.clone(),
        duration_ms: Some(whole_ms(now - row.started_at)),
        tool_use_count: None,
        replied_since_task: None,
        handback: row.handback.as_ref().map(HandbackOutcome::text),
    }
}

fn collect_targets(data: &Value) -> anyhow::Result<Vec<String>> {
    match data.get("targets") {
        None | Some(Value::Null) => Ok(Vec::new()),
        Some(Value::Array(items)) => items
            .iter()
            .map(|item| match item.as_str().map(str::trim) {
                Some(target) if !target.is_empty() => Ok(target.to_owned()),
                _ => bail!("rlm.collect targets must be non-empty strings"),
            })
            .collect(),
        Some(_) => bail!("rlm.collect targets must be an array of child ids or names"),
    }
}

/// `rlm.collect`: typed fan-in. Running children are awaited inside one
/// shared wait, `timeout_ms` clamped to the runtime's blocking budget (a
/// longer wait would hold the cell past it); a timeout returns current
/// snapshots, never an error.
async fn collect(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let targets = collect_targets(&call.data)?;
    let requested = match call.data.get("timeout_ms") {
        None | Some(Value::Null) => Duration::ZERO,
        Some(value) => Duration::from_millis(
            value
                .as_u64()
                .ok_or_else(|| anyhow!("rlm.collect timeout_ms must be a non-negative integer"))?,
        ),
    };
    let timeout = requested.min(
        children
            .services
            .settings
            .manager()
            .get_tool_blocking_budget(),
    );
    let harness = children.harness.require().map_err(session_error)?;
    let conversation_id = conversation_of(&call);
    let state = read_children(&harness, conversation_id, &cx())
        .await
        .map_err(session_error)?;
    let mut live: Vec<TaskId> = Vec::new();
    let mut deleted: Vec<TaskId> = Vec::new();
    if targets.is_empty() {
        live.extend(
            state
                .children
                .values()
                .filter(|row| !row.is_deleted())
                .map(ChildRow::task_id),
        );
    }
    for target in &targets {
        // A live row owns its selector; a tombstone answers only a selector
        // no live child holds.
        match resolve(
            state.children.values().filter(|row| !row.is_deleted()),
            target,
        ) {
            Resolved::One(row) => live.push(row.task_id()),
            Resolved::Ambiguous => {
                bail!("RLM child selector \"{target}\" is ambiguous in the current parent session")
            }
            Resolved::None => {
                match resolve(
                    state.children.values().filter(|row| row.is_deleted()),
                    target,
                ) {
                    Resolved::One(row) => deleted.push(row.task_id()),
                    Resolved::None => bail!(
                        "No direct RLM child matches \"{target}\" in the current parent session"
                    ),
                    Resolved::Ambiguous => bail!(
                        "RLM child selector \"{target}\" is ambiguous in the current parent session"
                    ),
                }
            }
        }
    }
    let deadline = tokio::time::Instant::now() + timeout;
    wait_for_verdicts(&harness, conversation_id, &live, deadline).await?;
    let state = read_children(&harness, conversation_id, &cx())
        .await
        .map_err(session_error)?;
    let now = now_ms();
    let results: Vec<RlmChildResult> = live
        .iter()
        .chain(&deleted)
        .filter_map(|task_id| state.children.get(&task_id.to_string()))
        .map(|row| collect_result(row, now))
        .collect();
    Ok(json!({ "results": results }))
}

/// Wait until every child of `task_ids` reached its verdict (its row left
/// `spawning`/`running`) or its task ended, or `deadline` passed. The row,
/// not the task: a settled child's task stays live while its report waits
/// behind the parent's busy turn — possibly the very turn that waits here.
async fn wait_for_verdicts(
    harness: &Harness,
    conversation_id: ConversationId,
    task_ids: &[TaskId],
    deadline: tokio::time::Instant,
) -> anyhow::Result<()> {
    if task_ids.is_empty() || tokio::time::Instant::now() >= deadline {
        return Ok(());
    }
    let changed = Arc::new(Notify::new());
    let watch = harness
        .watch_doc(&CHILDREN_DOC, conversation_id, &cx())
        .await
        .map_err(session_error)?;
    if let Some(watch) = &watch {
        let changed = Arc::clone(&changed);
        watch
            .start(Arc::new(move |_value, _ops, _cx| {
                changed.notify_one();
                futures::future::ready(Ok(())).boxed()
            }))
            .map_err(session_error)?;
    }
    let outcome = async {
        loop {
            let state = read_children(harness, conversation_id, &cx())
                .await
                .map_err(session_error)?;
            let mut pending = None;
            for task_id in task_ids {
                let running = state
                    .children
                    .get(&task_id.to_string())
                    .is_some_and(|row| !row.status.is_terminal());
                let ended = harness
                    .get_task(*task_id, &cx())
                    .await
                    .map_err(session_error)?
                    .is_none_or(|record| record.state.status() == TaskStatus::Terminal);
                if running && !ended {
                    pending = Some(*task_id);
                    break;
                }
            }
            let Some(task_id) = pending else {
                return anyhow::Ok(());
            };
            let woke = tokio::time::timeout_at(deadline, async {
                tokio::select! {
                    () = changed.notified() => Ok(()),
                    ended = harness.wait_for_task(task_id, &cx()) => ended.map(drop),
                }
            })
            .await;
            match woke {
                Ok(woke) => woke.map_err(session_error)?,
                Err(_elapsed) => return Ok(()),
            }
        }
    }
    .await;
    if let Some(watch) = watch {
        watch.stop().await;
    }
    outcome
}

/// `rlm.answer`: the settled-or-not state of the one live child `target`
/// selects, with its full final answer when it kept one (a silent
/// child's): `{status, settled, sessionId, answer?, error?, failure?}`.
async fn answer(children: Arc<Children>, call: HostCall) -> anyhow::Result<Value> {
    let Some(target) = call
        .data
        .get("target")
        .and_then(Value::as_str)
        .map(str::trim)
        .filter(|target| !target.is_empty())
    else {
        bail!("rlm.answer target must be a non-empty string");
    };
    let harness = children.harness.require().map_err(session_error)?;
    let state = read_children(&harness, conversation_of(&call), &cx())
        .await
        .map_err(session_error)?;
    let row = resolve_live(state.children.values(), target, "child")?;
    Ok(json!({
        "status": row.status.collect_status(),
        "settled": row.status.is_terminal(),
        "sessionId": row.session_id,
        "answer": row.answer.clone().or_else(|| row.answer_preview.clone()),
        "error": row.error,
        "failure": row.failure,
    }))
}

// ---------------------------------------------------------------------------
// kwargs helpers
// ---------------------------------------------------------------------------

/// Present-but-non-string kwargs fail like the TS normalizers do.
fn optional_string_kwarg<'a>(
    kwargs: &'a Map<String, Value>,
    key: &str,
    operation: &str,
) -> anyhow::Result<Option<&'a str>> {
    match kwargs.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(value)) => Ok(Some(value)),
        Some(_) => bail!("{operation} {key} must be a string"),
    }
}

fn reject_unsupported_kwargs(
    kwargs: &Map<String, Value>,
    operation: &str,
    supported: &[&str],
) -> anyhow::Result<()> {
    let mut unsupported: Vec<&str> = kwargs
        .keys()
        .map(String::as_str)
        .filter(|key| !supported.contains(key))
        .collect();
    if unsupported.is_empty() {
        return Ok(());
    }
    unsupported.sort_unstable();
    bail!("Unsupported {operation} kwargs: {}", unsupported.join(", "));
}
