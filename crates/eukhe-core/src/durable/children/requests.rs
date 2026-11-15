//! The `rlm.*` kernel host requests over the durable children registry:
//! the spawns of [`super::spawn`] (`rlm.run`, `rlm.split`, and the tree
//! facts of a crown its caller keeps), `rlm.find_models`,
//! `rlm.list_subagents`, `rlm.delete_subagent`, `rlm.collect`,
//! `rlm.answer`, and `rlm.progress.note` (`rlm.rename` lives in
//! [`super::rename`]).

use std::future::Future;
use std::sync::Arc;
use std::time::Duration;

use anyhow::{anyhow, bail};
use eukhe_ai::auth::AuthOperationOptions;
use eukhe_bend::rules::agent_tree::{self, Action, View};
use eukhe_bend::rules::worker::GateKind;
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{CommitListener, SessionError, SessionResult, Tx};
use eukhe_durable::types::{
    CommitChange, CommitPublication, ConversationId, DocumentObserverExt, InputSubmission,
    SubmissionState, TaskId, TaskStatus, ROOT_CONVERSATION_ID,
};
use futures::FutureExt;
use serde_json::{json, Value};
use tokio::sync::Notify;

use super::host::{RlmChildDeleteRequest, RlmChildListing, RlmChildVerdict, RlmSubagentHost};
use super::notice::DELETED_BY_PARENT;
use super::progress::{tx_note, utf16_length, NoteOutcome, RLM_PROGRESS_NOTE_MAX_LENGTH};
use super::registry::{
    read_children, resolve, tx_update_row, ChildDeletion, ChildRow, HandbackOutcome, Resolved,
    CHILDREN_DOC,
};
use super::task::report_request_id;
use super::wire::{RlmChildResult, RlmDeleteSubagentResult, RlmSubagentActivity, RlmSubagentEntry};
use super::Children;
use crate::durable::deps::{HostCall, HostRequestRegistry};
use crate::kernel::cancellation::AbortSignal;
use crate::kernel::rlm_runtime::{
    find_rlm_model_matches, RlmModelInfo, DEFAULT_RLM_MODEL_SEARCH_LIMIT,
    MAX_RLM_MODEL_SEARCH_LIMIT,
};

/// Register every `rlm.*` handler of `children` onto `registry`. A spawn
/// (`rlm.run`, `rlm.split`) first asks at the run pause's gate: a paused
/// session starts none until it runs again. A spawn that fails shows the
/// user its error once ([`super::spawn::show_spawn_failure`]); the model
/// reads it as the tool's result.
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
    macro_rules! spawning {
        ($request_type:literal, $operation:literal, $function:path) => {{
            let children = Arc::clone(children);
            registry.register(
                $request_type,
                Arc::new(move |call: HostCall| {
                    let children = Arc::clone(&children);
                    async move {
                        children
                            .pause
                            .gate(GateKind::Spawn, &cx())
                            .await
                            .map_err(session_error)?;
                        let api = call.call.clone();
                        let spawned = $function(Arc::clone(&children), call).await;
                        if let Err(error) = &spawned {
                            super::spawn::show_spawn_failure(&children, api, $operation, error)
                                .await;
                        }
                        spawned
                    }
                    .boxed()
                }),
            );
        }};
    }
    handler!("rlm.find_models", find_models);
    handler!("rlm.progress.note", progress_note);
    spawning!("rlm.run", "rlm.spawn", super::spawn::run);
    spawning!("rlm.split", "rlm.split", super::spawn::split);
    handler!("rlm.tree_facts", super::spawn::tree_facts);
    handler!("rlm.tree_lend", super::spawn::tree_lend);
    handler!("rlm.tree_return", super::spawn::tree_return);
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
pub(super) fn whole_ms(value: f64) -> u64 {
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

/// `rlm.list_subagents`: the roster. A listing is no read ([`mark_read`]):
/// it shows a settled child's compacted answer preview, never its full
/// answer, so the child's report still reaches the parent.
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
        let live = row.live_task();
        harness.abort_task(live, cx).await.map_err(session_error)?;
        harness
            .wait_for_task(live, cx)
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
            acceptance: row.acceptance.as_ref().map(RlmChildVerdict::summary),
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
        acceptance: row.acceptance.as_ref().map(RlmChildVerdict::summary),
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
/// shared wait, `timeout_ms` clamped to the cap of every wait on the
/// agent's work (30 minutes, the compiled core's `wait_any` timeout; the
/// kernel keeps a cell inside it from detaching at its blocking budget);
/// a timeout returns current snapshots, never an error. The agent tree's
/// next action ends the wait (T10): a queued message first, then the
/// first result that arrived. A wait the message ended answers
/// `end: "message"` and leaves the children running, their reports owed.
/// `arrived` names the waited children settled and unread when the wait
/// ended. An abort of the turn that stops the waiting cell (Esc) cancels
/// the children it waited on ([`cancel_waited`]) and fails the wait.
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
    let timeout = requested.min(Duration::from_secs(
        eukhe_bend::rules::wait_any::timeout_secs(None),
    ));
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
    let mut waited = wait_for_verdicts(
        &harness,
        conversation_id,
        &live,
        deadline,
        call.signal.as_ref(),
    )
    .await?;
    if waited == Waited::Stopped {
        if turn_aborted(&harness, &call).await? {
            cancel_waited(&harness, conversation_id, &live).await?;
            bail!("rlm.collect aborted: the turn was cancelled");
        }
        // A stop that is no abort request (a closing session signals the
        // call without marking it) leaves the children running; the wait
        // goes on as before it.
        waited = wait_for_verdicts(&harness, conversation_id, &live, deadline, None).await?;
    }
    let state = read_children(&harness, conversation_id, &cx())
        .await
        .map_err(session_error)?;
    let rows: Vec<&ChildRow> = live
        .iter()
        .filter_map(|task_id| state.children.get(&task_id.to_string()))
        .collect();
    let arrived: Vec<&str> = rows
        .iter()
        .filter(|row| row.status.is_terminal() && !row.read)
        .map(|row| row.rlm_child_id.as_str())
        .collect();
    mark_read(&harness, conversation_id, &call, rows.iter().copied()).await?;
    let now = now_ms();
    let results: Vec<RlmChildResult> = rows
        .iter()
        .copied()
        .chain(
            deleted
                .iter()
                .filter_map(|task_id| state.children.get(&task_id.to_string())),
        )
        .map(|row| collect_result(row, now))
        .collect();
    Ok(match waited {
        Waited::Message => json!({ "results": results, "arrived": arrived, "end": "message" }),
        Waited::Over | Waited::Arrived | Waited::Stopped => {
            json!({ "results": results, "arrived": arrived })
        }
    })
}

/// The parent read the outcome of each settled child of `rows` through a
/// cell of its own tool call (`call`): its report reached the parent. Each
/// unread one turns read and its queued report is withdrawn (`Collect` in
/// `bend/child.bend`), so its report phase ends without waking the parent
/// for a turn that restates what it read. A request outside a tool call (a
/// detached job's) reads for nobody.
async fn mark_read<'a>(
    harness: &Harness,
    conversation_id: ConversationId,
    call: &HostCall,
    rows: impl IntoIterator<Item = &'a ChildRow>,
) -> anyhow::Result<()> {
    if call.call.is_none() {
        return Ok(());
    }
    let task_ids: Vec<TaskId> = rows
        .into_iter()
        .filter(|row| row.status.is_terminal() && !row.read)
        .map(ChildRow::task_id)
        .collect();
    if task_ids.is_empty() {
        return Ok(());
    }
    let queued = commit(harness, conversation_id, move |tx| async move {
        let mut queued = Vec::new();
        for task_id in task_ids {
            let row = tx_update_row(&tx, conversation_id, task_id, |row| row.read = true).await?;
            queued.extend(row.report_submission);
        }
        Ok(queued)
    })
    .await?;
    for submission in queued {
        harness
            .abort_submission(submission, Some(conversation_id), &cx())
            .await
            .map_err(session_error)?;
    }
    Ok(())
}

/// How [`wait_for_verdicts`] ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Waited {
    /// Every child reached its verdict, or the deadline passed.
    Over,
    /// A child's result arrived while others still run.
    Arrived,
    /// A message for the parent is queued: it reads it first.
    Message,
    /// The requesting cell's stop signal fired first.
    Stopped,
}

/// Wait on the children of `task_ids` until the agent tree's next action
/// is no wait (T10: a queued message, else a result that arrived: a
/// child's verdict the parent has not read), every child reached its
/// verdict (its row left `spawning`/`running`) or its task ended, or
/// `deadline` passed, or `stop` (the requesting cell's stop signal) fired.
/// The row, not the task: a settled child's task stays live while its
/// report waits behind the parent's busy turn — possibly the very turn
/// that waits here.
async fn wait_for_verdicts(
    harness: &Harness,
    conversation_id: ConversationId,
    task_ids: &[TaskId],
    deadline: tokio::time::Instant,
    stop: Option<&AbortSignal>,
) -> anyhow::Result<Waited> {
    if task_ids.is_empty() || tokio::time::Instant::now() >= deadline {
        return Ok(Waited::Over);
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
    let inputs = {
        let changed = Arc::clone(&changed);
        let listener: CommitListener = Arc::new(move |publication, _| {
            if moves_inputs(publication, conversation_id) {
                changed.notify_one();
            }
        });
        harness.subscribe_commits(listener).map_err(session_error)?
    };
    let outcome = async {
        loop {
            let state = read_children(harness, conversation_id, &cx())
                .await
                .map_err(session_error)?;
            let mut pending = None;
            let mut arrived: u64 = 0;
            for task_id in task_ids {
                let row = state.children.get(&task_id.to_string());
                let running = row.is_some_and(|row| !row.status.is_terminal());
                let live = row.map_or(*task_id, ChildRow::live_task);
                let ended = harness
                    .get_task(live, &cx())
                    .await
                    .map_err(session_error)?
                    .is_none_or(|record| record.state.status() == TaskStatus::Terminal);
                if running && !ended {
                    pending.get_or_insert(live);
                } else if row.is_some_and(|row| row.status.is_terminal() && !row.read) {
                    arrived += 1;
                }
            }
            let Some(task_id) = pending else {
                return anyhow::Ok(Waited::Over);
            };
            let view = View {
                message: message_queued(harness, conversation_id).await?,
                arrived,
                own_work: false,
            };
            match agent_tree::next(view) {
                Action::ReadMessage => return Ok(Waited::Message),
                Action::Integrate => return Ok(Waited::Arrived),
                Action::WorkOwn | Action::Wait => {}
            }
            let woke = tokio::time::timeout_at(deadline, async {
                tokio::select! {
                    () = changed.notified() => Ok(None),
                    ended = harness.wait_for_task(task_id, &cx()) => ended.map(|_| None),
                    () = stopped(stop) => Ok(Some(Waited::Stopped)),
                }
            })
            .await;
            match woke {
                Ok(woke) => {
                    if let Some(waited) = woke.map_err(session_error)? {
                        return Ok(waited);
                    }
                }
                Err(_elapsed) => return Ok(Waited::Over),
            }
        }
    }
    .await;
    inputs.unsubscribe();
    if let Some(watch) = watch {
        watch.stop().await;
    }
    outcome
}

/// Whether `publication` queues, places or settles an input of
/// `conversation_id`.
fn moves_inputs(publication: &CommitPublication, conversation_id: ConversationId) -> bool {
    publication.changes.iter().any(|change| match change {
        CommitChange::Submission(record) => record.conversation_id == conversation_id,
        CommitChange::Conversation(_)
        | CommitChange::Entry(_)
        | CommitChange::Task(_)
        | CommitChange::Document(_) => false,
    })
}

/// Whether an input other than a child's report waits queued for
/// `conversation_id`: a user message or steer, a peer's message, a job
/// notice. A report is a child's result, read through its row.
async fn message_queued(
    harness: &Harness,
    conversation_id: ConversationId,
) -> anyhow::Result<bool> {
    let inspection = harness.inspect(&cx()).await.map_err(session_error)?;
    Ok(inspection.submissions.iter().any(|submission| {
        submission.conversation_id == conversation_id
            && matches!(
                submission.state,
                SubmissionState::Input(InputSubmission::Queued)
            )
            && !submission.request_id.as_deref().is_some_and(is_report)
    }))
}

/// Whether `request_id` names a child's report ([`report_request_id`]).
fn is_report(request_id: &str) -> bool {
    request_id
        .strip_prefix("rlm:")
        .and_then(|rest| rest.split_once(":report:"))
        .and_then(|(task, ordinal)| task.parse::<u64>().ok().zip(ordinal.parse::<u32>().ok()))
        .is_some_and(|(task, ordinal)| {
            report_request_id(TaskId::from_number(task), ordinal) == request_id
        })
}

/// Resolves when `stop` fires; never without one.
async fn stopped(stop: Option<&AbortSignal>) {
    match stop {
        Some(stop) => stop.cancelled().await,
        None => std::future::pending().await,
    }
}

/// Whether the stop of the cell `call` runs is an abort of its turn: the
/// `python` call carries an abort request's mark (a closing session signals
/// the call without marking it, and a restart's mark is no abort request).
async fn turn_aborted(harness: &Harness, call: &HostCall) -> anyhow::Result<bool> {
    let Some(api) = &call.call else {
        return Ok(false);
    };
    let record = harness
        .get_task(api.task_id(), &cx())
        .await
        .map_err(session_error)?;
    Ok(record.is_some_and(|record| record.abort_requested && record.abort_reason.is_none()))
}

/// Cancel the children of `task_ids` still running: the turn whose cell
/// waited on them was aborted, and an aborted wait cancels every handle it
/// awaited, then waits for each to settle. Each child task's abort cancels the
/// child's run at the host and marks its row cancelled, owing no report
/// (`task::abort`); a child that reached its verdict keeps it.
async fn cancel_waited(
    harness: &Harness,
    conversation_id: ConversationId,
    task_ids: &[TaskId],
) -> anyhow::Result<()> {
    let state = read_children(harness, conversation_id, &cx())
        .await
        .map_err(session_error)?;
    let running: Vec<TaskId> = task_ids
        .iter()
        .filter_map(|task_id| state.children.get(&task_id.to_string()))
        .filter(|row| !row.settled && !row.status.is_terminal())
        .map(ChildRow::live_task)
        .collect();
    for task_id in &running {
        harness
            .abort_task(*task_id, &cx())
            .await
            .map_err(session_error)?;
    }
    for task_id in running {
        harness
            .wait_for_task(task_id, &cx())
            .await
            .map_err(session_error)?;
    }
    Ok(())
}

/// `rlm.answer`: the settled-or-not state of the one live child `target`
/// selects, with its full final answer when it kept one (a silent
/// child's): `{status, settled, sessionId, answer?, error?, failure?,
/// scopedHandback?, patch?}`: a finished writer's hand-back by its scope,
/// a failed or cancelled writer's partial patch (not applied).
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
    let conversation_id = conversation_of(&call);
    let state = read_children(&harness, conversation_id, &cx())
        .await
        .map_err(session_error)?;
    let row = resolve_live(state.children.values(), target, "child")?;
    mark_read(&harness, conversation_id, &call, [row]).await?;
    let scoped = match &row.handback {
        Some(HandbackOutcome::Done { handback }) => Some(&handback.handback),
        Some(HandbackOutcome::Failed { .. }) | None => None,
    };
    Ok(json!({
        "status": row.status.collect_status(),
        "settled": row.status.is_terminal(),
        "sessionId": row.session_id,
        "answer": row.answer.clone().or_else(|| row.answer_preview.clone()),
        "error": row.error,
        "failure": row.failure,
        "scopedHandback": scoped,
        "patch": row.patch,
    }))
}
