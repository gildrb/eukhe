//! The built-in `pi.live` document (`harness/live.ts`, spec §8.2): run control
//! and presentation of the current generation, tool round, and compactions.
//!
//! Run helpers that create generations live in [`run`]; TS keeps them in
//! `generation.ts`, which imports this module back.

pub(crate) mod run;

use eukhe_chord::delta::{Draft, DraftItem, Op};
use eukhe_chord::json::{to_json, JsonObject, JsonValue};
use eukhe_types::pi_ai::AssistantMessage;
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::{Deserialize, Serialize};

use crate::documents::{ConversationDoc, DocDefinition};
use crate::harness::scheduler::SchedulerOutcome;
use crate::harness::types::{CompactionReason, ToolDiagnostic};
use crate::session::{SessionResult, Tx};
use crate::types::{
    AnyTaskRecord, CheckpointInfo, EntryId, LatestFork, SubmissionId, SubmissionSettlement, TaskId,
};

/// Status of one tool call of the current round.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ToolSlotStatus {
    Pending,
    Running,
    Done,
}

/// Presentation of one tool call of the current round.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ToolSlot {
    pub call_id: String,
    pub name: String,
    /// Absent for a call not started yet (sequential round) and for a call its
    /// request did not offer, which starts `done` with the `entry` generation
    /// wrote.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub task_id: Option<TaskId>,
    pub status: ToolSlotStatus,
    /// Retained running output and what the bounds dropped.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dropped_bytes: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub dropped_lines: Option<u64>,
    /// Last `details()` value.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub details: Option<JsonValue>,
    /// Diagnostics recorded through `api.diagnostic()`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub diagnostics: Option<Vec<ToolDiagnostic>>,
    /// Result entry once done; absent when the tool task faulted or was orphaned.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub entry: Option<EntryId>,
}

/// A durable backoff before the next attempt.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LiveRetry {
    pub at: f64,
    pub error: String,
}

/// Presentation of one live compaction task (spec §8.7).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CompactionStatus {
    pub task_id: TaskId,
    pub reason: CompactionReason,
    /// Whether a generation waits for it: a compaction the generation owns.
    pub blocking: bool,
    pub attempt: u64,
    /// Durable backoff before the next summarization attempt.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub retry: Option<LiveRetry>,
}

/// Run control: the task that settles the run's inputs, and those inputs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LiveRun {
    pub task_id: TaskId,
    pub inputs: Vec<SubmissionId>,
}

/// A provider-side deferred response being polled.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LiveDeferred {
    pub poll_at: f64,
}

/// Presentation of the current generation attempt.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LiveGeneration {
    pub attempt: u64,
    /// Committed throttled partial of the in-flight response.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub message: Option<AssistantMessage>,
    /// Durable backoff before the next attempt.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub retry: Option<LiveRetry>,
    /// Provider-side deferred response being polled.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub deferred: Option<LiveDeferred>,
}

/// Built-in live conversation state: run control and presentation of the
/// current generation and tool round.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct LiveState {
    /// Present exactly while busy.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub run: Option<LiveRun>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub generation: Option<LiveGeneration>,
    /// The current tool round in call order, from the tool-calling answer
    /// until the generation's `tools` phase ends it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tools: Option<Vec<ToolSlot>>,
    /// Live compaction tasks in task ID order; absent when none.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub compactions: Option<Vec<CompactionStatus>>,
}

// REMINDER: a complete base whenever nothing runs (spec §8.2): no generation
// and no running tool slot. That holds while idle, in the commit handing a
// generation over to its tool round, and between tools, so the delta chain
// spans at most one generation or the overlapping execution of one round's
// tools. A slot holds output only while running, so every base is small. Do
// not add a delta-count bound; the tool output benchmark checks this rule.
fn live_checkpoint_when(value: &JsonObject, _ops: &[Op], _info: CheckpointInfo) -> bool {
    value.get("generation").is_none()
        && !value
            .get("tools")
            .and_then(JsonValue::as_array)
            .unwrap_or_default()
            .iter()
            .any(|slot| slot.get("status").and_then(JsonValue::as_str) == Some("running"))
}

/// The `pi.live` document token (TS `LiveDoc`).
pub static LIVE_DOC: ConversationDoc<LiveState> = match ConversationDoc::define(
    DocDefinition {
        kind: "pi.live",
        version: 1,
        initial: LiveState::default,
        migrate: None,
        checkpoint_when: Some(live_checkpoint_when),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("invalid pi.live definition"),
};

/// Built-in task kinds that can own `pi.live.run`.
const RUN_TASK_KINDS: [&str; 1] = ["pi.generation"];
const TOOL_TASK_KIND: &str = "pi.tool";
const COMPACTION_TASK_KIND: &str = "pi.compaction";

/// A container child of `draft` at `key`, if present.
pub(crate) fn child_draft(draft: &Draft, key: &str) -> SessionResult<Option<Draft>> {
    Ok(draft.get(key)?.and_then(DraftItem::into_draft))
}

/// The task ID stored at `key` of an object draft, if any.
fn task_id_at(draft: &Draft, key: &str) -> SessionResult<Option<TaskId>> {
    Ok(match draft.get(key)? {
        Some(DraftItem::Value(value)) => value.as_u64().map(TaskId::from_number),
        Some(DraftItem::Draft(_)) | None => None,
    })
}

/// The task that owns `pi.live.run`, if busy.
///
/// # Errors
///
/// A tracker failure.
pub fn run_task_id(live: &Draft) -> SessionResult<Option<TaskId>> {
    match child_draft(live, "run")? {
        Some(run) => task_id_at(&run, "taskId"),
        None => Ok(None),
    }
}

/// End the run owned by `task_id`: settle each of its inputs and remove
/// `run`. Always removes `generation` and `tools`, whose presentation belongs
/// to the ending run.
///
/// # Errors
///
/// The transaction settled, or a tracker failure.
pub fn end_run(
    tx: &Tx,
    live: &Draft,
    task_id: TaskId,
    settlement: &SubmissionSettlement,
) -> SessionResult<()> {
    if let Some(run) = child_draft(live, "run")? {
        if task_id_at(&run, "taskId")? == Some(task_id) {
            let inputs = run.child("inputs")?.value()?;
            for input in inputs.as_array().unwrap_or_default() {
                if let Some(id) = input.as_u64() {
                    tx.settle_submission(SubmissionId::from_number(id), settlement.clone())?;
                }
            }
            live.delete("run")?;
        }
    }
    live.delete("generation")?;
    live.delete("tools")?;
    Ok(())
}

/// Add the status of a compaction task created in this commit; statuses stay
/// in task ID order.
///
/// # Errors
///
/// A tracker or JSON failure.
pub fn add_compaction_status(live: &Draft, status: &CompactionStatus) -> SessionResult<()> {
    if live.get("compactions")?.is_none() {
        live.set("compactions", JsonValue::array())?;
    }
    live.child("compactions")?.push([to_json(status)?])?;
    Ok(())
}

/// Index of the array item whose `taskId` is `task_id`.
fn find_by_task(items: &Draft, task_id: TaskId) -> SessionResult<Option<usize>> {
    for index in 0..items.len()? {
        if task_id_at(&items.child(index)?, "taskId")? == Some(task_id) {
            return Ok(Some(index));
        }
    }
    Ok(None)
}

/// The status of compaction task `task_id`, if listed.
///
/// # Errors
///
/// A tracker failure.
pub fn compaction_status(live: &Draft, task_id: TaskId) -> SessionResult<Option<Draft>> {
    let Some(statuses) = child_draft(live, "compactions")? else {
        return Ok(None);
    };
    match find_by_task(&statuses, task_id)? {
        Some(index) => Ok(Some(statuses.child(index)?)),
        None => Ok(None),
    }
}

/// Remove the status of compaction task `task_id`, and the list once empty.
///
/// # Errors
///
/// A tracker failure.
pub fn remove_compaction_status(live: &Draft, task_id: TaskId) -> SessionResult<()> {
    let Some(statuses) = child_draft(live, "compactions")? else {
        return Ok(());
    };
    if let Some(index) = find_by_task(&statuses, task_id)? {
        statuses.splice(
            i64::try_from(index).unwrap_or(i64::MAX),
            1,
            Vec::<JsonValue>::new(),
        )?;
    }
    if statuses.is_empty()? {
        live.delete("compactions")?;
    }
    Ok(())
}

/// The slot of tool task `task_id` in the current round, if the round still
/// lists it.
///
/// # Errors
///
/// A tracker failure.
pub fn tool_slot(live: &Draft, task_id: TaskId) -> SessionResult<Option<Draft>> {
    let Some(tools) = child_draft(live, "tools")? else {
        return Ok(None);
    };
    match find_by_task(&tools, task_id)? {
        Some(index) => Ok(Some(tools.child(index)?)),
        None => Ok(None),
    }
}

/// Mark a slot done: the result entry, if any, now carries its running
/// output, details, and diagnostics.
///
/// # Errors
///
/// A tracker or JSON failure.
pub fn finish_slot(slot: &Draft, entry: Option<EntryId>) -> SessionResult<()> {
    slot.set("status", "done")?;
    if let Some(entry) = entry {
        slot.set("entry", to_json(&entry)?)?;
    }
    clear_progress(slot)
}

/// Remove what a tool published while running; its result entry or a rerun
/// replaces it.
///
/// # Errors
///
/// A tracker failure.
pub fn clear_progress(slot: &Draft) -> SessionResult<()> {
    for key in [
        "output",
        "droppedBytes",
        "droppedLines",
        "details",
        "diagnostics",
    ] {
        slot.delete(key)?;
    }
    Ok(())
}

/// Harness cleanup for a terminal outcome the scheduler writes itself
/// (`faulted` or `orphaned`). A run task ends its run; a tool task's slot is
/// marked done without an entry, and context derivation synthesizes the
/// missing result; a compaction task's status is removed.
///
/// Ignores other kinds so it never creates `pi.live` elsewhere. The scheduler
/// calls this without knowing task kinds; the Harness passes it in (spec
/// §5.4).
///
/// REMINDER: a committed generation partial becomes an aborted assistant
/// entry here, exactly as in the generation abort handler, so the transcript
/// keeps what the model produced and `pi.usage` counts its spend. The
/// scheduler's commit has no task scope, so that entry has no `byTaskId`.
/// Faults come from task bugs or malformed provider data (a non-JSON value in
/// a response), or a commit the Storage rejected without effect; an uncertain
/// storage failure poisons the Session instead and writes no outcome.
pub fn settle_scheduler_outcome(
    tx: Tx,
    record: AnyTaskRecord,
    outcome: SchedulerOutcome,
) -> BoxFuture<'static, SessionResult<()>> {
    async move {
        if record.kind == TOOL_TASK_KIND {
            let live = tx.doc(&LIVE_DOC, record.conversation_id).await?;
            if let Some(slot) = tool_slot(&live, record.id)? {
                finish_slot(&slot, None)?;
            }
            return Ok(());
        }
        if record.kind == COMPACTION_TASK_KIND {
            let live = tx.doc(&LIVE_DOC, record.conversation_id).await?;
            return remove_compaction_status(&live, record.id);
        }
        if !RUN_TASK_KINDS.contains(&record.kind.as_str()) {
            return Ok(());
        }
        let live = tx.doc(&LIVE_DOC, record.conversation_id).await?;
        if run_task_id(&live)? != Some(record.id) {
            return Ok(());
        }
        run::convert_partial(&tx, &live, record.conversation_id).await?;
        let settlement = match &outcome {
            SchedulerOutcome::Faulted { error } => SubmissionSettlement::Unanswered {
                reason: "faulted".to_owned(),
                detail: Some(JsonValue::from(error.message.as_str())),
            },
            SchedulerOutcome::Orphaned { reason } => SubmissionSettlement::Unanswered {
                reason: reason.clone(),
                detail: None,
            },
        };
        end_run(&tx, &live, record.id, &settlement)
    }
    .boxed()
}
