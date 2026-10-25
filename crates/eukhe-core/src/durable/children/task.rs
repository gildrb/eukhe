//! The `eukhe.rlm.child` durable task: one per spawned child, background and
//! owned by the spawning conversation, so a child's lifecycle survives a
//! parent restart (the old daemon settle watcher died with the worker).
//!
//! Phases: `spawn` (host create under the identity derived from the task
//! id), `prompt` (at once, while the spawning tool call may still run),
//! `watch` (host long-poll; a pause between polls, which a reopened
//! parent's first poll skips; child usage attributed per poll; the watch's
//! clock ([`Vigil`]) reports a child with no progress for
//! `subagentStallMs` as stalled and one whose polls fail
//! [`CHILD_POLL_FAILURES`] times in a row as unreachable), `report` (a
//! follow-up input to the parent with a request id, so a rerun cannot
//! report twice, held until it reaches the parent's transcript and
//! submitted again under the next id when the inbox withdraws it), then
//! terminal. Abort cancels the child's run and delivers the report a
//! delete owes. `bend/child.bend` models the phases (docs/harness.md H5);
//! the bridge test runs their decisions ([`watched_next`],
//! [`report_step`], [`owed_on_abort`]) against its `step`.

use std::collections::HashSet;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::Entry;
use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_durable::harness::types::{
    ConversationHandle, InputSubmissionDraft, Submission, WhenBusy,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::tasks::{
    define_task, AnyTask, Migrated, NextTaskState, RunningTask, Task, TaskDefinition, TaskRuntime,
};
use eukhe_durable::types::{
    SubmissionState, SubmissionStatus, TaskId, TaskOptions, TaskOutcome, TaskOutcomeError,
    TaskOwnership,
};
use eukhe_types::input_origin::ChildFailure;
use eukhe_types::pi_ai::UserContent;
use serde::{Deserialize, Serialize};

use super::host::{
    ChildMessageKind, RlmChildCancelRequest, RlmChildHandbackRequest, RlmChildObservation,
    RlmChildPromptRequest, RlmChildRunState, RlmChildSpawnRequest, RlmChildWaitRequest,
    RlmSubagentHost,
};
use super::notice::{ChildReport, DELETED_BY_PARENT};
use super::registry::{
    child_identity, read_children, tx_attribute_usage, tx_remove_row, tx_row, tx_update_row,
    ChildRow, ChildStatus, HandbackOutcome,
};
use super::watch::{get_report, verdict, Call, Obs, Report, Vigil, CHILD_POLL_FAILURES};
use crate::child_workspace::WorkspaceMode;
use crate::durable::deps::SessionClosing;
use crate::durable::observe::semantic_edges::{
    last_committed_request_id, SemanticEdgeRecorder, SEMANTIC_EDGES_LEDGER_FILENAME,
};
use crate::durable::settings::EukheSettings;

/// The task kind.
pub(crate) const CHILD_TASK_KIND: &str = "eukhe.rlm.child";
/// One long-poll slice of the settle watch.
pub(crate) const WATCH_WAIT_SLICE_MS: u64 = 60_000;
/// Re-poll cadence after a slice ends without a settled child; each failed
/// poll in a row doubles it, so the failed polls that report a child
/// unreachable span a minute and more (a restarting worker is back by
/// then).
pub(crate) const WATCH_POLL_INTERVAL_MS: f64 = 2_000.0;
/// The error text of a run the user cancelled (no notice is owed).
const CANCELLED_BY_USER: &str = "Cancelled by user";
/// Ordinal of a report's first submission; each redelivery of a withdrawn
/// submission takes the next one.
const FIRST_REPORT_ORDINAL: u32 = 1;

/// What the child-task phases need from the session.
pub(crate) struct ChildrenServices {
    pub(crate) host: Arc<dyn RlmSubagentHost>,
    pub(crate) parent_session_id: String,
    /// This (the parent) session's depth; children run one deeper.
    pub(crate) rlm_depth: u32,
    pub(crate) rlm_max_depth: u32,
    /// The parent's semantic-edge recorder: a settled child's return is
    /// claimed on it before its notice (TS `recordChildReturned`).
    pub(crate) semantic_edges: Option<Arc<SemanticEdgeRecorder>>,
    /// The parent's closing gate: a closing parent admits no report.
    pub(crate) closing: SessionClosing,
    /// The session settings: `subagentStallMs`, the blocking budget.
    pub(crate) settings: Arc<EukheSettings>,
    /// The child tasks whose watch polled since this session opened (by
    /// task id): the pause before a re-poll is this session's own.
    pub(crate) polled: Mutex<HashSet<u64>>,
}

/// Input of one child task (the validated `rlm.spawn` request).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct ChildTaskInput {
    pub(crate) prompt: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) model: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) thinking: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) spawned_by_request_id: Option<String>,
    /// The depth bound in force at the spawn (a runtime override or the
    /// configured bound); `None` on tasks admitted before it was recorded.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) max_depth: Option<u32>,
    /// Where the child works; `None` when the caller did not choose (the
    /// shared workspace).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) workspace: Option<WorkspaceMode>,
    /// Set on a task that carries the report an aborted child task owed:
    /// it starts in the report phase. An abort cannot wait for the parent
    /// to place a report, so it hands the report to this task, which the
    /// abort does not reach.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) owed: Option<OwedReport>,
    /// Whether the settled child reports to the parent's inbox (absent in
    /// tasks admitted before it: the inbox).
    #[serde(default, skip_serializing_if = "ReportMode::is_inbox")]
    pub(crate) report: ReportMode,
    /// Set on a re-task (`assign`) of the existing child of this spawn
    /// task: the task starts in the prompt phase on that child; its row
    /// and identity are that task's, while this task's own id names its
    /// prompt and its report's request ids.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) child: Option<u64>,
    /// What the prompt is to the child (a re-task may carry the user's
    /// context or redirect to an idle child); absent: a task.
    #[serde(default, skip_serializing_if = "is_task")]
    pub(crate) kind: ChildMessageKind,
    /// More details of the prompt's row (`userMessages`, `note`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) details: Option<serde_json::Map<String, serde_json::Value>>,
    /// The child is a worker of a main session (`sessionShape`
    /// `main-worker`): it gets the chat view and the worker doctrine, and
    /// main's worker tools reach it.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub(crate) worker: bool,
}

#[expect(
    clippy::trivially_copy_pass_by_ref,
    reason = "serde's skip_serializing_if passes the field by reference"
)]
fn is_task(kind: &ChildMessageKind) -> bool {
    *kind == ChildMessageKind::Task
}

/// Where a settled child's outcome goes.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) enum ReportMode {
    /// A follow-up input to the parent (the `rlm.spawn` default).
    #[default]
    Inbox,
    /// Only the registry row: the spawner reads the outcome itself (a
    /// dynamic workflow's agents), and the row keeps the full answer.
    Silent,
}

impl ReportMode {
    #[expect(
        clippy::trivially_copy_pass_by_ref,
        reason = "serde's skip_serializing_if passes the field by reference"
    )]
    fn is_inbox(&self) -> bool {
        match self {
            Self::Inbox => true,
            Self::Silent => false,
        }
    }
}

/// A report an aborted child task hands on.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct OwedReport {
    /// The child task the report is of: its registry row and the report's
    /// request ids are that task's.
    pub(crate) child: u64,
    pub(crate) report: ChildReport,
    /// Submissions the parent withdrew so far.
    pub(crate) withdrawn: u32,
}

impl OwedReport {
    /// The checkpoint of the task that carries the report on.
    fn checkpoint(&self) -> ChildCheckpoint {
        ChildCheckpoint::Report {
            report: self.report.clone(),
            withdrawn: self.withdrawn,
        }
    }
}

/// Checkpoint of one child task.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
pub(crate) enum ChildCheckpoint {
    Spawn,
    Prompt,
    #[serde(rename_all = "camelCase")]
    Watch {
        poll: u64,
        /// Harness clock before which the next poll of this session does
        /// not start (a reopened parent's first poll runs at once).
        next_poll_at: f64,
        /// The watch's clock on the child (absent in checkpoints stored
        /// before it: a fresh clock).
        #[serde(default)]
        vigil: Vigil,
    },
    Report {
        report: ChildReport,
        /// Submissions of the report the parent's inbox withdrew before
        /// placing them; the next one takes the next request id.
        #[serde(default)]
        withdrawn: u32,
    },
}

/// The task definition: `Task<input, checkpoint, final status, no hooks>`.
pub(crate) type ChildTask = Task<ChildTaskInput, ChildCheckpoint, ChildStatus, ()>;
type Runtime = TaskRuntime<ChildTaskInput, ChildCheckpoint, ChildStatus, ()>;
type Running = RunningTask<ChildTaskInput, ChildCheckpoint, ChildStatus>;
type Next = NextTaskState<ChildCheckpoint, ChildStatus>;

/// The follow-up request id of submission `ordinal` of the report of child
/// task `task_id`.
pub(crate) fn report_request_id(task_id: TaskId, ordinal: u32) -> String {
    format!("rlm:{task_id}:report:{ordinal}")
}

/// Where the parent's inbox holds a submission of the report; `S` is the
/// handle the report phase waits on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Fate<S> {
    Queued(S),
    Withdrawn,
    Placed,
}

impl<S> Fate<S> {
    /// The fate of `submission` in `state`: placed once it has a
    /// transcript entry, withdrawn once it settled without one.
    pub(crate) fn of(state: &SubmissionState, submission: S) -> Self {
        if state.entry().is_some() {
            Self::Placed
        } else if state.status() == SubmissionStatus::Queued {
            Self::Queued(submission)
        } else {
            Self::Withdrawn
        }
    }
}

/// The report phase's next move.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ReportStep<S> {
    /// Submit the report under this ordinal (a known request id finds its
    /// submission).
    Submit(u32),
    /// Wait for the queued submission to settle.
    Wait(S),
    /// The inbox withdrew it: the checkpoint counts this many withdrawn,
    /// and the next invocation submits it again under the next ordinal.
    Again(u32),
    /// It reached the parent's transcript: the task ends.
    Done,
}

/// The ordinal of the next submission of a report the parent's inbox
/// withdrew `withdrawn` submissions of.
fn report_ordinal(withdrawn: u32) -> u32 {
    FIRST_REPORT_ORDINAL + withdrawn
}

/// The count of withdrawn submissions of a report whose next submission
/// goes under `ordinal` (a reply of the compiled core).
fn withdrawn_of(ordinal: u64) -> SessionResult<u32> {
    u32::try_from(ordinal)
        .ok()
        .and_then(|ordinal| ordinal.checked_sub(FIRST_REPORT_ORDINAL))
        .ok_or_else(|| SessionError::error(format!("a report ordinal out of range: {ordinal}")))
}

/// The child task's request to the compiled core, and its reply decoded
/// by `decode`.
fn ask<T>(request: &mut Writer, decode: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>) -> T {
    let answer = (|| -> Result<T, eukhe_bend::Error> {
        let reply = eukhe_bend::call(Entry::Child, &request.finish()?)?;
        let mut reply = Reader::reply(&reply)?;
        let value = decode(&mut reply)?;
        reply.end()?;
        Ok(value)
    })();
    eukhe_bend::expect_core(Entry::Child, answer)
}

/// The report phase's move as the core answers it (`Move` in
/// `bend/child.bend`).
enum Move {
    Submit(u64),
    Await,
    Resubmit(u64),
    Delivered,
}

/// The one report rule (`owe.next` in `bend/child.bend`, run by the
/// compiled Bend core; `child_report_move`): the move of the report phase
/// whose report had `withdrawn` submissions withdrawn, when its current
/// submission has `fate` (`None`: not submitted). It submits again only
/// once it saw its submission withdrawn, so at most one submission of the
/// report is ever live (`child_one_live`).
pub(crate) fn report_step<S>(
    withdrawn: u32,
    fate: Option<Fate<S>>,
) -> SessionResult<ReportStep<S>> {
    let mut request = Writer::new();
    request.tag(1);
    let queued = match fate {
        None => {
            request.none();
            None
        }
        Some(Fate::Queued(submission)) => {
            request.some().tag(0);
            Some(submission)
        }
        Some(Fate::Withdrawn) => {
            request.some().tag(1);
            None
        }
        Some(Fate::Placed) => {
            request.some().tag(2);
            None
        }
    };
    request.nat(u64::from(report_ordinal(withdrawn)));
    let next = ask(&mut request, |reply| {
        Ok(match reply.tag_of(4, "a report move")? {
            0 => Move::Submit(reply.nat()?),
            1 => Move::Await,
            2 => Move::Resubmit(reply.nat()?),
            // `tag_of` answers a tag below 4: this is 3.
            _ => Move::Delivered,
        })
    });
    Ok(match next {
        Move::Submit(ordinal) => ReportStep::Submit(report_ordinal(withdrawn_of(ordinal)?)),
        Move::Await => ReportStep::Wait(queued.ok_or_else(|| {
            SessionError::error("the RLM child report move waits on no queued submission")
        })?),
        Move::Resubmit(ordinal) => ReportStep::Again(withdrawn_of(ordinal)?),
        Move::Delivered => ReportStep::Done,
    })
}

/// The report kind of `report` (`Report` in `bend/child.bend`).
fn report_kind(report: &ChildReport) -> u32 {
    match report {
        ChildReport::CompletedWithoutReply { .. } => 0,
        ChildReport::Failed {
            failure: Some(ChildFailure::Stalled),
            ..
        } => 3,
        ChildReport::Failed {
            failure: Some(ChildFailure::Unreachable),
            ..
        } => 4,
        ChildReport::Failed { .. } => 1,
        ChildReport::Cancelled { .. } => 2,
    }
}

/// The task's phase after an abort, as the core answers it (`Ph` in
/// `bend/child.bend`).
enum Phase {
    Watching,
    Owing(Report, u64),
    Ended,
}

/// The report an abort of the task at `checkpoint` hands on (`cut.ph` in
/// `bend/child.bend`, run by the compiled Bend core; `child_abort_rule`):
/// the report phase's, under its request ids, or the cancelled report a
/// delete of the running child `row` owes.
fn owed_on_abort(
    checkpoint: &ChildCheckpoint,
    child: TaskId,
    row: &ChildRow,
) -> SessionResult<Option<OwedReport>> {
    let mut request = Writer::new();
    request.tag(2);
    match checkpoint {
        ChildCheckpoint::Report { report, withdrawn } => {
            request
                .tag(1)
                .tag(report_kind(report))
                .nat(u64::from(report_ordinal(*withdrawn)));
        }
        // The abort reads no clock: the watch phase goes as an empty one.
        ChildCheckpoint::Spawn | ChildCheckpoint::Prompt | ChildCheckpoint::Watch { .. } => {
            request.tag(0).none().nat(0).nat(0);
        }
    }
    // A delete of a child that has not ended owes the cancelled report.
    request.bool(row.delete_requested() && !row.status.is_terminal());
    let phase = ask(&mut request, |reply| {
        Ok(match reply.tag_of(3, "a child task's phase")? {
            0 => {
                // Its clock, which the abort carries unread.
                if reply.maybe()? {
                    reply.nat()?;
                }
                reply.nat()?;
                reply.nat()?;
                Phase::Watching
            }
            1 => Phase::Owing(get_report(reply)?, reply.nat()?),
            // `tag_of` answers a tag below 3: this is 2.
            _ => Phase::Ended,
        })
    });
    let (kind, ordinal) = match phase {
        Phase::Ended => return Ok(None),
        Phase::Owing(kind, ordinal) => (kind, ordinal),
        Phase::Watching => {
            return Err(SessionError::error(
                "the RLM child abort left the task watching",
            ))
        }
    };
    let withdrawn = withdrawn_of(ordinal)?;
    Ok(Some(match (checkpoint, kind) {
        (ChildCheckpoint::Report { report, .. }, _) => OwedReport {
            child: child.get(),
            report: report.clone(),
            withdrawn,
        },
        (
            ChildCheckpoint::Spawn | ChildCheckpoint::Prompt | ChildCheckpoint::Watch { .. },
            Report::Cancelled,
        ) => OwedReport {
            child: child.get(),
            report: ChildReport::Cancelled {
                session_name: row.session_name.clone(),
                reason: Some(DELETED_BY_PARENT.to_owned()),
                handback: row.handback.clone(),
            },
            withdrawn,
        },
        (
            ChildCheckpoint::Spawn | ChildCheckpoint::Prompt | ChildCheckpoint::Watch { .. },
            Report::Completed | Report::Failed | Report::Stalled | Report::Unreachable,
        ) => {
            return Err(SessionError::error(
                "the RLM child abort owes a report other than cancelled",
            ))
        }
    }))
}

/// Define the child task over `services`.
pub(crate) fn child_task(services: &Arc<ChildrenServices>) -> ChildTask {
    let phase = |run: fn(Arc<ChildrenServices>, Running, Runtime, Context) -> PhaseFuture| {
        let services = Arc::clone(services);
        move |task: Running, runtime: Runtime, cx: Context| {
            run(Arc::clone(&services), task, runtime, cx)
        }
    };
    define_task(
        TaskDefinition::new(
            CHILD_TASK_KIND,
            2,
            |input: &ChildTaskInput| {
                Ok(match (&input.owed, input.child) {
                    (Some(owed), _) => owed.checkpoint(),
                    (None, Some(_)) => ChildCheckpoint::Prompt,
                    (None, None) => ChildCheckpoint::Spawn,
                })
            },
            phase(|services, task, runtime, cx| Box::pin(abort(services, task, runtime, cx))),
        )
        // Version 1 stored a report as its text only: the watch derives the
        // report again from the settled child, and the request id keeps a
        // report already submitted from queueing twice.
        .migrate(|input, checkpoint, _version| {
            let checkpoint = match checkpoint.get("phase").and_then(JsonValue::as_str) {
                Some("report") => ChildCheckpoint::Watch {
                    poll: 0,
                    next_poll_at: 0.0,
                    vigil: Vigil::default(),
                },
                Some(_) | None => from_json(checkpoint)?,
            };
            Ok(Migrated {
                input: from_json(input)?,
                checkpoint,
            })
        })
        .phase(
            "spawn",
            phase(|services, task, runtime, cx| Box::pin(spawn(services, task, runtime, cx))),
        )
        .phase(
            "prompt",
            phase(|services, task, runtime, cx| Box::pin(prompt(services, task, runtime, cx))),
        )
        .phase(
            "watch",
            phase(|services, task, runtime, cx| Box::pin(watch(services, task, runtime, cx))),
        )
        .phase(
            "report",
            phase(|services, task, runtime, cx| Box::pin(report(services, task, runtime, cx))),
        ),
    )
}

type PhaseFuture = futures::future::BoxFuture<'static, SessionResult<()>>;

/// The child task whose work `task` serves: its own, or, for a task
/// carrying an aborted child task's report, that task's. Its id names the
/// report's request ids and the host requests' idempotency keys.
fn report_task_id(task: &Running) -> TaskId {
    task.input
        .owed
        .as_ref()
        .map_or_else(|| task.id.erase(), |owed| TaskId::from_number(owed.child))
}

/// The spawn task of the child `task` serves: its registry row is keyed by
/// it and the child's identity derives from it.
fn row_task_id(task: &Running) -> TaskId {
    task.input
        .child
        .map_or_else(|| report_task_id(task), TaskId::from_number)
}

async fn require_row(runtime: &Runtime, task: &Running, cx: &Context) -> SessionResult<ChildRow> {
    let task_id = row_task_id(task);
    let state = read_children(runtime, task.conversation_id, cx).await?;
    state
        .children
        .get(&task_id.to_string())
        .cloned()
        .ok_or_else(|| SessionError::error(format!("RLM child task {task_id} has no registry row")))
}

fn failed(message: String) -> Next {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Failed {
            error: TaskOutcomeError {
                message,
                detail: None,
            },
            result: None,
        },
    }
}

/// `spawn`: create the child session under the task's identity. A failed
/// admission removes the row (no child exists) and fails the task with the
/// host's error, which the `rlm.spawn` caller receives.
async fn spawn(
    services: Arc<ChildrenServices>,
    task: Running,
    runtime: Runtime,
    cx: Context,
) -> SessionResult<()> {
    let row = require_row(&runtime, &task, &cx).await?;
    let task_id = task.id.erase();
    let request = RlmChildSpawnRequest {
        idempotency_key: format!("rlm:{task_id}:spawn"),
        child: child_identity(&services.parent_session_id, task_id),
        name: row.session_name.clone(),
        prompt: task.input.prompt.clone(),
        model: task.input.model.clone(),
        thinking: task.input.thinking.clone(),
        depth: services.rlm_depth + 1,
        max_depth: task.input.max_depth.unwrap_or(services.rlm_max_depth),
        spawned_by_request_id: task.input.spawned_by_request_id.clone(),
        parent_task_id: task_id.to_string(),
        workspace: task.input.workspace.unwrap_or_default(),
        worker: task.input.worker,
    };
    let spawned = services.host.spawn(request).await;
    let conversation_id = task.conversation_id;
    runtime
        .commit(
            move |tx, _current| async move {
                match spawned {
                    Ok(session) => {
                        tx_update_row(&tx, conversation_id, task_id, |row| {
                            row.status = ChildStatus::Running;
                            row.active_session_id = Some(session.active_session_id);
                            row.session_name = session.session_name;
                            row.session_dir = Some(session.session_dir);
                            row.model = Some(session.model);
                        })
                        .await?;
                        Ok(Some(NextTaskState::Running {
                            checkpoint: ChildCheckpoint::Prompt,
                        }))
                    }
                    Err(error) => {
                        tx_remove_row(&tx, conversation_id, task_id).await?;
                        Ok(Some(failed(format!("{error:#}"))))
                    }
                }
            },
            &cx,
        )
        .await
}

/// `prompt`: admit the task prompt (one retry, as the old route did). A
/// prompt that cannot be admitted cancels the child and reports the
/// failure. The prompt goes out while the spawning tool call may still
/// run: a cell that spawns and then waits on the child (`rlm.collect`
/// with a timeout) must see it run.
async fn prompt(
    services: Arc<ChildrenServices>,
    task: Running,
    runtime: Runtime,
    cx: Context,
) -> SessionResult<()> {
    let ChildCheckpoint::Prompt = task.checkpoint else {
        return Err(SessionError::error(
            "RLM child prompt phase without its checkpoint",
        ));
    };
    let task_id = task.id.erase();
    let row_id = row_task_id(&task);
    let identity = child_identity(&services.parent_session_id, row_id);
    let request = RlmChildPromptRequest {
        idempotency_key: format!("rlm:{task_id}:prompt"),
        session_id: identity.session_id.clone(),
        rlm_child_id: identity.rlm_child_id.clone(),
        prompt: task.input.prompt.clone(),
        kind: task.input.kind,
        row_id: match task.input.child {
            None => format!("spawn:{}", identity.rlm_child_id),
            Some(_) => format!("task:{task_id}"),
        },
        details: task.input.details.clone(),
    };
    let prompted = match services.host.prompt(request.clone()).await {
        Ok(()) => Ok(()),
        Err(_) => services.host.prompt(request).await,
    };
    let failure = match prompted {
        Ok(()) => None,
        Err(error) => {
            let cancel = RlmChildCancelRequest {
                idempotency_key: format!("rlm:{task_id}:cancel"),
                session_id: identity.session_id,
            };
            if let Err(cancel_error) = services.host.cancel(cancel).await {
                runtime.report(SessionError::error(format!(
                    "RLM child {task_id} cancel after a failed prompt: {cancel_error:#}"
                )))?;
            }
            Some(format!("{error:#}"))
        }
    };
    let now = runtime.now()?;
    let conversation_id = task.conversation_id;
    let report = task.input.report;
    runtime
        .commit(
            move |tx, _current| async move {
                let Some(error) = failure else {
                    return Ok(Some(NextTaskState::Running {
                        checkpoint: ChildCheckpoint::Watch {
                            poll: 0,
                            next_poll_at: now,
                            vigil: Vigil::default(),
                        },
                    }));
                };
                let row = tx_update_row(&tx, conversation_id, row_id, |row| {
                    row.status = ChildStatus::Error;
                    row.error = Some(error.clone());
                    row.failure = Some(ChildFailure::Undelivered);
                    // A silent child's end goes to its caller through its
                    // row, never to the inbox.
                    row.settled = report == ReportMode::Silent;
                })
                .await?;
                Ok(Some(match report {
                    ReportMode::Inbox => report_next(ChildReport::Failed {
                        session_name: row.session_name,
                        failure: Some(ChildFailure::Undelivered),
                        error,
                        handback: None,
                    }),
                    ReportMode::Silent => NextTaskState::Terminal {
                        outcome: TaskOutcome::Completed {
                            result: ChildStatus::Error,
                        },
                    },
                }))
            },
            &cx,
        )
        .await
}

fn report_next(report: ChildReport) -> Next {
    NextTaskState::Running {
        checkpoint: ChildCheckpoint::Report {
            report,
            withdrawn: 0,
        },
    }
}

/// What one poll of the watch read, with what a report of it needs.
enum Seen {
    /// The child is unsettled (running, or idle with background jobs).
    Unsettled,
    /// The poll got no answer.
    Unreached { error: anyhow::Error },
    /// The child's run failed.
    Failed {
        failure: ChildFailure,
        error: String,
    },
    /// The child's run answered.
    Answered { answer_preview: Option<String> },
}

impl Seen {
    /// The poll as the watch's call reads it; `replied`: the child already
    /// replied to its parent (read for an answer only).
    fn obs(&self, progress: Option<u64>, replied: bool) -> Obs {
        match self {
            Self::Unsettled => Obs::Busy { progress },
            Self::Unreached { .. } => Obs::Lost,
            Self::Failed { .. } => Obs::Broke,
            Self::Answered { .. } => Obs::Answered { replied },
        }
    }
}

/// The report the watch gives up on a child with, or `None`.
fn gives_up(call: &Call) -> Option<Report> {
    match call {
        Call::Reports(report @ (Report::Stalled | Report::Unreachable))
        | Call::Settles(Some(report @ (Report::Stalled | Report::Unreachable))) => Some(*report),
        Call::Watches(_)
        | Call::Reports(Report::Completed | Report::Failed | Report::Cancelled)
        | Call::Settles(None | Some(Report::Completed | Report::Failed | Report::Cancelled)) => {
            None
        }
    }
}

/// The task's next state after the watch's poll `poll`, which ended at
/// `now`, read `seen` and got `call` (`verdict` in `bend/child.bend`):
/// watch on, report, or end; `row` takes the child's end. A child that
/// answered through an agent message, and every child of a silent task,
/// owes no notice.
fn watched_next(
    call: Call,
    seen: Seen,
    poll: u64,
    now: f64,
    row: &mut ChildRow,
    stall: std::time::Duration,
) -> SessionResult<Next> {
    let (why, reports) = match call {
        // Each failed poll in a row doubles the pause.
        Call::Watches(vigil) => {
            return Ok(NextTaskState::Running {
                checkpoint: ChildCheckpoint::Watch {
                    poll: poll + 1,
                    next_poll_at: now
                        + WATCH_POLL_INTERVAL_MS * 2_f64.powf(f64::from(vigil.failures)),
                    vigil,
                },
            })
        }
        Call::Reports(report) => (Some(report), true),
        Call::Settles(why) => (why, false),
    };
    let misfit = |why: Option<Report>| {
        SessionError::error(format!(
            "the RLM child watch's call ({why:?}) does not fit its poll"
        ))
    };
    let report = match seen {
        Seen::Answered { answer_preview } => match why {
            None | Some(Report::Completed) => {
                row.status = ChildStatus::Done;
                row.answer_preview.clone_from(&answer_preview);
                ChildReport::CompletedWithoutReply {
                    session_name: row.session_name.clone(),
                    last_assistant_text_preview: answer_preview,
                    handback: row.handback.clone(),
                }
            }
            Some(Report::Failed | Report::Cancelled | Report::Stalled | Report::Unreachable) => {
                return Err(misfit(why))
            }
        },
        Seen::Failed { failure, error } => match why {
            Some(Report::Failed) => watch_failed(row, failure, error),
            None
            | Some(
                Report::Completed | Report::Cancelled | Report::Stalled | Report::Unreachable,
            ) => return Err(misfit(why)),
        },
        Seen::Unsettled | Seen::Unreached { .. }
            if matches!(why, Some(Report::Stalled)) =>
        {
            watch_failed(
                row,
                ChildFailure::Stalled,
                format!(
                    "RLM child showed no progress for {} s and was stopped",
                    stall.as_secs_f64()
                ),
            )
        }
        Seen::Unreached { error } if matches!(why, Some(Report::Unreachable)) => watch_failed(
            row,
            ChildFailure::Unreachable,
            format!(
                "RLM child could not be reached in {CHILD_POLL_FAILURES} polls in a row and was stopped: {error:#}"
            ),
        ),
        Seen::Unsettled | Seen::Unreached { .. } => return Err(misfit(why)),
    };
    Ok(if reports {
        report_next(report)
    } else {
        row.settled = true;
        NextTaskState::Terminal {
            outcome: TaskOutcome::Completed { result: row.status },
        }
    })
}

/// The row of a child the watch ends as failed with `failure`, and the
/// report of it.
fn watch_failed(row: &mut ChildRow, failure: ChildFailure, error: String) -> ChildReport {
    row.status = ChildStatus::Error;
    row.error = Some(error.clone());
    row.failure = Some(failure);
    ChildReport::Failed {
        session_name: row.session_name.clone(),
        failure: Some(failure),
        error,
        handback: row.handback.clone(),
    }
}

/// `watch`: one long-poll per invocation. Every poll commits progress (the
/// attributed usage, the watch's clock, the next deadline), so a restarted
/// parent resumes the watch where it stopped and never bills a child
/// twice. The clock counts the time of this invocation only: a parent's
/// own downtime is not the child's. The pause before a re-poll is the
/// polling session's: a reopened parent's first poll runs at once.
async fn watch(
    services: Arc<ChildrenServices>,
    task: Running,
    runtime: Runtime,
    cx: Context,
) -> SessionResult<()> {
    let ChildCheckpoint::Watch {
        poll,
        next_poll_at,
        vigil,
    } = task.checkpoint
    else {
        return Err(SessionError::error(
            "RLM child watch phase without its checkpoint",
        ));
    };
    let started = runtime.now()?;
    let task_id = task.id.erase();
    // Only a poll tells a reopened (restarted) parent whether the child's
    // run was interrupted while it was down (H5), so its first poll does
    // not wait out a pause the closed session scheduled: after a poll the
    // daemon's own shutdown failed, that was 4 s (up to 32 s), and the
    // restarted roster read the interrupted child as `running` meanwhile.
    let first_poll = services
        .polled
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .insert(task_id.get());
    if !first_poll {
        runtime.sleep(next_poll_at, &cx).await?;
    }
    let row_id = row_task_id(&task);
    let identity = child_identity(&services.parent_session_id, row_id);
    // The long poll yields to an abort mark or a closing Harness: the
    // invocation is joined before the abort handler runs.
    let signal = runtime.signal();
    let observed = tokio::select! {
        observed = services.host.wait_settled(RlmChildWaitRequest {
            session_id: identity.session_id.clone(),
            rlm_child_id: identity.rlm_child_id.clone(),
            timeout_ms: WATCH_WAIT_SLICE_MS,
        }) => observed,
        reason = signal.cancelled() => return Err(SessionError::Aborted(reason)),
    };
    let now = runtime.now()?;
    // A settled child's return is claimed on the parent's ledger BEFORE
    // the commit that delivers its notice (TS records the return before
    // the notice triggers the parent's next turn): the child's last
    // committed request, read from its ledger in its RLM session dir; a
    // child with no ledger returns nothing (an absent edge beats a wrong
    // one).
    let claim_child_return = {
        let settled = matches!(
            &observed,
            Ok(observation) if matches!(observation.state, RlmChildRunState::Answered { .. })
        );
        let services = Arc::clone(&services);
        let session_id = identity.session_id.clone();
        move |row: &ChildRow| {
            if !settled {
                return;
            }
            let Some(recorder) = services.semantic_edges.as_ref() else {
                return;
            };
            let ledger = row
                .session_dir
                .as_deref()
                .map(|dir| std::path::Path::new(dir).join(SEMANTIC_EDGES_LEDGER_FILENAME));
            recorder.record_child_returned(
                &session_id,
                ledger.as_deref().and_then(last_committed_request_id),
            );
        }
    };
    let stall = services.settings.manager().get_subagent_stall();
    let report = task.input.report;
    let call = move |seen: &Seen, progress, replied| {
        verdict(
            vigil,
            stall.as_secs_f64() * 1000.0,
            (now - started).max(0.0),
            seen.obs(progress, replied),
            report,
        )
    };
    let mut answer = None;
    let (usage, progress, seen) = match observed {
        Ok(RlmChildObservation {
            state,
            usage,
            progress,
            answer: full,
        }) => {
            answer = full;
            let seen = match state {
                RlmChildRunState::Running | RlmChildRunState::Idle { .. } => Seen::Unsettled,
                RlmChildRunState::Answered { answer_preview } => Seen::Answered { answer_preview },
                RlmChildRunState::Failed { failure, error } => Seen::Failed { failure, error },
            };
            (usage, progress, seen)
        }
        Err(error) => (None, None, Seen::Unreached { error }),
    };
    // An answer's call reads whether the child replied to its parent, on
    // the row the commit holds; every other call is made here, before the
    // watch acts on it.
    let called = match &seen {
        Seen::Answered { .. } => None,
        Seen::Unsettled | Seen::Unreached { .. } | Seen::Failed { .. } => {
            Some(call(&seen, progress, false))
        }
    };
    if called.as_ref().and_then(gives_up).is_some() {
        // Abort its run, then stop its agent, so its worker is released.
        // Each may take its full host timeout: an abort mark ends the wait
        // (the abort handler cancels the child itself).
        let request = |verb| RlmChildCancelRequest {
            idempotency_key: format!("rlm:{task_id}:{verb}"),
            session_id: identity.session_id.clone(),
        };
        let (cancelled, stopped) = tokio::select! {
            cancelled = services.host.cancel(request("cancel")) => {
                tokio::select! {
                    stopped = services.host.stop(request("stop")) => (cancelled, stopped),
                    reason = signal.cancelled() => return Err(SessionError::Aborted(reason)),
                }
            }
            reason = signal.cancelled() => return Err(SessionError::Aborted(reason)),
        };
        for (verb, outcome) in [("cancel", cancelled), ("stop", stopped)] {
            if let Err(error) = outcome {
                runtime.report(SessionError::error(format!(
                    "RLM child {task_id} {verb} after the watch gave up on it: {error:#}"
                )))?;
            }
        }
    }
    let handback = match &called {
        Some(Call::Watches(_)) => None,
        Some(Call::Reports(_) | Call::Settles(_)) | None => {
            tokio::select! {
                outcome = hand_back(services.host.as_ref(), &identity.session_id, &identity.rlm_child_id) => outcome,
                reason = signal.cancelled() => return Err(SessionError::Aborted(reason)),
            }
        }
    };
    let conversation_id = task.conversation_id;
    runtime
        .commit(
            move |tx, _current| async move {
                let Some(mut row) = tx_row(&tx, conversation_id, row_id).await? else {
                    return Err(SessionError::error(format!(
                        "RLM child task {task_id} has no registry row"
                    )));
                };
                claim_child_return(&row);
                if let Some(usage) = &usage {
                    tx_attribute_usage(&tx, conversation_id, &mut row, usage).await?;
                }
                row.progress = progress.or(row.progress);
                row.handback = handback;
                if report == ReportMode::Silent && matches!(seen, Seen::Answered { .. }) {
                    row.answer = answer;
                }
                let called = match called {
                    Some(called) => called,
                    None => call(&seen, progress, row.replied_since_task),
                };
                let next = watched_next(called, seen, poll, now, &mut row, stall)?;
                super::registry::tx_put_row(&tx, conversation_id, &row).await?;
                Ok(Some(next))
            },
            &cx,
        )
        .await
}

/// Hand an ended child's workspace back into the parent's; `None` for a
/// child in the shared workspace.
#[tracing::instrument(skip(host))]
async fn hand_back(
    host: &dyn RlmSubagentHost,
    session_id: &str,
    rlm_child_id: &str,
) -> Option<HandbackOutcome> {
    match host
        .hand_back(RlmChildHandbackRequest {
            session_id: session_id.to_owned(),
            rlm_child_id: rlm_child_id.to_owned(),
        })
        .await
    {
        Ok(Some(handback)) => Some(HandbackOutcome::Done { handback }),
        Ok(None) => None,
        Err(error) => Some(HandbackOutcome::Failed {
            error: format!("{error:#}"),
        }),
    }
}

/// The conversation that owns child task `task`.
async fn owner(
    runtime: &Runtime,
    task: &Running,
    cx: &Context,
) -> SessionResult<Arc<dyn ConversationHandle>> {
    runtime
        .conversation(task.conversation_id, cx)
        .await?
        .ok_or_else(|| {
            SessionError::error(format!(
                "RLM child task {} lost its conversation {}",
                task.id, task.conversation_id
            ))
        })
}

/// Submit `report` to the parent as a follow-up under submission
/// `ordinal`. The request id makes a rerun (a crash between the submission
/// and the next commit) return the first submission instead of queueing a
/// second report. A closing parent admits none: its close aborts the run
/// and withdraws the queued inputs first, so a report admitted after that
/// would start a run on the closing session. The report stays owed to the
/// reopened session, and the invocation waits for the close to end it.
async fn submit_report(
    services: &ChildrenServices,
    runtime: &Runtime,
    task: &Running,
    report: &ChildReport,
    ordinal: u32,
    cx: &Context,
) -> SessionResult<Arc<dyn Submission>> {
    let conversation = owner(runtime, task, cx).await?;
    let draft = InputSubmissionDraft {
        request_id: Some(report_request_id(report_task_id(task), ordinal)),
        content: UserContent::Text(report.text()),
        when_busy: Some(WhenBusy::FollowUp),
        origin: report.origin(),
        entry: None,
    };
    match services
        .closing
        .admit(|| conversation.submit(draft, cx))
        .await
    {
        Some(submitted) => submitted,
        None => Err(SessionError::Aborted(runtime.signal().cancelled().await)),
    }
}

/// `report`: deliver the owed report, then end the task. The child is
/// settled once its report is admitted, but the report stays owed until
/// it reaches the parent's transcript: a queued input the parent's inbox
/// withdraws (a conversation abort) settles unanswered without an entry,
/// and the report is submitted again under the next request id once the
/// aborted run is over (an input queued behind a run that ends by abort
/// waits for the next run). When the abort is a close's (a daemon
/// shutdown, a session switch), the closing parent admits no submission
/// and the reopened session delivers the report.
async fn report(
    services: Arc<ChildrenServices>,
    task: Running,
    runtime: Runtime,
    cx: Context,
) -> SessionResult<()> {
    let ChildCheckpoint::Report { report, withdrawn } = &task.checkpoint else {
        return Err(SessionError::error(
            "RLM child report phase without its checkpoint",
        ));
    };
    let (report, withdrawn) = (report.clone(), *withdrawn);
    let (conversation_id, task_id) = (task.conversation_id, row_task_id(&task));
    // The waits yield to an abort mark or a closing Harness; a rerun finds
    // the same submission by its request id.
    let signal = runtime.signal();
    let mut fate: Option<Fate<Arc<dyn Submission>>> = None;
    let again = loop {
        fate = Some(match report_step(withdrawn, fate)? {
            ReportStep::Submit(ordinal) => {
                if withdrawn > 0 {
                    let conversation = owner(&runtime, &task, &cx).await?;
                    tokio::select! {
                        idle = conversation.wait_for_idle(&cx) => idle?,
                        reason = signal.cancelled() => return Err(SessionError::Aborted(reason)),
                    }
                }
                let submission =
                    submit_report(&services, &runtime, &task, &report, ordinal, &cx).await?;
                runtime
                    .commit(
                        move |tx, _current| async move {
                            tx_update_row(&tx, conversation_id, task_id, |row| row.settled = true)
                                .await?;
                            Ok(None)
                        },
                        &cx,
                    )
                    .await?;
                Fate::Queued(submission)
            }
            ReportStep::Wait(submission) => {
                let settled = tokio::select! {
                    settled = submission.wait(&cx) => settled?,
                    reason = signal.cancelled() => return Err(SessionError::Aborted(reason)),
                };
                Fate::of(&settled.state, submission)
            }
            ReportStep::Again(withdrawn) => break Some(withdrawn),
            ReportStep::Done => break None,
        });
    };
    runtime
        .commit(
            move |tx, _current| async move {
                if let Some(withdrawn) = again {
                    return Ok(Some(NextTaskState::Running {
                        checkpoint: ChildCheckpoint::Report { report, withdrawn },
                    }));
                }
                let row = tx_row(&tx, conversation_id, task_id)
                    .await?
                    .ok_or_else(|| {
                        SessionError::error(format!("RLM child task {task_id} has no registry row"))
                    })?;
                Ok(Some(NextTaskState::Terminal {
                    outcome: TaskOutcome::Completed { result: row.status },
                }))
            },
            &cx,
        )
        .await
}

/// Abort: a delete (the row's `deletion`) owes the cancelled notice;
/// a plain cancel suppresses the no-reply notice (TS
/// `run.suppressTerminalNotice`). A child whose prompt may have been
/// admitted is cancelled at the host; a delete tears it down itself.
///
/// An owed report (the report phase's, or a delete's) is handed to a new
/// task that starts in the report phase under the same request ids: the
/// one report rule (submit, wait for placement, submit again under the
/// next id after each withdrawal) then delivers it, also when the abort
/// that reached this task withdrew it. The abort that reached this task
/// does not reach the new one (`bend/child.bend`, `cut.ph`).
async fn abort(
    services: Arc<ChildrenServices>,
    task: Running,
    runtime: Runtime,
    cx: Context,
) -> SessionResult<()> {
    let mut row = require_row(&runtime, &task, &cx).await?;
    let task_id = report_task_id(&task);
    let row_id = row_task_id(&task);
    let running = !row.status.is_terminal();
    let prompt_admissible = !matches!(task.checkpoint, ChildCheckpoint::Spawn);
    if running && prompt_admissible && !row.delete_requested() {
        let cancel = RlmChildCancelRequest {
            idempotency_key: format!("rlm:{task_id}:cancel"),
            session_id: row.session_id.clone(),
        };
        if let Err(error) = services.host.cancel(cancel).await {
            runtime.report(SessionError::error(format!(
                "RLM child {task_id} cancel: {error:#}"
            )))?;
        }
    }
    // A spawned child not handed back yet (the watch hands back an ended
    // one) hands its workspace back now, after its run was cancelled.
    let handback = if prompt_admissible && row.handback.is_none() {
        hand_back(services.host.as_ref(), &row.session_id, &row.rlm_child_id).await
    } else {
        None
    };
    if let Some(outcome) = &handback {
        row.handback = Some(outcome.clone());
    }
    let owed = match task.input.report {
        ReportMode::Inbox => owed_on_abort(&task.checkpoint, task_id, &row)?,
        ReportMode::Silent => None,
    };
    let reporter = match owed {
        Some(owed) => {
            let definition = runtime
                .registry()
                .task(CHILD_TASK_KIND)
                .map(AnyTask::as_definition_ref)
                .ok_or_else(|| SessionError::error(format!("{CHILD_TASK_KIND} is not defined")))?;
            let input = to_json(&ChildTaskInput {
                owed: Some(owed),
                ..task.input.clone()
            })?;
            Some((definition, input))
        }
        None => None,
    };
    let reason = if row.delete_requested() {
        DELETED_BY_PARENT
    } else {
        CANCELLED_BY_USER
    };
    let conversation_id = task.conversation_id;
    runtime
        .commit(
            move |tx, _current| async move {
                let reporter = match reporter {
                    Some((definition, input)) => Some(
                        tx.create_task(
                            definition,
                            input,
                            TaskOptions {
                                ownership: TaskOwnership::Conversation,
                                conversation_id: Some(conversation_id),
                                background: Some(true),
                                abandon_on_restart: None,
                            },
                        )
                        .await?,
                    ),
                    None => None,
                };
                let row = tx_update_row(&tx, conversation_id, row_id, |row| {
                    if !row.status.is_terminal() {
                        row.status = ChildStatus::Cancelled;
                        row.error = Some(reason.to_owned());
                    }
                    if let Some(outcome) = &handback {
                        row.handback = Some(outcome.clone());
                    }
                    match reporter {
                        // The new task settles the row once it admits the
                        // report.
                        Some(reporter) => {
                            row.reporter = Some(reporter.get());
                            row.settled = false;
                        }
                        None => row.settled = true,
                    }
                })
                .await?;
                Ok(Some(NextTaskState::Terminal {
                    outcome: TaskOutcome::Aborted {
                        reason: Some(reason.to_owned()),
                        result: Some(row.status),
                    },
                }))
            },
            &cx,
        )
        .await
}
