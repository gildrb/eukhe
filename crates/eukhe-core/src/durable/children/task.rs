//! The `eukhe.rlm.child` durable task: one per spawned child, background and
//! owned by the spawning conversation, so a child's lifecycle survives a
//! parent restart (the old daemon settle watcher died with the worker).
//!
//! Phases: `spawn` (host create under the identity derived from the task
//! id), `prompt` (after the spawning tool call settled), `watch` (host
//! long-poll; a durable deadline between polls; child usage attributed per
//! poll), `report` (a follow-up input to the parent with a request id, so a
//! rerun cannot report twice), then terminal. Abort cancels the child's run
//! and delivers the report a delete owes.

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::tasks::{
    define_task, NextTaskState, RunningTask, Task, TaskDefinition, TaskRuntime,
};
use eukhe_durable::types::{JoinPolicy, TaskId, TaskOutcome, TaskOutcomeError};
use eukhe_types::pi_ai::UserContent;
use serde::{Deserialize, Serialize};

use super::host::{
    RlmChildCancelRequest, RlmChildPromptRequest, RlmChildRunState, RlmChildSpawnRequest,
    RlmChildWaitRequest, RlmSubagentHost,
};
use super::notice::{ChildReport, DELETED_BY_PARENT};
use super::registry::{
    child_identity, read_children, tx_attribute_usage, tx_remove_row, tx_row, tx_update_row,
    ChildRow, ChildStatus,
};
use crate::durable::observe::semantic_edges::{
    last_committed_request_id, SemanticEdgeRecorder, SEMANTIC_EDGES_LEDGER_FILENAME,
};

/// The task kind.
pub(crate) const CHILD_TASK_KIND: &str = "eukhe.rlm.child";
/// One long-poll slice of the settle watch.
pub(crate) const WATCH_WAIT_SLICE_MS: u64 = 60_000;
/// Re-poll cadence after a slice ends without a settled child.
pub(crate) const WATCH_POLL_INTERVAL_MS: f64 = 2_000.0;
/// Consecutive failed polls before an unreachable child settles as errored.
pub(crate) const WATCH_MAX_UNREACHABLE_POLLS: u32 = 150;
/// The error text of a child that stayed unreachable.
const UNREACHABLE_ERROR: &str = "Child worker unreachable";
/// The error text of a run the user cancelled (no notice is owed).
const CANCELLED_BY_USER: &str = "Cancelled by user";
/// Ordinal of the report a child task delivers (its only one).
const REPORT_ORDINAL: u32 = 1;

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
    /// The `pi.tool` task that spawned the child: its prompt waits for that
    /// call to settle, so the parent's continuation request goes first.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) spawning_tool_task: Option<u64>,
    /// The depth bound in force at the spawn (a runtime override or the
    /// configured bound); `None` on tasks admitted before it was recorded.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) max_depth: Option<u32>,
}

/// Checkpoint of one child task.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
pub(crate) enum ChildCheckpoint {
    Spawn,
    #[serde(rename_all = "camelCase")]
    Prompt {
        waited: bool,
    },
    #[serde(rename_all = "camelCase")]
    Watch {
        poll: u64,
        /// Harness clock before which the next poll does not start.
        next_poll_at: f64,
        unreachable_polls: u32,
    },
    Report {
        text: String,
    },
}

/// The task definition: `Task<input, checkpoint, final status, no hooks>`.
pub(crate) type ChildTask = Task<ChildTaskInput, ChildCheckpoint, ChildStatus, ()>;
type Runtime = TaskRuntime<ChildTaskInput, ChildCheckpoint, ChildStatus, ()>;
type Running = RunningTask<ChildTaskInput, ChildCheckpoint, ChildStatus>;
type Next = NextTaskState<ChildCheckpoint, ChildStatus>;

/// The follow-up request id of the report of child task `task_id`.
pub(crate) fn report_request_id(task_id: TaskId) -> String {
    format!("rlm:{task_id}:report:{REPORT_ORDINAL}")
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
            1,
            |_: &ChildTaskInput| Ok(ChildCheckpoint::Spawn),
            phase(|services, task, runtime, cx| Box::pin(abort(services, task, runtime, cx))),
        )
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
            phase(|_services, task, runtime, cx| Box::pin(report(task, runtime, cx))),
        ),
    )
}

type PhaseFuture = futures::future::BoxFuture<'static, SessionResult<()>>;

async fn require_row(runtime: &Runtime, task: &Running, cx: &Context) -> SessionResult<ChildRow> {
    let state = read_children(runtime, task.conversation_id, cx).await?;
    state
        .children
        .get(&task.id.to_string())
        .cloned()
        .ok_or_else(|| {
            SessionError::error(format!("RLM child task {} has no registry row", task.id))
        })
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
                            checkpoint: ChildCheckpoint::Prompt { waited: false },
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

/// `prompt`: wait for the spawning tool call to settle, then admit the task
/// prompt (one retry, as the old route did). A prompt that cannot be
/// admitted cancels the child and reports the failure.
async fn prompt(
    services: Arc<ChildrenServices>,
    task: Running,
    runtime: Runtime,
    cx: Context,
) -> SessionResult<()> {
    let ChildCheckpoint::Prompt { waited } = task.checkpoint else {
        return Err(SessionError::error(
            "RLM child prompt phase without its checkpoint",
        ));
    };
    if let (false, Some(tool_task)) = (waited, task.input.spawning_tool_task) {
        return runtime
            .commit(
                move |_tx, _current| async move {
                    Ok(Some(NextTaskState::Waiting {
                        checkpoint: ChildCheckpoint::Prompt { waited: true },
                        on: vec![TaskId::from_number(tool_task)],
                        policy: JoinPolicy::AllSettled,
                    }))
                },
                &cx,
            )
            .await;
    }
    let task_id = task.id.erase();
    let identity = child_identity(&services.parent_session_id, task_id);
    let request = RlmChildPromptRequest {
        idempotency_key: format!("rlm:{task_id}:prompt"),
        session_id: identity.session_id.clone(),
        prompt: task.input.prompt.clone(),
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
    runtime
        .commit(
            move |tx, _current| async move {
                let Some(error) = failure else {
                    return Ok(Some(NextTaskState::Running {
                        checkpoint: ChildCheckpoint::Watch {
                            poll: 0,
                            next_poll_at: now,
                            unreachable_polls: 0,
                        },
                    }));
                };
                let row = tx_update_row(&tx, conversation_id, task_id, |row| {
                    row.status = ChildStatus::Error;
                    row.error = Some(error.clone());
                })
                .await?;
                Ok(Some(report_next(&ChildReport::Failed {
                    session_name: row.session_name,
                    error,
                })))
            },
            &cx,
        )
        .await
}

fn report_next(report: &ChildReport) -> Next {
    NextTaskState::Running {
        checkpoint: ChildCheckpoint::Report {
            text: report.text(),
        },
    }
}

/// `watch`: one long-poll per invocation. Every poll commits progress (the
/// attributed usage, the next deadline), so a restarted parent resumes the
/// watch where it stopped and never bills a child twice.
async fn watch(
    services: Arc<ChildrenServices>,
    task: Running,
    runtime: Runtime,
    cx: Context,
) -> SessionResult<()> {
    let ChildCheckpoint::Watch {
        poll,
        next_poll_at,
        unreachable_polls,
    } = task.checkpoint
    else {
        return Err(SessionError::error(
            "RLM child watch phase without its checkpoint",
        ));
    };
    runtime.sleep(next_poll_at, &cx).await?;
    let task_id = task.id.erase();
    let identity = child_identity(&services.parent_session_id, task_id);
    // The long poll yields to an abort mark or a closing Harness: the
    // invocation is joined before the abort handler runs.
    let signal = runtime.signal();
    let observed = tokio::select! {
        observed = services.host.wait_settled(RlmChildWaitRequest {
            session_id: identity.session_id.clone(),
            timeout_ms: WATCH_WAIT_SLICE_MS,
        }) => observed,
        reason = signal.cancelled() => return Err(SessionError::Aborted(reason)),
    };
    let next_poll_at = runtime.now()? + WATCH_POLL_INTERVAL_MS;
    // A settled child's return is claimed on the parent's ledger BEFORE
    // the commit that delivers its notice (TS records the return before
    // the notice triggers the parent's next turn): the child's last
    // committed request, read from its ledger beside its storage; a child
    // with no ledger returns nothing (an absent edge beats a wrong one).
    let claim_child_return = {
        let settled = matches!(
            &observed,
            Ok(observation) if matches!(observation.state, RlmChildRunState::Settled { .. })
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
                .map(std::path::Path::new)
                .map(|dir| {
                    dir.join(row.session_id.as_str())
                        .join(SEMANTIC_EDGES_LEDGER_FILENAME)
                });
            recorder.record_child_returned(
                &session_id,
                ledger.as_deref().and_then(last_committed_request_id),
            );
        }
    };
    let conversation_id = task.conversation_id;
    runtime
        .commit(
            move |tx, _current| async move {
                let Some(mut row) = tx_row(&tx, conversation_id, task_id).await? else {
                    return Err(SessionError::error(format!(
                        "RLM child task {task_id} has no registry row"
                    )));
                };
                claim_child_return(&row);
                let next = match observed {
                    Ok(observation) => {
                        if let Some(usage) = &observation.usage {
                            tx_attribute_usage(&tx, conversation_id, &mut row, usage).await?;
                        }
                        settle_next(&mut row, observation.state, poll, next_poll_at)
                    }
                    Err(_) if unreachable_polls + 1 >= WATCH_MAX_UNREACHABLE_POLLS => {
                        row.status = ChildStatus::Error;
                        row.error = Some(UNREACHABLE_ERROR.to_owned());
                        report_next(&ChildReport::Failed {
                            session_name: row.session_name.clone(),
                            error: UNREACHABLE_ERROR.to_owned(),
                        })
                    }
                    Err(_) => NextTaskState::Running {
                        checkpoint: ChildCheckpoint::Watch {
                            poll: poll + 1,
                            next_poll_at,
                            unreachable_polls: unreachable_polls + 1,
                        },
                    },
                };
                super::registry::tx_put_row(&tx, conversation_id, &row).await?;
                Ok(Some(next))
            },
            &cx,
        )
        .await
}

/// The step after one successful poll; settles `row` when the run ended.
fn settle_next(row: &mut ChildRow, state: RlmChildRunState, poll: u64, next_poll_at: f64) -> Next {
    match state {
        RlmChildRunState::Running => NextTaskState::Running {
            checkpoint: ChildCheckpoint::Watch {
                poll: poll + 1,
                next_poll_at,
                unreachable_polls: 0,
            },
        },
        RlmChildRunState::Settled {
            answer_preview,
            replied_since_task,
        } => {
            row.status = ChildStatus::Done;
            row.answer_preview.clone_from(&answer_preview);
            row.replied_since_task = replied_since_task;
            if replied_since_task {
                // The child answered through an agent message: no notice.
                row.settled = true;
                return NextTaskState::Terminal {
                    outcome: TaskOutcome::Completed {
                        result: ChildStatus::Done,
                    },
                };
            }
            report_next(&ChildReport::CompletedWithoutReply {
                session_name: row.session_name.clone(),
                last_assistant_text_preview: answer_preview,
            })
        }
        RlmChildRunState::Failed { error } => {
            row.status = ChildStatus::Error;
            row.error = Some(error.clone());
            report_next(&ChildReport::Failed {
                session_name: row.session_name.clone(),
                error,
            })
        }
    }
}

/// Submit `text` to the parent as a follow-up. The request id makes a rerun
/// (a crash between the submission and the terminal commit) return the
/// first submission instead of queueing a second report.
async fn submit_report(
    runtime: &Runtime,
    task: &Running,
    text: String,
    cx: &Context,
) -> SessionResult<()> {
    let conversation = runtime
        .conversation(task.conversation_id, cx)
        .await?
        .ok_or_else(|| {
            SessionError::error(format!(
                "RLM child task {} lost its conversation {}",
                task.id, task.conversation_id
            ))
        })?;
    conversation
        .submit(
            InputSubmissionDraft {
                request_id: Some(report_request_id(task.id.erase())),
                content: UserContent::Text(text),
                when_busy: Some(WhenBusy::FollowUp),
            },
            cx,
        )
        .await?;
    Ok(())
}

/// `report`: deliver the owed report, then end the task.
async fn report(task: Running, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let ChildCheckpoint::Report { text } = task.checkpoint.clone() else {
        return Err(SessionError::error(
            "RLM child report phase without its checkpoint",
        ));
    };
    submit_report(&runtime, &task, text, &cx).await?;
    let (conversation_id, task_id) = (task.conversation_id, task.id.erase());
    runtime
        .commit(
            move |tx, _current| async move {
                let row =
                    tx_update_row(&tx, conversation_id, task_id, |row| row.settled = true).await?;
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
/// `run.suppressTerminalNotice`). A report the run already owed is still
/// delivered. A child whose prompt may have been admitted is cancelled at
/// the host; a delete tears it down itself.
async fn abort(
    services: Arc<ChildrenServices>,
    task: Running,
    runtime: Runtime,
    cx: Context,
) -> SessionResult<()> {
    let row = require_row(&runtime, &task, &cx).await?;
    let task_id = task.id.erase();
    let running = !row.status.is_terminal();
    let owed = match &task.checkpoint {
        ChildCheckpoint::Report { text } => Some(text.clone()),
        ChildCheckpoint::Spawn | ChildCheckpoint::Prompt { .. } | ChildCheckpoint::Watch { .. } => {
            (row.delete_requested() && running).then(|| {
                ChildReport::Cancelled {
                    session_name: row.session_name.clone(),
                    reason: Some(DELETED_BY_PARENT.to_owned()),
                }
                .text()
            })
        }
    };
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
    if let Some(text) = owed {
        submit_report(&runtime, &task, text, &cx).await?;
    }
    let reason = if row.delete_requested() {
        DELETED_BY_PARENT
    } else {
        CANCELLED_BY_USER
    };
    let conversation_id = task.conversation_id;
    runtime
        .commit(
            move |tx, _current| async move {
                let row = tx_update_row(&tx, conversation_id, task_id, |row| {
                    if !row.status.is_terminal() {
                        row.status = ChildStatus::Cancelled;
                        row.error = Some(reason.to_owned());
                    }
                    row.settled = true;
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
