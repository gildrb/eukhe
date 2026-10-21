//! The `eukhe.workflow.run` durable task: one per run, background and
//! owned by the conversation that called `workflow`, so the run outlives
//! the tool call (the call returns at once) and resumes after a restart.
//!
//! Phases: `run` (the script on the code mode sandbox; a restart replays
//! its journal), `report` (a follow-up input to the conversation with a
//! request id, so a rerun cannot report twice, held until it reaches the
//! transcript and submitted again under the next id when the inbox
//! withdraws it: the children's report rule, [`report_step`]), then
//! terminal. A close of the Harness stops the `run` phase without an
//! outcome, and the reopened session runs it again. An abort of the task
//! (`/workflows` cancel) cancels the run's agents, marks the run
//! cancelled, and hands the cancelled report to a new task that starts in
//! the `report` phase, which the abort does not reach.

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_chord::json::to_json;
use eukhe_durable::codemode::{run_codemode_task, CodemodeToolOptions};
use eukhe_durable::harness::types::{
    ConversationHandle, InputSubmissionDraft, Submission, ToolExecutionResult, WhenBusy,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::tasks::{
    define_task, AnyTask, NextTaskState, RunningTask, Task, TaskDefinition, TaskRuntime,
};
use eukhe_durable::types::{TaskId, TaskOptions, TaskOutcome, TaskOwnership};
use eukhe_types::input_origin::{InputOrigin, Report};
use eukhe_types::job::{CellStatus, JobId};
use eukhe_types::pi_ai::{UserContent, UserContentBlock};
use eukhe_types::workflow::WorkflowRunState;
use serde::{Deserialize, Serialize};

use super::cancel_agents;
use super::run_doc::{tx_put_run, tx_run, RunRecord};
use crate::durable::children::{report_step, Fate, ReportStep};
use crate::durable::deps::{HarnessCell, SessionClosing};

/// The task kind.
pub(crate) const RUN_TASK_KIND: &str = "eukhe.workflow.run";
/// The reason of a run the user cancelled.
const CANCELLED_BY_USER: &str = "Cancelled by user";

/// What the run task's phases need from the session.
pub(crate) struct RunServices {
    /// The sandbox and the `wf.*` globals.
    pub(crate) options: Arc<CodemodeToolOptions>,
    /// The session's Harness: the cancel of a run's agents.
    pub(crate) harness: HarnessCell,
    /// The session's closing gate: a closing conversation admits no report.
    pub(crate) closing: SessionClosing,
}

/// Input of one run task.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase")]
pub(crate) enum RunTaskInput {
    /// Run the script: `code` is the source the sandbox runs.
    Run { code: String },
    /// Deliver the report an aborted run task owed.
    Report { owed: OwedReport },
}

/// A report an aborted run task hands on.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct OwedReport {
    /// The run task the report is of: its record and the report's request
    /// ids are that task's.
    pub(crate) run: u64,
    pub(crate) report: RunReport,
    /// Submissions the conversation withdrew so far.
    pub(crate) withdrawn: u32,
}

/// The report of an ended run.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct RunReport {
    /// How the run ended, as the report header says it.
    pub(crate) status: CellStatus,
    /// The report body: the run's header line, then the script's output.
    pub(crate) body: String,
}

impl RunReport {
    /// The report of run `run_id`, whose record is `record`, with the
    /// script's `output`.
    fn ended(run_id: &str, record: &RunRecord, output: &str) -> Self {
        // A run reports only once it ended; a running state cannot reach
        // here and reports as an error.
        let (status, word) = match &record.state {
            WorkflowRunState::Done => (CellStatus::Ok, "done"),
            WorkflowRunState::Failed { .. } => (CellStatus::Error, "failed"),
            WorkflowRunState::Cancelled => (CellStatus::Aborted, "cancelled"),
            WorkflowRunState::Running => (CellStatus::Error, "running"),
        };
        let header = format!("workflow run {run_id} ({}): {word}", record.meta.name);
        let body = if output.is_empty() {
            header
        } else {
            format!("{header}\n{output}")
        };
        Self { status, body }
    }
}

/// Checkpoint of one run task.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
pub(crate) enum RunCheckpoint {
    Run,
    Report {
        report: RunReport,
        /// Submissions of the report the conversation's inbox withdrew
        /// before placing them; the next one takes the next request id.
        withdrawn: u32,
    },
}

/// The task definition: `Task<input, checkpoint, final run state, no hooks>`.
pub(crate) type RunTask = Task<RunTaskInput, RunCheckpoint, WorkflowRunState, ()>;
type Runtime = TaskRuntime<RunTaskInput, RunCheckpoint, WorkflowRunState, ()>;
type Running = RunningTask<RunTaskInput, RunCheckpoint, WorkflowRunState>;
type PhaseFuture = futures::future::BoxFuture<'static, SessionResult<()>>;

/// The job id the report of run `run` carries (`workflow-<run>`).
///
/// # Errors
///
/// None in practice: a task id holds only digits.
pub(crate) fn report_job(run: u64) -> SessionResult<JobId> {
    JobId::new(format!("workflow-{run}")).map_err(|error| SessionError::error(error.to_string()))
}

/// The follow-up request id of submission `ordinal` of the report of run
/// `run`.
pub(crate) fn report_request_id(run: u64, ordinal: u32) -> String {
    format!("workflow:{run}:report:{ordinal}")
}

/// Define the run task over `services`.
pub(crate) fn run_task(services: &Arc<RunServices>) -> RunTask {
    let phase = |handler: fn(Arc<RunServices>, Running, Runtime, Context) -> PhaseFuture| {
        let services = Arc::clone(services);
        move |task: Running, runtime: Runtime, cx: Context| {
            handler(Arc::clone(&services), task, runtime, cx)
        }
    };
    define_task(
        TaskDefinition::new(
            RUN_TASK_KIND,
            1,
            |input: &RunTaskInput| {
                Ok(match input {
                    RunTaskInput::Run { .. } => RunCheckpoint::Run,
                    RunTaskInput::Report { owed } => RunCheckpoint::Report {
                        report: owed.report.clone(),
                        withdrawn: owed.withdrawn,
                    },
                })
            },
            phase(|services, task, runtime, cx| Box::pin(abort(services, task, runtime, cx))),
        )
        .phase(
            "run",
            phase(|services, task, runtime, cx| Box::pin(run(services, task, runtime, cx))),
        )
        .phase(
            "report",
            phase(|services, task, runtime, cx| Box::pin(report(services, task, runtime, cx))),
        ),
    )
}

/// The run whose record and report `task` serves: its own, or, for a task
/// that carries an aborted run task's report, that task's.
fn run_of(task: &Running) -> u64 {
    match &task.input {
        RunTaskInput::Run { .. } => task.id.get(),
        RunTaskInput::Report { owed } => owed.run,
    }
}

fn no_record(run_id: &str) -> SessionError {
    SessionError::error(format!("workflow run {run_id} has no record"))
}

/// The text of `result`'s output blocks.
fn output_text(result: &ToolExecutionResult) -> String {
    result
        .output
        .iter()
        .flatten()
        .filter_map(|block| match block {
            UserContentBlock::Text(text) => Some(text.text.as_str()),
            UserContentBlock::Image(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// `run`: run the script to its end, then commit the run's end and move
/// to `report`. A run that did not end done cancels its live agents. An
/// abort or a close of the Harness stops the script and commits nothing:
/// the abort handler or the reopened session takes over.
async fn run(
    services: Arc<RunServices>,
    task: Running,
    runtime: Runtime,
    cx: Context,
) -> SessionResult<()> {
    let code = match (&task.input, &task.checkpoint) {
        (RunTaskInput::Run { code }, RunCheckpoint::Run) => code.clone(),
        (RunTaskInput::Report { .. }, RunCheckpoint::Run | RunCheckpoint::Report { .. })
        | (RunTaskInput::Run { .. }, RunCheckpoint::Report { .. }) => {
            return Err(SessionError::error("workflow run phase without its script"));
        }
    };
    let (conversation_id, run_id) = (task.conversation_id, task.id.to_string());
    let outcome = run_codemode_task(
        Arc::clone(&services.options),
        Arc::clone(runtime.backend()),
        cx.clone(),
        &code,
    )
    .await;
    if let Some(reason) = runtime.signal().reason() {
        return Err(SessionError::Aborted(reason));
    }
    let (state, output) = match outcome {
        Err(error) => {
            let message = error.to_string();
            (
                WorkflowRunState::Failed {
                    error: message.clone(),
                },
                message,
            )
        }
        Ok(result) => {
            let text = output_text(&result);
            match result.is_error {
                Some(true) => (
                    WorkflowRunState::Failed {
                        error: text.clone(),
                    },
                    text,
                ),
                Some(false) | None => (WorkflowRunState::Done, text),
            }
        }
    };
    if state != WorkflowRunState::Done {
        let harness = services.harness.require()?;
        cancel_agents(&harness, conversation_id, &run_id, &cx)
            .await
            .map_err(|error| SessionError::error(format!("{error:#}")))?;
    }
    runtime
        .commit(
            move |tx, _current| async move {
                let mut record = tx_run(&tx, conversation_id, &run_id)
                    .await?
                    .ok_or_else(|| no_record(&run_id))?;
                if !record.state.is_terminal() {
                    record.state = state;
                }
                if record.state != WorkflowRunState::Done {
                    record.cancel_live_agents();
                }
                tx_put_run(&tx, conversation_id, &run_id, &mut record).await?;
                Ok(Some(NextTaskState::Running {
                    checkpoint: RunCheckpoint::Report {
                        report: RunReport::ended(&run_id, &record, &output),
                        withdrawn: 0,
                    },
                }))
            },
            &cx,
        )
        .await
}

/// The conversation that owns run task `task`.
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
                "workflow run task {} lost its conversation {}",
                task.id, task.conversation_id
            ))
        })
}

/// Submit `report` of run `run` to the conversation as a follow-up under
/// submission `ordinal`. The request id makes a rerun return the first
/// submission instead of queueing a second report. A closing conversation
/// admits none: the report stays owed to the reopened session, and the
/// invocation waits for the close to end it.
async fn submit_report(
    services: &RunServices,
    runtime: &Runtime,
    task: &Running,
    report: &RunReport,
    ordinal: u32,
    cx: &Context,
) -> SessionResult<Arc<dyn Submission>> {
    let run = run_of(task);
    let header = Report::JobSettled {
        job: report_job(run)?,
        status: report.status,
    };
    let conversation = owner(runtime, task, cx).await?;
    let draft = InputSubmissionDraft {
        request_id: Some(report_request_id(run, ordinal)),
        content: UserContent::Text(header.render(&report.body)),
        when_busy: Some(WhenBusy::FollowUp),
        origin: InputOrigin::Report { report: header },
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

/// `report`: deliver the run's report, then end the task. The run is
/// settled once its report is admitted; the report stays owed until it
/// reaches the transcript (the children's rule, `report` in
/// `children/task.rs`).
async fn report(
    services: Arc<RunServices>,
    task: Running,
    runtime: Runtime,
    cx: Context,
) -> SessionResult<()> {
    let (report, withdrawn) = match &task.checkpoint {
        RunCheckpoint::Report { report, withdrawn } => (report.clone(), *withdrawn),
        RunCheckpoint::Run => {
            return Err(SessionError::error(
                "workflow report phase without its checkpoint",
            ));
        }
    };
    let (conversation_id, run_id) = (task.conversation_id, run_of(&task).to_string());
    let signal = runtime.signal();
    let mut fate: Option<Fate<Arc<dyn Submission>>> = None;
    let again = loop {
        fate = Some(match report_step(withdrawn, fate) {
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
                let run_id = run_id.clone();
                runtime
                    .commit(
                        move |tx, _current| async move {
                            let mut record = tx_run(&tx, conversation_id, &run_id)
                                .await?
                                .ok_or_else(|| no_record(&run_id))?;
                            record.settled = true;
                            tx_put_run(&tx, conversation_id, &run_id, &mut record).await?;
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
                        checkpoint: RunCheckpoint::Report { report, withdrawn },
                    }));
                }
                let record = tx_run(&tx, conversation_id, &run_id)
                    .await?
                    .ok_or_else(|| no_record(&run_id))?;
                Ok(Some(NextTaskState::Terminal {
                    outcome: TaskOutcome::Completed {
                        result: record.state,
                    },
                }))
            },
            &cx,
        )
        .await
}

/// Abort (`/workflows` cancel): cancel the run's live agents, mark the run
/// and its live agents cancelled, and hand the report on to a new task
/// that starts in the `report` phase under the same request ids: the
/// cancelled report, or the report the `report` phase owed. The abort
/// that reached this task does not reach the new one.
async fn abort(
    services: Arc<RunServices>,
    task: Running,
    runtime: Runtime,
    cx: Context,
) -> SessionResult<()> {
    let (conversation_id, run) = (task.conversation_id, run_of(&task));
    let run_id = run.to_string();
    let carried = match &task.checkpoint {
        RunCheckpoint::Run => {
            let harness = services.harness.require()?;
            cancel_agents(&harness, conversation_id, &run_id, &cx)
                .await
                .map_err(|error| SessionError::error(format!("{error:#}")))?;
            None
        }
        RunCheckpoint::Report { report, withdrawn } => Some((report.clone(), *withdrawn)),
    };
    let definition = runtime
        .registry()
        .task(RUN_TASK_KIND)
        .map(AnyTask::as_definition_ref)
        .ok_or_else(|| SessionError::error(format!("{RUN_TASK_KIND} is not defined")))?;
    runtime
        .commit(
            move |tx, _current| async move {
                let mut record = tx_run(&tx, conversation_id, &run_id)
                    .await?
                    .ok_or_else(|| no_record(&run_id))?;
                if !record.state.is_terminal() {
                    record.state = WorkflowRunState::Cancelled;
                }
                if record.state != WorkflowRunState::Done {
                    record.cancel_live_agents();
                }
                let (report, withdrawn) = match carried {
                    Some(carried) => carried,
                    None => (RunReport::ended(&run_id, &record, CANCELLED_BY_USER), 0),
                };
                let input = RunTaskInput::Report {
                    owed: OwedReport {
                        run,
                        report,
                        withdrawn,
                    },
                };
                let reporter: TaskId = tx
                    .create_task(
                        definition,
                        to_json(&input)?,
                        TaskOptions {
                            ownership: TaskOwnership::Conversation,
                            conversation_id: Some(conversation_id),
                            background: Some(true),
                            abandon_on_restart: None,
                        },
                    )
                    .await?;
                // The new task settles the run once it admits the report.
                record.reporter = Some(reporter.get());
                record.settled = false;
                tx_put_run(&tx, conversation_id, &run_id, &mut record).await?;
                Ok(Some(NextTaskState::Terminal {
                    outcome: TaskOutcome::Aborted {
                        reason: Some(CANCELLED_BY_USER.to_owned()),
                        result: Some(record.state),
                    },
                }))
            },
            &cx,
        )
        .await
}
