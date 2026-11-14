//! The work a conversation still owns after its turn ended: the session
//! jobs that run (detached `python` cells and `bash` tool scripts), the
//! kernel's background `bash()` commands, the unsettled children, and the
//! unsettled workflow runs. Each one settles into a wake of the session
//! (its job-settled notice or its report), so a turn that ended while any
//! of them runs is waiting, not done: print mode keeps the session open,
//! ACP holds the prompt, and the TUI shows what the session waits on.

use eukhe_chord::context::Context;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::SessionError;
use eukhe_durable::types::ConversationId;
use eukhe_types::job::JobId;

use super::children::unsettled_child_tasks;
use super::deps::HostDeps;
use super::jobs::{Job, JobKind};
use super::rlm::kernel_background_jobs;
use super::workflow::unsettled_run_tasks;

/// One running session job.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PendingJob {
    pub id: JobId,
    pub kind: JobKind,
    pub label: String,
    /// When the job started, in Unix milliseconds.
    pub started_at_ms: u64,
}

/// What a conversation still waits on.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PendingWork {
    /// Running session jobs (cells and scripts that detached), oldest first.
    pub jobs: Vec<PendingJob>,
    /// The session's own jobs are pending by the job table's account
    /// ([`super::jobs::JobTable::pending_work`]): one runs, or one settled
    /// with a result kept for a wait that no notice took yet.
    pub held_results: bool,
    /// Running background `bash()` commands of the conversation's kernel.
    pub kernel_jobs: usize,
    /// Children whose report is still owed.
    pub children: usize,
    /// Workflow runs whose report is still owed.
    pub workflow_runs: usize,
}

impl PendingWork {
    /// Nothing runs that will wake the session.
    #[must_use]
    pub fn is_none(&self) -> bool {
        self.jobs.is_empty()
            && !self.held_results
            && self.kernel_jobs == 0
            && self.children == 0
            && self.workflow_runs == 0
    }
}

/// Why the pending work could not be read.
#[derive(Debug, thiserror::Error)]
pub enum PendingWorkError {
    /// The children or workflow-run document read failed.
    #[error("cannot read the conversation's pending work: {0}")]
    Read(#[from] SessionError),
}

/// The work `conversation` still owns. A user bash is not counted: it
/// never wakes the session (its owner reads its result).
///
/// # Errors
///
/// A children or workflow-run document read failure (callers count an
/// unknown as pending: unknown never reads idle).
pub async fn pending_work(
    deps: &HostDeps,
    harness: &Harness,
    conversation: ConversationId,
    cx: &Context,
) -> Result<PendingWork, PendingWorkError> {
    let jobs = deps
        .jobs
        .agent_jobs()
        .into_iter()
        .filter(Job::is_running)
        .map(|job| PendingJob {
            id: job.id().clone(),
            kind: job.kind(),
            label: job.label().to_owned(),
            started_at_ms: job.started_at_ms(),
        })
        .collect();
    let held_results = deps.jobs.pending_work();
    let children = unsettled_child_tasks(harness, conversation, cx)
        .await?
        .len();
    let workflow_runs = unsettled_run_tasks(harness, conversation, cx).await?.len();
    Ok(PendingWork {
        jobs,
        held_results,
        kernel_jobs: kernel_background_jobs(deps, conversation),
        children,
        workflow_runs,
    })
}
