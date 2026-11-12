//! Detached `python` cells: the detached cell of one conversation's
//! kernel, and the `jobs.*` kernel host requests over the session's work
//! (ADR 0010).
//!
//! A cell whose call outlives the runtime's blocking budget
//! ([`HostDeps::blocking_budget`](super::super::HostDeps::blocking_budget))
//! keeps running as a job of the session ([`crate::durable::jobs`]): its
//! call settles `detached` with the output so far, and the cell's end
//! settles the job: its result goes to a `jobs.wait` that watches it, else
//! through [`HostDeps::job_settled`](super::super::HostDeps::job_settled)
//! (the daemon's job-settled wake), before the job reads ended. A cancel is
//! the kernel's abort: the cell is interrupted, then its kernel is killed
//! after the grace (ADR 0011).
//!
//! `jobs.list`, `jobs.wait` ([`super::wait`]) and `jobs.cancel` cover the
//! session's detached cells and `bash` tool scripts; the kernel runtime
//! adds its own `bash()` handles and the subagents.

use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError, Weak};

use eukhe_bend::rules::job_notice::{self, Notice};
use eukhe_types::job::CellStatus;
use futures::FutureExt;
use serde_json::{json, Value};

use super::super::{HostCall, HostCallHandler, JobSettledSink};
use super::wait::{self, ask_of, ended_json, job_json};
use super::RlmRuntime;
use crate::durable::jobs::{self, Job, JobEvent, JobResult};

/// The settle side of one detached cell, held by its continuation.
pub(crate) struct CellJobSettle {
    job: Job,
}

impl CellJobSettle {
    /// Hand how the cell ended to its job's delivery (a watching wait, or
    /// the notice through `sink`), then end the job: a cell that ran to
    /// its end or raised exits (0 or 1); an aborted or killed one is
    /// killed (a live cell is never interrupted: that status is a stale
    /// job's at a restart).
    pub(crate) fn settle(self, status: CellStatus, output: String, sink: Option<&JobSettledSink>) {
        self.job.settle(JobResult { status, output }, sink);
        self.job.record(match status {
            CellStatus::Ok => JobEvent::Exited(0),
            CellStatus::Error => JobEvent::Exited(1),
            CellStatus::Aborted | CellStatus::Killed | CellStatus::Interrupted => JobEvent::Killed,
        });
    }
}

/// The detached cell of one conversation's kernel: the kernel runs one
/// cell at a time, so at most one holds it.
#[derive(Default)]
pub(crate) struct CellJobs {
    latest: Mutex<Option<Job>>,
}

impl CellJobs {
    /// Enter the job of a cell whose call just detached.
    pub(crate) fn start(&self, job: Job) -> CellJobSettle {
        *self.latest.lock().unwrap_or_else(PoisonError::into_inner) = Some(job.clone());
        CellJobSettle { job }
    }

    /// The detached cell still holding the kernel.
    pub(crate) fn running(&self) -> Option<Job> {
        self.latest
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .as_ref()
            .filter(|job| job.is_running())
            .cloned()
    }
}

/// Register `jobs.list`, `jobs.wait`, `jobs.wait_event` and `jobs.cancel`
/// (the runtime's `jobs` API).
pub(super) fn register(runtime: &Arc<RlmRuntime>) {
    let registry = runtime.deps.host_requests.clone();
    registry.register("jobs.list", handler(runtime, list));
    registry.register("jobs.wait", handler(runtime, wait));
    registry.register("jobs.wait_event", handler(runtime, wait_event));
    registry.register("jobs.cancel", handler(runtime, cancel));
}

fn handler<F, Fut>(runtime: &Arc<RlmRuntime>, serve: F) -> HostCallHandler
where
    F: Fn(Arc<RlmRuntime>, HostCall) -> Fut + Send + Sync + Copy + 'static,
    Fut: Future<Output = anyhow::Result<Value>> + Send + 'static,
{
    let weak: Weak<RlmRuntime> = Arc::downgrade(runtime);
    Arc::new(move |call: HostCall| {
        let weak = weak.clone();
        async move {
            let runtime = weak.upgrade().ok_or_else(|| {
                anyhow::anyhow!("the session ended before the request could be served")
            })?;
            serve(runtime, call).await
        }
        .boxed()
    })
}

fn find_job(runtime: &RlmRuntime, data: &Value) -> anyhow::Result<Job> {
    let id = data
        .get("job")
        .and_then(Value::as_str)
        .filter(|id| !id.is_empty())
        .ok_or_else(|| anyhow::anyhow!("jobs: job must be a non-empty job id string"))?;
    runtime
        .deps
        .jobs
        .agent_jobs()
        .into_iter()
        .find(|job| job.id().as_str() == id)
        .ok_or_else(|| anyhow::anyhow!("jobs: unknown job {id:?}"))
}

#[tracing::instrument(skip_all)]
async fn list(runtime: Arc<RlmRuntime>, _call: HostCall) -> anyhow::Result<Value> {
    let jobs: Vec<Value> = runtime
        .deps
        .jobs
        .agent_jobs()
        .iter()
        .map(job_json)
        .collect();
    Ok(json!({ "jobs": jobs }))
}

/// `jobs.wait`: the first of the agent's work that settles
/// ([`super::wait`]); `wait_id` names it for its `jobs.wait_event`s.
#[tracing::instrument(skip_all)]
async fn wait(runtime: Arc<RlmRuntime>, call: HostCall) -> anyhow::Result<Value> {
    let ask = ask_of(&call.data)?;
    let id = call
        .data
        .get("wait_id")
        .and_then(Value::as_str)
        .map(str::to_owned);
    let conversation = runtime
        .target(call.call.as_ref(), &super::background())
        .await?
        .0;
    let ended = wait::wait(&runtime, conversation, ask, id, std::future::pending()).await?;
    Ok(ended_json(&ended))
}

/// `jobs.wait_event`: the kernel tells its wait `wait_id` that its
/// `bash()` handle `local` settled, or that the wait was cancelled.
#[tracing::instrument(skip_all)]
async fn wait_event(runtime: Arc<RlmRuntime>, call: HostCall) -> anyhow::Result<Value> {
    let id = call
        .data
        .get("wait_id")
        .and_then(Value::as_str)
        .ok_or_else(|| anyhow::anyhow!("jobs.wait_event: wait_id must be a string"))?;
    let local = match call.data.get("local") {
        None | Some(Value::Null) => None,
        Some(value) => Some(
            value
                .as_u64()
                .and_then(|index| usize::try_from(index).ok())
                .ok_or_else(|| anyhow::anyhow!("jobs.wait_event: local must be an index"))?,
        ),
    };
    let cancel = call
        .data
        .get("cancel")
        .and_then(Value::as_bool)
        .unwrap_or(false);
    runtime.waits.event(id, local, cancel);
    Ok(json!({}))
}

/// `jobs.cancel`: stop one job (a cell through the kernel's abort, a
/// script through its kill) and wait, within the budget, for it to settle.
/// The cancel watches the job while it waits; the compiled core's notice
/// (`bend/ffi_job_notice.bend`) decides the rest: a result that settles in
/// time is taken into the reply (its end is dropped, so the agent's own
/// stop never wakes the session); a job still running at the budget goes
/// to the notice when it settles. A cell or a script's end carries no
/// stopper.
#[tracing::instrument(skip_all)]
async fn cancel(runtime: Arc<RlmRuntime>, call: HostCall) -> anyhow::Result<Value> {
    let job = find_job(&runtime, &call.data)?;
    job.watch();
    job.kill();
    let settled = jobs::wait_until(
        tokio::time::Instant::now() + runtime.deps.blocking_budget(),
        job.ended(),
    )
    .await;
    let taken = match settled {
        jobs::Wait::Settled(_) => true,
        jobs::Wait::Detached => false,
    };
    match job_notice::notice(None, taken) {
        Notice::Drop => {
            let _in_the_reply = job.take();
        }
        Notice::Wake => job.unwatch(runtime.deps.job_settled.as_ref()),
    }
    Ok(job_json(&job))
}
