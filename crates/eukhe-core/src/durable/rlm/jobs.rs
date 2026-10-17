//! Detached `ipython` cells: the job board of one conversation's kernel and
//! the `jobs.*` kernel host requests over the session's boards (ADR 0010).
//!
//! A cell whose call outlives the runtime's blocking budget
//! ([`HostDeps::blocking_budget`](super::super::HostDeps::blocking_budget))
//! keeps running as a job of the session ([`crate::durable::jobs`]): its
//! call settles `detached` with the output so far, and the cell's end
//! settles the job here and through
//! [`HostDeps::job_settled`](super::super::HostDeps::job_settled) (the
//! daemon's job-settled wake). A cancel is the kernel's abort: the cell is
//! interrupted, then its kernel is killed after the grace (ADR 0011).
//! Every wait here is the one blocking wait on a job
//! ([`jobs::wait_until`]), within the budget.

use std::collections::VecDeque;
use std::future::Future;
use std::sync::{Arc, Mutex, OnceLock, PoisonError, Weak};
use std::time::Duration;

use eukhe_types::job::CellStatus;
use futures::FutureExt;
use serde_json::{json, Value};

use super::super::{HostCall, HostCallHandler};
use super::RlmRuntime;
use crate::durable::jobs::{self, Job, JobEnd, JobEvent, JobState};

/// Settled jobs a board keeps for `jobs.wait`/`jobs.list`.
const SETTLED_HISTORY: usize = 16;

/// One detached cell on its kernel's board: its job, and how the cell
/// ended once it did.
#[derive(Clone)]
pub(crate) struct CellJobEntry {
    pub(crate) job: Job,
    /// The cell's status and whole projection (bounded once), set before
    /// its job ends.
    settled: Arc<OnceLock<(CellStatus, String)>>,
}

impl CellJobEntry {
    fn to_json(&self) -> Value {
        let mut entry = json!({
            "id": self.job.id().as_str(),
            "kind": "cell",
            "elapsed_ms": u64::try_from(self.job.elapsed().as_millis()).unwrap_or(u64::MAX),
        });
        match (self.job.state(), self.settled.get()) {
            (JobState::Live { .. }, _) => entry["state"] = json!("running"),
            (JobState::Ended { .. }, Some((status, output))) => {
                entry["state"] = json!(status.label());
                entry["output"] = json!(output);
            }
            // A cell job ends only through its settle, which keeps the
            // status first; the end alone still names how it ended.
            (JobState::Ended { end, .. }, None) => {
                entry["state"] = json!(match end {
                    JobEnd::Exited(0) => CellStatus::Ok.label(),
                    JobEnd::Exited(_) => CellStatus::Error.label(),
                    JobEnd::Killed => CellStatus::Killed.label(),
                });
            }
        }
        entry
    }
}

/// The settle side of one detached cell, held by its continuation.
pub(crate) struct CellJobSettle {
    entry: CellJobEntry,
}

impl CellJobSettle {
    /// Keep how the cell ended, then end its job: a cell that ran to its
    /// end or raised exits (0 or 1); an aborted or killed one is killed.
    pub(crate) fn settle(self, status: CellStatus, output: String) {
        let _ = self.entry.settled.set((status, output));
        self.entry.job.record(match status {
            CellStatus::Ok => JobEvent::Exited(0),
            CellStatus::Error => JobEvent::Exited(1),
            CellStatus::Aborted | CellStatus::Killed => JobEvent::Killed,
        });
    }
}

/// The detached cells of one conversation's kernel: at most one running
/// (the kernel runs one cell at a time), then the latest settled ones.
#[derive(Default)]
pub(crate) struct CellJobs {
    entries: Mutex<VecDeque<CellJobEntry>>,
}

impl CellJobs {
    fn entries(&self) -> std::sync::MutexGuard<'_, VecDeque<CellJobEntry>> {
        self.entries.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Enter the job of a cell whose call just detached.
    pub(crate) fn start(&self, job: Job) -> CellJobSettle {
        let entry = CellJobEntry {
            job,
            settled: Arc::default(),
        };
        let mut entries = self.entries();
        while entries.len() > SETTLED_HISTORY {
            let Some(oldest_settled) = entries.iter().position(|entry| !entry.job.is_running())
            else {
                break;
            };
            entries.remove(oldest_settled);
        }
        entries.push_back(entry.clone());
        CellJobSettle { entry }
    }

    /// The detached cell still holding the kernel.
    pub(crate) fn running(&self) -> Option<CellJobEntry> {
        self.entries()
            .iter()
            .find(|entry| entry.job.is_running())
            .cloned()
    }

    fn get(&self, id: &str) -> Option<CellJobEntry> {
        self.entries()
            .iter()
            .find(|entry| entry.job.id().as_str() == id)
            .cloned()
    }

    fn list(&self) -> Vec<CellJobEntry> {
        self.entries().iter().cloned().collect()
    }
}

/// Register `jobs.list`, `jobs.wait`, and `jobs.cancel` (the runtime's
/// `jobs` API) over every kernel board of the session.
pub(super) fn register(runtime: &Arc<RlmRuntime>) {
    let registry = runtime.deps.host_requests.clone();
    registry.register("jobs.list", handler(runtime, list));
    registry.register("jobs.wait", handler(runtime, wait));
    registry.register("jobs.cancel", handler(runtime, cancel));
}

fn handler<F, Fut>(runtime: &Arc<RlmRuntime>, serve: F) -> HostCallHandler
where
    F: Fn(Arc<RlmRuntime>, Value) -> Fut + Send + Sync + Copy + 'static,
    Fut: Future<Output = anyhow::Result<Value>> + Send + 'static,
{
    let weak: Weak<RlmRuntime> = Arc::downgrade(runtime);
    Arc::new(move |call: HostCall| {
        let weak = weak.clone();
        async move {
            let runtime = weak.upgrade().ok_or_else(|| {
                anyhow::anyhow!("the session ended before the request could be served")
            })?;
            serve(runtime, call.data).await
        }
        .boxed()
    })
}

fn every_job(runtime: &RlmRuntime) -> Vec<CellJobEntry> {
    runtime
        .kernels
        .boards()
        .iter()
        .flat_map(|board| board.list())
        .collect()
}

fn find_job(runtime: &RlmRuntime, data: &Value) -> anyhow::Result<CellJobEntry> {
    let id = data
        .get("job")
        .and_then(Value::as_str)
        .filter(|id| !id.is_empty())
        .ok_or_else(|| anyhow::anyhow!("jobs: job must be a non-empty job id string"))?;
    runtime
        .kernels
        .boards()
        .iter()
        .find_map(|board| board.get(id))
        .ok_or_else(|| anyhow::anyhow!("jobs: unknown job {id:?}"))
}

#[tracing::instrument(skip_all)]
async fn list(runtime: Arc<RlmRuntime>, _data: Value) -> anyhow::Result<Value> {
    let jobs: Vec<Value> = every_job(&runtime)
        .iter()
        .map(CellJobEntry::to_json)
        .collect();
    Ok(json!({ "jobs": jobs }))
}

/// `jobs.wait`: wait for one job, `timeout_ms` (default: the budget)
/// clamped to the blocking budget; the job's state when the wait ends.
#[tracing::instrument(skip_all)]
async fn wait(runtime: Arc<RlmRuntime>, data: Value) -> anyhow::Result<Value> {
    let job = find_job(&runtime, &data)?;
    let budget = runtime.deps.blocking_budget();
    let timeout = match data.get("timeout_ms") {
        None | Some(Value::Null) => budget,
        Some(value) => value
            .as_u64()
            .map(Duration::from_millis)
            .ok_or_else(|| anyhow::anyhow!("jobs.wait timeout_ms must be a non-negative integer"))?
            .min(budget),
    };
    let _settled_or_detached =
        jobs::wait_until(tokio::time::Instant::now() + timeout, job.job.ended()).await;
    Ok(job.to_json())
}

/// `jobs.cancel`: stop one job through the kernel's abort (interrupt, then
/// kill after the grace) and wait, within the budget, for it to settle.
#[tracing::instrument(skip_all)]
async fn cancel(runtime: Arc<RlmRuntime>, data: Value) -> anyhow::Result<Value> {
    let job = find_job(&runtime, &data)?;
    job.job.kill();
    let _settled_or_detached = jobs::wait_until(
        tokio::time::Instant::now() + runtime.deps.blocking_budget(),
        job.job.ended(),
    )
    .await;
    Ok(job.to_json())
}
