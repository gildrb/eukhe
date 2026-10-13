//! Detached `ipython` cells: the job board of one conversation's kernel and
//! the `jobs.*` kernel host requests over the session's boards (ADR 0010).
//!
//! A cell whose call outlives the runtime's blocking budget
//! ([`HostDeps::blocking_budget`](super::super::HostDeps::blocking_budget))
//! keeps running as a job: its call settles `detached` with the output so
//! far, and the cell's end settles the job here and through
//! [`HostDeps::job_settled`](super::super::HostDeps::job_settled) (the
//! daemon's job-settled wake). A cancel is the kernel's abort: the cell is
//! interrupted, then its kernel is killed after the grace (ADR 0011).
//! Every wait here is clamped to the budget.

use std::collections::VecDeque;
use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError, Weak};
use std::time::{Duration, Instant};

use eukhe_types::job::{CellStatus, JobId};
use futures::FutureExt;
use serde_json::{json, Value};
use tokio::sync::watch;

use super::super::{HostCall, HostCallHandler};
use super::RlmRuntime;
use crate::kernel::cancellation::AbortSignal;

/// Settled jobs a board keeps for `jobs.wait`/`jobs.list`.
const SETTLED_HISTORY: usize = 16;

/// Where one detached cell is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CellJobState {
    Running,
    /// `output` is the cell's whole projection, bounded once.
    Settled {
        status: CellStatus,
        output: String,
    },
}

/// One detached cell on its kernel's board.
#[derive(Clone)]
pub(crate) struct CellJobEntry {
    pub(crate) id: JobId,
    started: Instant,
    cancel: AbortSignal,
    state: watch::Receiver<CellJobState>,
}

impl CellJobEntry {
    pub(crate) fn state(&self) -> CellJobState {
        self.state.borrow().clone()
    }

    pub(crate) fn elapsed(&self) -> Duration {
        self.started.elapsed()
    }

    /// Wait until the job settles or `deadline` passes; its state then.
    pub(crate) async fn wait_until(&self, deadline: tokio::time::Instant) -> CellJobState {
        let mut state = self.state.clone();
        let settled = state.wait_for(|state| matches!(state, CellJobState::Settled { .. }));
        // A dropped sender leaves the last state, which the read reports.
        let _deadline_or_settled = tokio::time::timeout_at(deadline, settled).await;
        self.state()
    }

    /// Request the cell's stop: the kernel interrupts it, and kills the
    /// kernel when the interrupt is not honored within the grace.
    pub(crate) fn cancel(&self) {
        self.cancel.abort();
    }

    fn to_json(&self) -> Value {
        let mut entry = json!({
            "id": self.id.as_str(),
            "kind": "cell",
            "elapsed_ms": u64::try_from(self.elapsed().as_millis()).unwrap_or(u64::MAX),
        });
        match self.state() {
            CellJobState::Running => entry["state"] = json!("running"),
            CellJobState::Settled { status, output } => {
                entry["state"] = json!(status.label());
                entry["output"] = json!(output);
            }
        }
        entry
    }
}

/// The settle side of one detached cell, held by its continuation.
pub(crate) struct CellJobSettle {
    state: watch::Sender<CellJobState>,
}

impl CellJobSettle {
    pub(crate) fn settle(self, status: CellStatus, output: String) {
        self.state
            .send_replace(CellJobState::Settled { status, output });
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

    /// Enter a cell whose call just detached; `cancel` is its execution's
    /// abort signal.
    pub(crate) fn start(&self, id: JobId, cancel: AbortSignal) -> CellJobSettle {
        let (state, receiver) = watch::channel(CellJobState::Running);
        let mut entries = self.entries();
        while entries.len() > SETTLED_HISTORY {
            let Some(oldest_settled) = entries
                .iter()
                .position(|entry| entry.state() != CellJobState::Running)
            else {
                break;
            };
            entries.remove(oldest_settled);
        }
        entries.push_back(CellJobEntry {
            id,
            started: Instant::now(),
            cancel,
            state: receiver,
        });
        CellJobSettle { state }
    }

    /// The detached cell still holding the kernel.
    pub(crate) fn running(&self) -> Option<CellJobEntry> {
        self.entries()
            .iter()
            .find(|entry| entry.state() == CellJobState::Running)
            .cloned()
    }

    fn get(&self, id: &str) -> Option<CellJobEntry> {
        self.entries()
            .iter()
            .find(|entry| entry.id.as_str() == id)
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
    job.wait_until(tokio::time::Instant::now() + timeout).await;
    Ok(job.to_json())
}

/// `jobs.cancel`: stop one job through the kernel's abort (interrupt, then
/// kill after the grace) and wait, within the budget, for it to settle.
#[tracing::instrument(skip_all)]
async fn cancel(runtime: Arc<RlmRuntime>, data: Value) -> anyhow::Result<Value> {
    let job = find_job(&runtime, &data)?;
    job.cancel();
    job.wait_until(tokio::time::Instant::now() + runtime.deps.blocking_budget())
        .await;
    Ok(job.to_json())
}
