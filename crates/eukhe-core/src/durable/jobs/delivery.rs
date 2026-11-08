//! Where a job's result goes once it settles: to a `jobs.wait` that
//! watches it, or to the session's job-settled notice
//! ([`HostDeps::job_settled`](super::super::HostDeps::job_settled)), never
//! both. The compiled Bend core decides each step (`bend/wait_any.bend`
//! `step`, entry `wait_any`; `laws/wait_any.bend` R2, R4): a result goes to
//! the notice only when no wait watches it and the session has a wake
//! path; otherwise it is kept for a wait, and the last watching wait that
//! ends without taking it hands it to the notice by the same rule. A job
//! records its result here before its end, so the notice is admitted
//! before the job reads ended.

use std::sync::PoisonError;

use eukhe_bend::rules::wait_any::{self, Delivery, Event, Phase, Target, Wake};
use eukhe_types::job::{CellStatus, JobSettled};

use super::{Job, JobKind};
use crate::durable::JobSettledSink;

/// How a detached cell or script ended: its status and whole output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JobResult {
    pub status: CellStatus,
    pub output: String,
}

/// One job's delivery and, once it settled, its result.
pub(super) struct Slot {
    delivery: Delivery,
    result: Option<JobResult>,
}

impl Default for Slot {
    fn default() -> Self {
        Self {
            delivery: Delivery::FRESH,
            result: None,
        }
    }
}

fn wake(sink: Option<&JobSettledSink>) -> Wake {
    match sink {
        Some(_) => Wake::Notice,
        None => Wake::None,
    }
}

impl Job {
    /// Apply one delivery event under the slot's lock: the result the
    /// event delivered, if it delivered one.
    fn deliver(&self, event: Event, wake: Wake, result: Option<JobResult>) -> Option<JobResult> {
        let delivered = {
            let mut slot = self
                .inner
                .slot
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            if let Some(result) = result {
                slot.result.get_or_insert(result);
            }
            let stepped = wait_any::step(wake, slot.delivery, event);
            slot.delivery = stepped.delivery;
            stepped.delivered.then(|| slot.result.clone()).flatten()
        };
        self.pulse();
        delivered
    }

    /// The row the notice admits for `result`; `None` for a user bash,
    /// which reports through its own notice.
    fn row(&self, result: JobResult) -> Option<JobSettled> {
        let JobResult { status, output } = result;
        match self.kind() {
            JobKind::Cell => Some(JobSettled::Cell {
                job: self.id().clone(),
                status,
                output,
            }),
            JobKind::Shell => Some(JobSettled::Shell {
                job: self.id().clone(),
                status,
                output,
            }),
            JobKind::UserBash => None,
        }
    }

    fn notify(&self, delivered: Option<JobResult>, sink: Option<&JobSettledSink>) {
        if let (Some(result), Some(sink)) = (delivered, sink) {
            if let Some(row) = self.row(result) {
                sink(row);
            }
        }
    }

    /// The job settled with `result`: it goes to the notice through `sink`
    /// unless a wait watches it or the session has no wake path, then it is
    /// kept for a wait. Called before the job's end is recorded.
    pub fn settle(&self, result: JobResult, sink: Option<&JobSettledSink>) {
        let delivered = self.deliver(Event::Settles, wake(sink), Some(result));
        self.notify(delivered, sink);
    }

    /// A wait starts watching the job.
    pub fn watch(&self) {
        let _never_delivers = self.deliver(Event::Watch, Wake::None, None);
    }

    /// A wait stops watching the job: a kept result no wait watches any
    /// more goes to the notice through `sink`.
    pub fn unwatch(&self, sink: Option<&JobSettledSink>) {
        let delivered = self.deliver(Event::Unwatch, wake(sink), None);
        self.notify(delivered, sink);
    }

    /// A wait takes the job's result: the kept result, now delivered, or
    /// the one delivered before (a wait that named the job); `None` while
    /// it runs.
    #[must_use]
    pub fn take(&self) -> Option<JobResult> {
        let delivered = self.deliver(Event::Taken, Wake::None, None);
        delivered.or_else(|| self.result())
    }

    /// The job's result once it settled.
    #[must_use]
    pub fn result(&self) -> Option<JobResult> {
        self.inner
            .slot
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .result
            .clone()
    }

    /// The job as a target of a wait: running, settled with its result
    /// kept for a wait, or settled and delivered.
    #[must_use]
    pub fn target(&self) -> Target {
        match self
            .inner
            .slot
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .delivery
            .phase
        {
            Phase::Live => Target::Running,
            Phase::Kept => Target::Ready,
            Phase::Sent => Target::Gone,
        }
    }
}
