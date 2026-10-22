//! Jobs (docs/runtime.md S2): everything that runs long is one [`Job`]. A
//! user bash is a job from its start; an `ipython` cell or a `bash` tool
//! script becomes one when its call outlives the blocking budget (ADR
//! 0010). A job counts its output
//! under the session's output cap, reports exactly one end, and has a kill.
//!
//! The Bend model `bend/job.bend` is the specification. `LAWS.bend` section
//! (S2) states its laws and `PROOF.bend` section `job` proves them. The bridge
//! test (`bridge.rs`, with `bend/bridge_job.bend`) runs this code and the
//! model on the same scenarios and requires the same transcript:
//! [`JobState::step`] is the model's `step`, [`wait_until`] its `wait`, and
//! [`JobTable::rewind`] its `rewind`.
//!
//! The session's [`JobTable`] holds its jobs. The table commits the start
//! and the end of each job (never its output) as a session document, so
//! the session state tree holds one node per running job ([`tree`]). A
//! rewind of the session sends the kill to every running job that started
//! after its target entry ([`stop_orphans`]), in the order of the entry
//! commits the table sees; the system prompt shows the running jobs of the
//! tree ([`running_jobs_section`]).

#[cfg(test)]
mod bridge;
#[cfg(test)]
mod tests;
mod tree;

use std::collections::{HashMap, VecDeque};
use std::future::Future;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};
use std::task::Poll;
use std::time::{Duration, Instant};

use eukhe_durable::harness::Truncation;
use eukhe_durable::types::{CommitChange, CommitPublication, EntryId, Seq};
use eukhe_types::job::JobId;
use tokio::sync::{mpsc, watch};

use tree::JobRecord;
pub use tree::{
    install, running_jobs_section, stop_orphans, Orphans, JOB_DOC_KIND,
    JOB_RECORD_FAILED_CUSTOM_TYPE,
};

/// Ended jobs a table keeps for `jobs.list` and `jobs.wait`.
const ENDED_HISTORY: usize = 16;

/// What runs as a job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JobKind {
    /// An `ipython` cell whose call detached.
    Cell,
    /// A user bash command (`!`, `execute_bash`, `execute_bash_and_wait`).
    UserBash,
    /// A `bash` tool script whose call detached.
    Shell,
}

impl JobKind {
    /// The name: `cell`, `bash`, or `shell`.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Cell => "cell",
            Self::UserBash => "bash",
            Self::Shell => "shell",
        }
    }
}

/// How a job ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JobEnd {
    /// The process exited with this code.
    Exited(i64),
    /// The kill signal ended it.
    Killed,
}

/// Where a job is: live with the output bytes it kept and dropped, or
/// ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JobState {
    Live {
        kept: u64,
        dropped: u64,
    },
    Ended {
        kept: u64,
        dropped: u64,
        end: JobEnd,
    },
}

/// What a job sees.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JobEvent {
    /// `n` bytes of output.
    Output(u64),
    /// The process exited with this code.
    Exited(i64),
    /// The kill signal reached the job.
    Killed,
}

impl JobState {
    /// A new job.
    pub const START: Self = Self::Live {
        kept: 0,
        dropped: 0,
    };

    /// The state after `event`, and the end the event reported (the
    /// model's `step` and `ends.of`). Under the cap `Some(c)` a job keeps at
    /// most `c` bytes and counts the rest as dropped; `None` (the opt-out)
    /// keeps all. An ended job ignores every event.
    #[must_use]
    pub fn step(self, cap: Option<u64>, event: JobEvent) -> (Self, Option<JobEnd>) {
        match self {
            Self::Ended { .. } => (self, None),
            Self::Live { kept, dropped } => match event {
                JobEvent::Output(bytes) => {
                    let take = cap.map_or(bytes, |cap| bytes.min(cap.saturating_sub(kept)));
                    (
                        Self::Live {
                            kept: kept.saturating_add(take),
                            dropped: dropped.saturating_add(bytes - take),
                        },
                        None,
                    )
                }
                JobEvent::Exited(code) => {
                    let end = JobEnd::Exited(code);
                    (Self::Ended { kept, dropped, end }, Some(end))
                }
                JobEvent::Killed => (
                    Self::Ended {
                        kept,
                        dropped,
                        end: JobEnd::Killed,
                    },
                    Some(JobEnd::Killed),
                ),
            },
        }
    }

    /// The job still runs.
    #[must_use]
    pub fn is_live(self) -> bool {
        match self {
            Self::Live { .. } => true,
            Self::Ended { .. } => false,
        }
    }
}

/// The kill of a job: it sends the kill signal to what runs (a process, a
/// cell's interrupt). The owner of the job reports the end that follows
/// with [`Job::record`].
pub type KillSwitch = Box<dyn Fn(&Job) + Send + Sync>;

/// A job to start ([`JobTable::start`]).
pub struct JobSpec {
    pub id: JobId,
    pub kind: JobKind,
    /// What runs, for people: the command of a bash.
    pub label: String,
    /// The output cap (default on; [`Truncation::Off`] is the opt-out).
    pub truncation: Truncation,
    /// The output bytes the run wrote before it became a job (a cell or a
    /// script whose call detached): they count under the cap as the job's
    /// first output, so the job counts every byte of the run.
    pub written: u64,
    pub kill: KillSwitch,
}

struct JobInner {
    id: JobId,
    kind: JobKind,
    label: String,
    started: Instant,
    /// The commit of the last entry the table saw when the job started
    /// (`None`: no entry since the session opened). A rewind decides from
    /// it, not from the job's node, which the writer commits later.
    after: Option<Seq>,
    /// The cap in bytes; `None` keeps all.
    cap: Option<u64>,
    state: watch::Sender<JobState>,
    kill: KillSwitch,
    /// The table's tree writer, which records the end.
    records: mpsc::UnboundedSender<JobRecord>,
}

/// One job; a clone is the same job.
#[derive(Clone)]
pub struct Job {
    inner: Arc<JobInner>,
}

impl Job {
    #[must_use]
    pub fn id(&self) -> &JobId {
        &self.inner.id
    }

    #[must_use]
    pub fn kind(&self) -> JobKind {
        self.inner.kind
    }

    #[must_use]
    pub fn label(&self) -> &str {
        &self.inner.label
    }

    #[must_use]
    pub fn elapsed(&self) -> Duration {
        self.inner.started.elapsed()
    }

    #[must_use]
    pub fn state(&self) -> JobState {
        *self.inner.state.borrow()
    }

    /// The job has not ended.
    #[must_use]
    pub fn is_running(&self) -> bool {
        self.state().is_live()
    }

    /// Apply one event. The event that ends the job reports its end to the
    /// table's writer. Every later event is ignored, so a job reports
    /// exactly one end.
    pub fn record(&self, event: JobEvent) {
        let mut ended = None;
        self.inner.state.send_if_modified(|state| {
            let (next, end) = state.step(self.inner.cap, event);
            ended = end;
            let changed = next != *state;
            *state = next;
            changed
        });
        if let Some(end) = ended {
            // A closed writer means the session closed; the next open
            // retires the job's node.
            let _ = self.inner.records.send(JobRecord::End {
                id: self.inner.id.clone(),
                end,
            });
        }
    }

    /// Send the kill signal to a running job; nothing for an ended one.
    pub fn kill(&self) {
        if self.is_running() {
            (self.inner.kill)(self);
        }
    }

    /// Resolves with the end of the job.
    pub async fn ended(&self) -> JobEnd {
        let mut state = self.inner.state.subscribe();
        // The job holds the sender, so the channel stays open.
        match state
            .wait_for(|state| !state.is_live())
            .await
            .map(|state| *state)
        {
            Ok(JobState::Ended { end, .. }) => end,
            Ok(JobState::Live { .. }) | Err(_) => std::future::pending().await,
        }
    }
}

/// The answer of a blocking call on a job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Wait<T> {
    /// The job ended in time.
    Settled(T),
    /// The budget passed: the job runs on in the background.
    Detached,
}

/// The one blocking wait on a job (the model's `wait`): `Settled` with
/// `end`'s value when it resolves before `deadline`, else `Detached` at the
/// deadline. Each poll reads the clock first, so a deadline that has passed
/// detaches even when the end is ready. Every blocking wait on a job uses
/// it, with a deadline within the session's blocking budget
/// ([`HostDeps::blocking_budget`](super::HostDeps::blocking_budget)).
pub async fn wait_until<F: Future>(deadline: tokio::time::Instant, end: F) -> Wait<F::Output> {
    let mut timer = std::pin::pin!(tokio::time::sleep_until(deadline));
    let mut end = std::pin::pin!(end);
    std::future::poll_fn(|cx| {
        if tokio::time::Instant::now() >= deadline || timer.as_mut().poll(cx).is_ready() {
            return Poll::Ready(Wait::Detached);
        }
        end.as_mut().poll(cx).map(Wait::Settled)
    })
    .await
}

/// The entries the session committed since it opened, in commit order.
#[derive(Default)]
struct EntryOrder {
    /// The commit of the last entry.
    last: Option<Seq>,
    commits: HashMap<EntryId, Seq>,
}

/// The jobs of one session: the running ones and the latest ended ones.
pub struct JobTable {
    jobs: Mutex<VecDeque<Job>>,
    entries: Mutex<EntryOrder>,
    records: mpsc::UnboundedSender<JobRecord>,
    /// The writer's end of `records`, until the session opens.
    queue: Mutex<Option<mpsc::UnboundedReceiver<JobRecord>>>,
}

impl Default for JobTable {
    fn default() -> Self {
        let (records, queue) = mpsc::unbounded_channel();
        Self {
            jobs: Mutex::new(VecDeque::new()),
            entries: Mutex::default(),
            records,
            queue: Mutex::new(Some(queue)),
        }
    }
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

impl JobTable {
    /// Start a job: it runs until its owner records its end.
    pub fn start(&self, spec: JobSpec) -> Job {
        let JobSpec {
            id,
            kind,
            label,
            truncation,
            written,
            kill,
        } = spec;
        let cap = truncation
            .max_bytes()
            .map(|cap| u64::try_from(cap).unwrap_or(u64::MAX));
        let (seeded, _) = JobState::START.step(cap, JobEvent::Output(written));
        let (state, _) = watch::channel(seeded);
        let job = Job {
            inner: Arc::new(JobInner {
                id: id.clone(),
                kind,
                label: label.clone(),
                started: Instant::now(),
                after: lock(&self.entries).last,
                cap,
                state,
                kill,
                records: self.records.clone(),
            }),
        };
        let _ = self.records.send(JobRecord::Start { id, kind, label });
        let mut jobs = lock(&self.jobs);
        while jobs.len() >= ENDED_HISTORY {
            let Some(oldest_ended) = jobs.iter().position(|job| !job.is_running()) else {
                break;
            };
            jobs.remove(oldest_ended);
        }
        jobs.push_back(job.clone());
        job
    }

    /// The job `id`, running or recently ended.
    #[must_use]
    pub fn get(&self, id: &str) -> Option<Job> {
        lock(&self.jobs)
            .iter()
            .find(|job| job.id().as_str() == id)
            .cloned()
    }

    /// Every job the table holds, oldest first.
    #[must_use]
    pub fn jobs(&self) -> Vec<Job> {
        lock(&self.jobs).iter().cloned().collect()
    }

    /// A rewind (the model's `rewind`): send the kill to every running job
    /// that `keeps` does not hold; the jobs it keeps stay as they are. The
    /// jobs it sent the kill to, oldest first.
    pub fn rewind(&self, keeps: impl Fn(&Job) -> bool) -> Vec<Job> {
        self.jobs()
            .into_iter()
            .filter(|job| job.is_running() && !keeps(job))
            .inspect(Job::kill)
            .collect()
    }

    /// The rewind to the session just after `target` was added (`None`:
    /// before every entry): it keeps the running jobs that started before
    /// that entry was committed, so their nodes are in the state tree at
    /// the target, and sends the kill to every other one. The order comes
    /// from the commits the table saw, not from the job nodes, which the
    /// writer commits later. An entry the table did not see was committed
    /// before the session opened, so before every job.
    pub fn rewind_to(&self, target: Option<EntryId>) -> Vec<Job> {
        let target = target.and_then(|entry| lock(&self.entries).commits.get(&entry).copied());
        self.rewind(|job| match (target, job.inner.after) {
            (None, _) => false,
            (Some(_), None) => true,
            (Some(target), Some(after)) => after < target,
        })
    }

    /// Note the entries of a commit (the session's commit listener).
    pub(super) fn observe(&self, publication: &CommitPublication) {
        let mut entries = lock(&self.entries);
        for change in &publication.changes {
            match change {
                CommitChange::Entry(record) => {
                    entries.commits.insert(record.id, publication.seq);
                    entries.last = Some(publication.seq);
                }
                CommitChange::Conversation(_)
                | CommitChange::Task(_)
                | CommitChange::Submission(_)
                | CommitChange::Document(_) => {}
            }
        }
    }

    fn take_queue(&self) -> Option<mpsc::UnboundedReceiver<JobRecord>> {
        lock(&self.queue).take()
    }
}
