//! Jobs (docs/runtime.md S2): everything that runs long is one [`Job`]. A
//! user bash is a job from its start; an `ipython` cell or a `bash` tool
//! script becomes one when its call outlives the blocking budget (ADR
//! 0010). A job counts its output
//! under the session's output cap, reports exactly one end, and has a kill.
//!
//! The Bend model `bend/job.bend` is the specification. `laws/job.bend`
//! (S2) states its laws and `proof/job/` proves them. The compiled Bend
//! core decides; Rust gathers the facts and acts: [`JobState::step`] runs
//! the model's `feed` (entry `job`), [`JobTable::rewind_to`] its `kills`
//! (entry `job_rewind`). [`wait_until`] is an event loop over the stepper
//! `job_wait`, which decides every event of a blocking wait with the
//! model's `poll`: Rust only sends the timer's tick and the job's end in
//! the order they arrive, so `laws/job_wait.bend`, which ties the stepper
//! to the model's `wait` for every order of events, covers it; no bridge.
//!
//! The session's [`JobTable`] holds its jobs. The table commits the start
//! and the end of each job (never its output) as a session document, so
//! the session state tree holds one node per running job ([`tree`]). A
//! rewind of the session sends the kill to every running job that started
//! after its target entry ([`stop_orphans`]), in the order of the entry
//! commits the table sees; the system prompt shows the running jobs of the
//! tree ([`running_jobs_section`]).

#[cfg(test)]
mod tests;
mod tree;

use std::collections::{HashMap, VecDeque};
use std::future::Future;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};
use std::task::Poll;
use std::time::{Duration, Instant};

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::{Entry, Stepper};
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

    /// The state after `event`, and the end the event reported: `feed`
    /// and `ends.of` in `bend/job.bend` (`laws/job.bend` S2), run by the
    /// compiled Bend core. Under the cap `Some(c)` a job keeps at most `c`
    /// bytes and counts the rest as dropped; `None` (the opt-out) keeps
    /// all; the bytes kept plus dropped saturate at the wire's
    /// [`NAT_MAX`] (`job_feed_fills`). An ended job ignores every event.
    #[must_use]
    pub fn step(self, cap: Option<u64>, event: JobEvent) -> (Self, Option<JobEnd>) {
        eukhe_bend::expect_core(Entry::Job, self.feed(cap, event))
    }

    fn feed(
        self,
        cap: Option<u64>,
        event: JobEvent,
    ) -> Result<(Self, Option<JobEnd>), eukhe_bend::Error> {
        let mut request = Writer::new();
        // The bound of the bytes kept plus dropped: the wire's largest Nat.
        request.nat(NAT_MAX);
        match cap {
            None => request.none(),
            Some(cap) => request.some().nat(cap.min(NAT_MAX)),
        };
        match self {
            Self::Live { kept, dropped } => {
                request.tag(0).nat(kept).nat(dropped);
            }
            Self::Ended { kept, dropped, end } => {
                request.tag(1).nat(kept).nat(dropped);
                put_end(&mut request, end);
            }
        }
        match event {
            JobEvent::Output(bytes) => {
                request.tag(0).nat(bytes.min(NAT_MAX));
            }
            JobEvent::Exited(code) => {
                let (hi, lo) = code_words(code);
                request.tag(1).u32(hi).u32(lo);
            }
            JobEvent::Killed => {
                request.tag(2);
            }
        }
        let reply = eukhe_bend::call(Entry::Job, &request.finish()?)?;
        let mut reply = Reader::reply(&reply)?;
        let next = match reply.tag_of(2, "a job")? {
            0 => Self::Live {
                kept: reply.nat()?,
                dropped: reply.nat()?,
            },
            // `tag_of` answers a tag below 2: this is 1.
            _ => Self::Ended {
                kept: reply.nat()?,
                dropped: reply.nat()?,
                end: get_end(&mut reply)?,
            },
        };
        // The ends the event reported: none, or its one end.
        let end = match reply.tag_of(2, "at most one job end")? {
            0 => None,
            _ => Some(get_end(&mut reply)?),
        };
        reply.end()?;
        Ok((next, end))
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

/// An exit code as the core's `Code`: the i64's two 32-bit words, high
/// first (two's complement), so every code crosses exactly.
fn code_words(code: i64) -> (u32, u32) {
    let bits = u64::from_ne_bytes(code.to_ne_bytes());
    ((bits >> 32) as u32, bits as u32)
}

fn put_end(request: &mut Writer, end: JobEnd) {
    match end {
        JobEnd::Exited(code) => {
            let (hi, lo) = code_words(code);
            request.tag(0).u32(hi).u32(lo);
        }
        JobEnd::Killed => {
            request.tag(1);
        }
    }
}

fn get_end(reply: &mut Reader<'_>) -> Result<JobEnd, WireError> {
    Ok(match reply.tag_of(2, "a job end")? {
        0 => {
            let hi = reply.u32()?;
            let lo = reply.u32()?;
            JobEnd::Exited(i64::from_ne_bytes(
                ((u64::from(hi) << 32) | u64::from(lo)).to_ne_bytes(),
            ))
        }
        // `tag_of` answers a tag below 2: this is 1.
        _ => JobEnd::Killed,
    })
}

/// A commit as the core's `Maybe<Nat>` (a commit sequence counts commits,
/// so it stays far below the wire's largest Nat).
fn put_commit(request: &mut Writer, commit: Option<Seq>) {
    match commit {
        None => request.none(),
        Some(seq) => request.some().nat(seq.get()),
    };
}

/// The kills of a rewind to the entry committed at `target`, one per job
/// of `jobs`, in order: the model's `kills`, run by the compiled Bend core
/// (`bend/ffi_job_rewind.bend`) on whether each job runs and the commit it
/// started after.
fn rewind_kills(target: Option<Seq>, jobs: &[Job]) -> Result<Vec<bool>, eukhe_bend::Error> {
    let mut request = Writer::new();
    put_commit(&mut request, target);
    request.count(jobs.len());
    for job in jobs {
        request.bool(job.is_running());
        put_commit(&mut request, job.inner.after);
    }
    let reply = eukhe_bend::call(Entry::JobRewind, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    if reply.count()? != jobs.len() {
        return Err(WireError::Malformed {
            at: 0,
            expected: "one kill per job",
        }
        .into());
    }
    let kills = jobs
        .iter()
        .map(|_| reply.bool())
        .collect::<Result<Vec<_>, _>>()?;
    reply.end()?;
    Ok(kills)
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

/// The event of a wait's stepper (entry `job_wait`): the deadline timer
/// fired (one tick: the wait's whole budget).
const TICK: u32 = 0;

/// The event of a wait's stepper (entry `job_wait`): the end came (its
/// value stays here).
const END: u32 = 1;

/// The one blocking wait on a job (the model's `wait`): `Settled` with
/// `end`'s value when it resolves before `deadline`, else `Detached` at the
/// deadline. The compiled Bend core's stepper (`bend/ffi_job_wait.bend`)
/// decides; this host opens it with a budget of one tick (the deadline
/// timer), sends it each event as it arrives (the timer's tick, then the
/// end, within one poll) and returns on its final turn. Every blocking
/// wait on a job uses it, with a deadline within the session's blocking
/// budget ([`HostDeps::blocking_budget`](super::HostDeps::blocking_budget)).
pub async fn wait_until<F: Future>(deadline: tokio::time::Instant, end: F) -> Wait<F::Output> {
    let mut value = None;
    let opened = (|| {
        let (core, reply) = Stepper::open(Entry::JobWait, &Writer::new().nat(1).finish()?)?;
        Ok::<_, eukhe_bend::Error>((core, turn(&reply, &mut value)?))
    })();
    let (mut core, opened) = eukhe_bend::expect_core(Entry::JobWait, opened);
    if let Some(waited) = opened {
        return waited;
    }
    let mut timer = std::pin::pin!(tokio::time::sleep_until(deadline));
    let mut end = std::pin::pin!(end);
    let mut fired = false;
    std::future::poll_fn(|cx| {
        // The timer fires once; the clock shows a deadline already past
        // before tokio's timer wheel turns.
        if !fired && (tokio::time::Instant::now() >= deadline || timer.as_mut().poll(cx).is_ready())
        {
            fired = true;
            if let Some(waited) = send(&mut core, TICK, &mut value) {
                return Poll::Ready(waited);
            }
        }
        // The end comes once.
        if value.is_none() {
            if let Poll::Ready(ended) = end.as_mut().poll(cx) {
                value = Some(ended);
                if let Some(waited) = send(&mut core, END, &mut value) {
                    return Poll::Ready(waited);
                }
            }
        }
        Poll::Pending
    })
    .await
}

/// Sends a wait's stepper `event` ([`TICK`] or [`END`]); answers its turn.
fn send<T>(core: &mut Stepper, event: u32, value: &mut Option<T>) -> Option<Wait<T>> {
    eukhe_bend::expect_core(
        Entry::JobWait,
        (|| turn(&core.step(&Writer::new().tag(event).finish()?)?, value))(),
    )
}

/// The turn a wait's stepper replied: `None` while the call waits,
/// `Settled` with the end's `value`, or `Detached`.
fn turn<T>(reply: &str, value: &mut Option<T>) -> Result<Option<Wait<T>>, eukhe_bend::Error> {
    let mut reply = Reader::reply(reply)?;
    let turn = reply.tag_of(3, "a turn of a wait")?;
    reply.end()?;
    Ok(match turn {
        0 => None,
        1 => Some(Wait::Settled(value.take().ok_or(WireError::Malformed {
            at: 0,
            expected: "a settle after the end came",
        })?)),
        // `tag_of` answers a tag below 3: this is 2.
        _ => Some(Wait::Detached),
    })
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
        let (state, _) = watch::channel(JobState::START);
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
        job.record(JobEvent::Output(written));
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

    /// The rewind to the session just after `target` was added (`None`:
    /// before every entry): it keeps the running jobs that started before
    /// that entry was committed, so their nodes are in the state tree at
    /// the target, and sends the kill to every other one; the compiled Bend
    /// core decides which (the model's `kills`, `bend/ffi_job_rewind.bend`).
    /// The order comes from the commits the table saw, not from the job
    /// nodes, which the writer commits later. An entry the table did not
    /// see was committed before the session opened, so before every job.
    /// The jobs it sent the kill to, oldest first.
    pub fn rewind_to(&self, target: Option<EntryId>) -> Vec<Job> {
        let target = target.and_then(|entry| lock(&self.entries).commits.get(&entry).copied());
        let jobs = self.jobs();
        let kills = eukhe_bend::expect_core(Entry::JobRewind, rewind_kills(target, &jobs));
        jobs.into_iter()
            .zip(kills)
            .filter_map(|(job, kill)| kill.then_some(job))
            .inspect(Job::kill)
            .collect()
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
