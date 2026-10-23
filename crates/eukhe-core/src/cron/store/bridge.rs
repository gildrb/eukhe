//! The bridge between the cron store ([`AgentCronJobStore`]) and its Bend
//! model (`bend/cron.bend`, whose laws `PROOF.bend` proves): both run the
//! same scenarios and must print the same transcript, byte for byte.
//!
//! A scenario (`bridge/bridge_cron.bend` documents the format) runs three
//! simulated processes, each with its own store and owner identity, on one
//! jobs file, over a clock of minutes. The processes make jobs, claim the
//! due jobs, recover claims, finish their runs (good, failed, skipped),
//! unwind their passes, and die; the user cancels and resumes jobs; another
//! writer adds records the store cannot read; the file becomes corrupt.
//! After each event the driver prints the jobs file.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;
use std::path::Path;
use std::sync::{Arc, Mutex};

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};

use super::owner::ClaimOwner;
use super::state::read_jobs_state;
use super::{
    AgentCronJobStore, CreateAgentCronJobInput, CronJobsState, DispatchOutcome,
    DispatchResultOptions, RlmHeartbeatStatusUpdate, RlmHeartbeatUpdate, RunningDispatch,
};
use crate::cron::{parse_iso_millis, JobStatus};

use super::FAILURE_STOP_AFTER;

/// The clock's zero: minute 0 of every scenario.
const BASE: u64 = 1_700_000_000_000;

const MINUTE: u64 = 60_000;

/// The simulated processes of a scenario.
const PROCESSES: u64 = 3;

/// A case the scenarios must reach, so that the bridge checks every rule
/// of the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Case {
    /// A recovery keeps the claim of another live process.
    LiveClaimKept,
    /// A recovery clears the claim of a dead process.
    DeadClaimCleared,
    /// A recovery clears a process's own claim after its pass unwound.
    OwnClaimCleared,
    /// A one-shot finishes after its run.
    OnceFinished,
    /// A failed run backs the next run off.
    BackedOff,
    /// A job stops after its failures in a row reach the cap.
    Stopped,
    /// A resume restarts a stopped job.
    Resumed,
    /// An update keeps records the store cannot read.
    UnreadKept,
    /// An update moves a corrupt file aside.
    MovedAside,
}

type Reached = BTreeSet<Case>;

fn minutes(iso: &str) -> u64 {
    (parse_iso_millis(iso).expect("a stored time") - BASE) / MINUTE
}

/// The scenario's processes, jobs and clock.
struct World {
    path: std::path::PathBuf,
    dead: Arc<Mutex<HashSet<u32>>>,
    stores: Vec<AgentCronJobStore>,
    /// The runs of each process: the job (by model id) and its dispatch.
    running: Vec<Vec<(u64, RunningDispatch)>>,
    /// The store ids of the jobs, by model id.
    ids: Vec<String>,
    now: u64,
}

impl World {
    fn ms(&self) -> u64 {
        BASE + self.now * MINUTE
    }

    fn model_id(&self, id: &str) -> u64 {
        u64::try_from(
            self.ids
                .iter()
                .position(|known| known == id)
                .expect("a known job"),
        )
        .unwrap()
    }

    fn store_id(&self, model: u64) -> String {
        usize::try_from(model)
            .ok()
            .and_then(|at| self.ids.get(at))
            .cloned()
            .unwrap_or_else(|| "missing".to_string())
    }

    fn corrupt(&self) -> Option<u64> {
        let raw = std::fs::read_to_string(&self.path).ok()?;
        raw.strip_prefix("corrupt ")
            .map(|token| token.parse().expect("a corrupt token"))
    }

    /// The file as the store reads it (empty when corrupt).
    fn state(&self) -> CronJobsState {
        match self.corrupt() {
            Some(_) => CronJobsState::default(),
            None => read_jobs_state(&self.path),
        }
    }

    fn aside(&self) -> Vec<u64> {
        let mut tokens: Vec<u64> = std::fs::read_dir(self.path.parent().unwrap())
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| {
                path.file_name()
                    .unwrap()
                    .to_string_lossy()
                    .starts_with("cron-jobs.json.corrupt-")
            })
            .map(|path| {
                std::fs::read_to_string(path)
                    .unwrap()
                    .strip_prefix("corrupt ")
                    .expect("a corrupt file")
                    .parse()
                    .unwrap()
            })
            .collect();
        tokens.sort_unstable_by(|left, right| right.cmp(left));
        tokens
    }

    fn token(value: &serde_json::Value, key: &str) -> u64 {
        value[key].as_u64().expect("a raw token")
    }

    fn show(&self) -> String {
        let state = self.state();
        let claims: HashMap<&str, String> = state
            .dispatches
            .iter()
            .map(|claim| {
                (
                    claim.job_id.as_str(),
                    format!("{}@{}", minutes(&claim.scheduled_for), claim.owner.pid),
                )
            })
            .collect();
        let mut jobs: Vec<(u64, String)> = state
            .jobs
            .iter()
            .map(|job| {
                let status = match job.status {
                    JobStatus::Active => "a",
                    JobStatus::Paused => "p",
                    JobStatus::Completed => "f",
                    JobStatus::Cancelled => "c",
                };
                let next = job
                    .next_run_at
                    .as_deref()
                    .map_or_else(|| "-".to_string(), |next| minutes(next).to_string());
                let claim = claims
                    .get(job.id.as_str())
                    .cloned()
                    .unwrap_or_else(|| "-".to_string());
                let id = self.model_id(&job.id);
                (
                    id,
                    format!(" {id}:{status}:{next}:{}:{claim}", job.failure_streak),
                )
            })
            .collect();
        jobs.sort();
        let mut line = match self.corrupt() {
            Some(token) => format!("b {token} |"),
            None => "b - |".to_string(),
        };
        for (_, job) in jobs {
            line.push_str(&job);
        }
        line.push_str(" |");
        for raw in &state.unread_jobs {
            write!(line, " {}", Self::token(raw, "rawJob")).unwrap();
        }
        line.push_str(" |");
        for raw in &state.unread_dispatches {
            write!(line, " {}", Self::token(raw, "rawClaim")).unwrap();
        }
        line.push_str(" |");
        for token in self.aside() {
            write!(line, " {token}").unwrap();
        }
        line.push('\n');
        line
    }

    /// Another writer adds a record to the list `key` of a file it reads.
    fn add_raw(&self, key: &str, record: serde_json::Value) {
        if self.corrupt().is_some() {
            return;
        }
        let mut file: serde_json::Value = std::fs::read_to_string(&self.path).map_or_else(
            |_| serde_json::json!({"jobs": [], "dispatches": []}),
            |raw| serde_json::from_str(&raw).unwrap(),
        );
        file[key].as_array_mut().unwrap().push(record);
        std::fs::write(&self.path, file.to_string()).unwrap();
    }

    fn input(&self, schedule_text: String) -> CreateAgentCronJobInput {
        CreateAgentCronJobInput {
            active_session_id: "live".to_string(),
            session_id: "session".to_string(),
            session_file: "/w/session.jsonl".to_string(),
            cwd: "/w".to_string(),
            prompt: "tick".to_string(),
            schedule_text,
            now: Some(self.ms()),
            ..Default::default()
        }
    }
}

/// The result of a run.
#[derive(Clone, Copy)]
enum Run {
    Good,
    Failed,
    Skipped,
}

/// One event of the scenario.
#[derive(Clone, Copy)]
enum Event {
    Create { p: u64, once: bool, d: u64 },
    Take { p: u64 },
    Recover { p: u64 },
    Finish { p: u64, job: u64, out: Run },
    Abort { p: u64 },
    Die { p: u64 },
    Cancel { p: u64, job: u64 },
    Resume { p: u64, job: u64 },
    Tick { d: u64 },
    RawJob { t: u64 },
    RawClaim { t: u64 },
    Corrupt { t: u64 },
}

impl Event {
    fn line(self) -> String {
        match self {
            Event::Create { p, once, d } => {
                format!("c {p} {} {d}\n", if once { "o" } else { "e" })
            }
            Event::Take { p } => format!("k {p}\n"),
            Event::Recover { p } => format!("v {p}\n"),
            Event::Finish { p, job, out } => {
                let out = match out {
                    Run::Good => "w",
                    Run::Failed => "l",
                    Run::Skipped => "s",
                };
                format!("f {p} {job} {out}\n")
            }
            Event::Abort { p } => format!("a {p}\n"),
            Event::Die { p } => format!("x {p}\n"),
            Event::Cancel { p, job } => format!("n {p} {job}\n"),
            Event::Resume { p, job } => format!("u {p} {job}\n"),
            Event::Tick { d } => format!("t {d}\n"),
            Event::RawJob { t } => format!("r {t}\n"),
            Event::RawClaim { t } => format!("q {t}\n"),
            Event::Corrupt { t } => format!("z {t}\n"),
        }
    }

    fn actor(self) -> Option<u64> {
        match self {
            Event::Create { p, .. }
            | Event::Take { p }
            | Event::Recover { p }
            | Event::Finish { p, .. }
            | Event::Abort { p }
            | Event::Cancel { p, .. }
            | Event::Resume { p, .. } => Some(p),
            Event::Die { .. }
            | Event::Tick { .. }
            | Event::RawJob { .. }
            | Event::RawClaim { .. }
            | Event::Corrupt { .. } => None,
        }
    }
}

fn pid(p: u64) -> u32 {
    u32::try_from(p).unwrap()
}

/// Run one event on the Rust stores and note the cases it reaches.
fn apply(world: &mut World, event: Event, reached: &mut Reached) {
    if event
        .actor()
        .is_some_and(|p| world.dead.lock().unwrap().contains(&pid(p)))
    {
        return;
    }
    let before = world.state();
    let aside_before = world.aside().len();
    let unread_before = before.unread_jobs.len() + before.unread_dispatches.len();
    let ms = world.ms();
    let at = |p: u64| usize::try_from(p).unwrap();
    match event {
        Event::Create { p, once, d } => {
            let store = &world.stores[at(p)];
            let job = if once {
                store.create(&world.input(format!("in {}m", d + 1)))
            } else {
                store.create_rlm_heartbeat(&world.input(format!("every {}m", d + 1)))
            }
            .expect("a job is made");
            world.ids.push(job.id);
        }
        Event::Take { p } => {
            let claimed = world.stores[at(p)].claim_due(ms, ms).unwrap();
            for running in claimed {
                let job = world.model_id(&running.dispatch().job.id);
                world.running[at(p)].push((job, running));
            }
        }
        Event::Recover { p } => {
            world.stores[at(p)]
                .recover_interrupted_dispatches(ms)
                .unwrap();
            let after = world.state();
            let dead = world.dead.lock().unwrap().clone();
            for claim in &before.dispatches {
                let kept = after.dispatches.contains(claim);
                let owner = u64::from(claim.owner.pid);
                reached.insert(match (owner == p, dead.contains(&claim.owner.pid), kept) {
                    (false, false, true) => Case::LiveClaimKept,
                    (false, true, false) => Case::DeadClaimCleared,
                    (true, false, false) => Case::OwnClaimCleared,
                    (false | true, false | true, false | true) => continue,
                });
            }
        }
        Event::Finish { p, job, out } => {
            let (outcome, error) = match out {
                Run::Good => (DispatchOutcome::Ran, None),
                Run::Failed => (DispatchOutcome::Ran, Some("boom".to_string())),
                Run::Skipped => (DispatchOutcome::Skipped, None),
            };
            let runs = &mut world.running[at(p)];
            let run = runs
                .iter()
                .position(|(run_job, _)| *run_job == job)
                .map(|found| runs.remove(found).1);
            let id = run
                .as_ref()
                .map_or_else(|| "none".to_string(), |run| run.dispatch().id.clone());
            let updated = world.stores[at(p)]
                .record_dispatch_result(
                    &id,
                    &DispatchResultOptions {
                        now: Some(ms),
                        outcome,
                        error,
                    },
                )
                .unwrap();
            drop(run);
            if let Some(updated) = updated {
                let case = match updated.status {
                    JobStatus::Completed => Some(Case::OnceFinished),
                    JobStatus::Paused => {
                        (updated.failure_streak == FAILURE_STOP_AFTER).then_some(Case::Stopped)
                    }
                    JobStatus::Active => (updated.failure_streak > 0).then_some(Case::BackedOff),
                    JobStatus::Cancelled => None,
                };
                reached.extend(case);
            }
        }
        Event::Abort { p } => world.running[at(p)].clear(),
        Event::Die { p } => {
            world.dead.lock().unwrap().insert(pid(p));
            world.running[at(p)].clear();
        }
        Event::Cancel { p, job } => {
            world.stores[at(p)]
                .cancel(&world.store_id(job), ms)
                .unwrap();
        }
        Event::Resume { p, job } => {
            let paused = before
                .jobs
                .iter()
                .any(|found| found.id == world.store_id(job) && found.status == JobStatus::Paused);
            // A job that cannot resume (a one-shot, a finished job) answers
            // an error or nothing; the model leaves it as it is too.
            let resumed = world.stores[at(p)].update_rlm_heartbeat(
                "live",
                &world.store_id(job),
                &RlmHeartbeatUpdate {
                    status: Some(RlmHeartbeatStatusUpdate::Resume),
                    now: Some(ms),
                    ..Default::default()
                },
            );
            if paused && matches!(resumed, Ok(Some(_))) {
                reached.insert(Case::Resumed);
            }
        }
        Event::Tick { d } => world.now += d,
        Event::RawJob { t } => world.add_raw("jobs", serde_json::json!({ "rawJob": t })),
        Event::RawClaim { t } => world.add_raw("dispatches", serde_json::json!({ "rawClaim": t })),
        Event::Corrupt { t } => std::fs::write(&world.path, format!("corrupt {t}")).unwrap(),
    }
    if world.aside().len() > aside_before {
        reached.insert(Case::MovedAside);
    }
    let after = world.state();
    if unread_before > 0
        && after != before
        && after.unread_jobs.len() + after.unread_dispatches.len() >= unread_before
    {
        reached.insert(Case::UnreadKept);
    }
}

/// The events of one scenario: random steps, or (one in four) a job that
/// keeps failing until it stops, then a resume.
fn events(rng: &mut Rng) -> Vec<Event> {
    let mut events = Vec::new();
    let mut token = 0;
    let mut next_token = || {
        token += 1;
        token
    };
    if rng.chance(25) {
        events.push(Event::Create {
            p: 0,
            once: false,
            d: rng.range(0, 3),
        });
        for _ in 0..rng.range(8, 11) {
            events.push(Event::Tick { d: 61 });
            events.push(Event::Take { p: 0 });
            if rng.chance(15) {
                events.push(Event::RawJob { t: next_token() });
            }
            events.push(Event::Finish {
                p: 0,
                job: 0,
                out: Run::Failed,
            });
        }
        events.push(Event::Resume { p: 1, job: 0 });
        events.push(Event::Tick { d: 5 });
        events.push(Event::Take { p: 1 });
        events.push(Event::Finish {
            p: 1,
            job: 0,
            out: Run::Good,
        });
        // A claim of a process that dies, recovered by another.
        events.push(Event::Tick { d: 61 });
        events.push(Event::Take { p: 0 });
        events.push(Event::Die { p: 0 });
        events.push(Event::Recover { p: 1 });
        return events;
    }
    let mut made = 0;
    for _ in 0..rng.range(15, 50) {
        let p = rng.below(PROCESSES);
        let job = rng.below(made + 1);
        let event = match rng.below(100) {
            0..=11 => {
                made += 1;
                Event::Create {
                    p,
                    once: rng.chance(40),
                    d: rng.range(0, 4),
                }
            }
            12..=31 => Event::Take { p },
            32..=41 => Event::Recover { p },
            42..=59 => Event::Finish {
                p,
                job,
                out: [Run::Good, Run::Failed, Run::Failed, Run::Skipped]
                    [usize::try_from(rng.below(4)).unwrap()],
            },
            60..=64 => Event::Abort { p },
            65..=67 => Event::Die { p },
            68..=72 => Event::Cancel { p, job },
            73..=76 => Event::Resume { p, job },
            77..=89 => Event::Tick { d: rng.range(0, 6) },
            90..=93 => Event::RawJob { t: next_token() },
            94..=96 => Event::RawClaim { t: next_token() },
            _ => Event::Corrupt { t: next_token() },
        };
        events.push(event);
    }
    events
}

/// One scenario: its events and the Rust transcript.
fn scenario(dir: &Path, rng: &mut Rng, reached: &mut Reached) -> (String, String) {
    let path = dir.join("cron-jobs.json");
    let dead = Arc::new(Mutex::new(HashSet::new()));
    let mut world = World {
        stores: (0..PROCESSES)
            .map(|p| {
                AgentCronJobStore::with_owner(path.clone(), ClaimOwner::simulated(pid(p), &dead))
            })
            .collect(),
        running: (0..PROCESSES).map(|_| Vec::new()).collect(),
        path,
        dead,
        ids: Vec::new(),
        now: 0,
    };
    let mut lines = String::new();
    let mut transcript = String::new();
    for event in events(rng) {
        lines.push_str(&event.line());
        apply(&mut world, event, reached);
        transcript.push_str(&world.show());
    }
    (lines, transcript)
}

#[test]
fn the_rust_cron_store_equals_the_bend_model() {
    let mut rng = Rng(0x00c0_70b5);
    let mut reached = Reached::new();
    let mut scenarios = Vec::new();
    for at in 0..120 {
        let dir = tempfile::tempdir().unwrap();
        let (events, transcript) = scenario(dir.path(), &mut rng, &mut reached);
        scenarios.push(Scenario {
            name: at.to_string(),
            events,
            transcript,
        });
    }
    assert_eq!(
        reached,
        Reached::from([
            Case::LiveClaimKept,
            Case::DeadClaimCleared,
            Case::OwnClaimCleared,
            Case::OnceFinished,
            Case::BackedOff,
            Case::Stopped,
            Case::Resumed,
            Case::UnreadKept,
            Case::MovedAside,
        ]),
        "the scenarios reach every case"
    );
    compare("bridge/bridge_cron.bend", scenarios);
}
