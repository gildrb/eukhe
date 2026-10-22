//! The D1 bridges: the supervisor's decision code and its Bend models
//! (`LAWS.bend` section `supervisor`, proved in `PROOF.bend` section `supervisor`) run the
//! same scenarios and must print the same transcript, byte for byte.
//!
//! - [`RestartBudget`] and the timeouts against `bend/bridge_supervise.bend`.
//! - [`busy_evidence_fresh`] on the refresh schedule against
//!   `bend/bridge_revive.bend`.
//! - [`exit_due`] and [`orphan_exit`] against `bend/bridge_orphan.bend`.
//! - [`WorkGate`], [`idle_shutdown_commits`] and [`adoption_verdict`]
//!   against `bend/bridge_launcher.bend`.
//!
//! Each `bend/bridge_*.bend` file documents its events and its output.
//! [`compare`] runs them (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;
use std::time::{Duration, Instant};

use eukhe_core::kernel::shared::{
    HOST_REQUEST_SHUTDOWN_TIMEOUT_MS, KERNEL_KILL_VERIFY_MS, KERNEL_SHUTDOWN_TIMEOUT_MS,
    KERNEL_TEARDOWN_TOTAL_MS, KERNEL_TERM_GRACE_MS, SNAPSHOT_EXECUTION_TIMEOUT_MS,
};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::daemon::timing::{
    CLIENT_RELAUNCH_WITHIN_MS, DAEMON_STARTUP_TIMEOUT_MS, WORKER_LOST_EXIT_DEFAULT_MS,
    WORKER_LOST_EXIT_SLACK_MS, WORKER_SUPERVISOR_CHECK_MS,
};

use crate::revival_gate::busy_evidence_fresh;
use crate::supervisor::adoption::{adoption_verdict, Adoption};
use crate::supervisor::restart_budget::{RestartBudget, RestartVerdict};
use crate::supervisor_lost::exit_due;
use crate::timeouts::{
    BUSY_REFRESH_MS, HARNESS_CLOSE_MS, LAUNCHER_DRAIN_MARGIN_MS, LAUNCHER_SHUTDOWN_WAIT_MS,
    QUIESCE_ANSWER_MS, QUIESCE_HOLD_MS, RESTART_BASE_BACKOFF_MS, RESTART_CRASH_LOOP_MS,
    RESTART_GIVE_UP_AFTER, RESTART_MAX_BACKOFF_MS, RESTART_WINDOW_MS, REVIVAL_BOOT_WINDOW_MS,
    REVIVAL_BUSY_EVIDENCE_MAX_AGE_MS, RLM_CHILD_KILL_TIMEOUT_MS, STOP_GRACE_MS,
    SUPERVISOR_DRAIN_MS, WORKER_KILL_VERIFY_MS, WORKER_TERM_GRACE_MS,
};
use crate::work_gate::{
    idle_shutdown_commits, orphan_exit, Admission, OrphanExit, QuiesceAnswer, Work, WorkGate,
};

/// The restart model counts time in steps of this many ms (every restart
/// constant is a multiple of it), so the model's numbers stay small.
const RESTART_UNIT_MS: u64 = 250;

/// The revival model counts time in seconds.
const REVIVE_UNIT_MS: u64 = 1_000;

fn units(ms: u64, unit: u64) -> u64 {
    assert_eq!(ms % unit, 0, "{ms} ms is not a multiple of {unit} ms");
    ms / unit
}

/// One restart scenario: a failure after each gap (in units).
fn restart_scenario(rng: &mut Rng) -> (String, String) {
    let window = units(RESTART_WINDOW_MS, RESTART_UNIT_MS);
    let mut events = format!(
        "c {RESTART_GIVE_UP_AFTER} {window} {} {}\n",
        units(RESTART_BASE_BACKOFF_MS, RESTART_UNIT_MS),
        units(RESTART_MAX_BACKOFF_MS, RESTART_UNIT_MS)
    );
    let mut transcript = String::new();
    let mut budget = RestartBudget::default();
    let base = Instant::now();
    let mut at = 0u64;
    let mut over = false;
    for _ in 0..rng.range(1, 12) {
        let gap = match rng.below(4) {
            0 => rng.range(0, 4),
            1 => rng.range(100, 700),
            2 => rng.range(window - 2, window + 2),
            _ => rng.range(0, window / 2),
        };
        writeln!(events, "f {gap}").unwrap();
        at += gap;
        if over {
            continue;
        }
        let now = base + Duration::from_millis(at * RESTART_UNIT_MS);
        match budget.on_failure(now) {
            RestartVerdict::Relaunch { failure, backoff } => {
                let pause = units(u64::try_from(backoff.as_millis()).unwrap(), RESTART_UNIT_MS);
                writeln!(transcript, "r {failure} {pause}").unwrap();
            }
            RestartVerdict::GiveUp { failures } => {
                writeln!(transcript, "x {failures}").unwrap();
                over = true;
            }
        }
    }
    (events, transcript)
}

/// The timeouts' base values and the derived values, as the Rust
/// constants hold them.
fn timeouts_scenario() -> (String, String) {
    let events = format!(
        "t {SNAPSHOT_EXECUTION_TIMEOUT_MS} {HOST_REQUEST_SHUTDOWN_TIMEOUT_MS} {KERNEL_SHUTDOWN_TIMEOUT_MS} {KERNEL_TERM_GRACE_MS} {KERNEL_KILL_VERIFY_MS} {HARNESS_CLOSE_MS} {WORKER_TERM_GRACE_MS} {WORKER_KILL_VERIFY_MS} {LAUNCHER_DRAIN_MARGIN_MS} {BUSY_REFRESH_MS} {REVIVAL_BOOT_WINDOW_MS} {CLIENT_RELAUNCH_WITHIN_MS} {DAEMON_STARTUP_TIMEOUT_MS} {WORKER_SUPERVISOR_CHECK_MS} {WORKER_LOST_EXIT_SLACK_MS} {RESTART_GIVE_UP_AFTER} {RESTART_MAX_BACKOFF_MS} {RESTART_CRASH_LOOP_MS} {QUIESCE_ANSWER_MS}\n"
    );
    let transcript = format!(
        "t {KERNEL_TEARDOWN_TOTAL_MS} {STOP_GRACE_MS} {SUPERVISOR_DRAIN_MS} {LAUNCHER_SHUTDOWN_WAIT_MS} {RLM_CHILD_KILL_TIMEOUT_MS} {WORKER_LOST_EXIT_DEFAULT_MS} {REVIVAL_BUSY_EVIDENCE_MAX_AGE_MS} {QUIESCE_HOLD_MS} {RESTART_WINDOW_MS}\n"
    );
    (events, transcript)
}

/// The restart budget on crash loops, rare crashes and window edges; the
/// timeouts as derived.
#[test]
fn the_supervisor_runs_as_its_model() {
    let mut rng = Rng(0x5eed_d1a1);
    let mut events = String::new();
    let mut transcript = String::new();
    for _ in 0..60 {
        let (e, t) = restart_scenario(&mut rng);
        events.push_str(&e);
        transcript.push_str(&t);
    }
    let (e, t) = timeouts_scenario();
    events.push_str(&e);
    transcript.push_str(&t);
    compare(
        "bend/bridge_supervise.bend",
        [Scenario {
            name: "restarts and timeouts".to_owned(),
            events,
            transcript,
        }],
    );
}

/// Runs of any length, crashes anywhere, boots near the boot window's
/// edge: a busy worker records at its run start and then every refresh.
#[test]
fn the_revival_runs_as_its_model() {
    let mut rng = Rng(0x0de1_7a11);
    let refresh = units(BUSY_REFRESH_MS, REVIVE_UNIT_MS);
    let boot = units(REVIVAL_BOOT_WINDOW_MS, REVIVE_UNIT_MS);
    let start_ms = 1_700_000_000_000u64;
    let mut events = String::new();
    let mut transcript = String::new();
    for _ in 0..80 {
        let crash = match rng.below(3) {
            0 => rng.range(0, refresh * 2),
            1 => rng.range(0, 12 * 60 * 60),
            _ => refresh * rng.range(1, 30) + rng.range(0, 2) - 1,
        };
        // The edge of the max age too: the evidence one second younger,
        // exactly as old, and one second older.
        let delay = match rng.below(3) {
            0 => rng.range(boot.saturating_sub(refresh), boot + refresh),
            1 => refresh + boot - crash % refresh + rng.range(0, 2) - 1,
            _ => rng.range(0, boot * 2),
        };
        writeln!(events, "v {refresh} {boot} {crash} {delay}").unwrap();
        let last_record_ms = start_ms + (crash / refresh) * refresh * REVIVE_UNIT_MS;
        let boot_ms = start_ms + (crash + delay) * REVIVE_UNIT_MS;
        let fresh = busy_evidence_fresh(last_record_ms, boot_ms);
        writeln!(transcript, "v {}", u8::from(fresh)).unwrap();
    }
    compare(
        "bend/bridge_revive.bend",
        [Scenario {
            name: "long runs".to_owned(),
            events,
            transcript,
        }],
    );
}

/// The orphan worker: a run, queued inputs, a compaction, the absence.
#[derive(Default)]
struct Orphan {
    run: bool,
    queued: u64,
    compacting: bool,
    absent: u64,
}

impl Orphan {
    fn work(&self) -> Work {
        if self.run || self.compacting || self.queued > 0 {
            Work::Ongoing
        } else {
            Work::Idle
        }
    }
}

fn orphan_scenario(rng: &mut Rng) -> Scenario {
    let window = rng.range(5, 40);
    let mut events = format!("w {window}\n");
    let mut worker = Orphan::default();
    let mut end = "live\n".to_owned();
    for _ in 0..rng.range(1, 25) {
        match rng.below(8) {
            0 => {
                events.push_str("s\n");
                worker.run = true;
            }
            1 => {
                events.push_str("e\n");
                worker.run = false;
            }
            2 => {
                events.push_str("q\n");
                worker.queued += 1;
            }
            3 => {
                events.push_str("d\n");
                worker.queued = worker.queued.saturating_sub(1);
            }
            4 => {
                events.push_str("c\n");
                worker.compacting = true;
            }
            5 => {
                events.push_str("k\n");
                worker.compacting = false;
            }
            6 => {
                let gone = rng.range(0, 30);
                writeln!(events, "g {gone}").unwrap();
                worker.absent += gone;
            }
            _ => {
                events.push_str("b\n");
                worker.absent = 0;
            }
        }
        let work = worker.work();
        if end == "live\n"
            && exit_due(
                Duration::from_millis(worker.absent),
                Duration::from_millis(window),
                work,
            )
        {
            let (how, busy, aborted) = match orphan_exit(work) {
                OrphanExit::Close => ("shut", 0, u8::from(work == Work::Ongoing)),
                OrphanExit::Handover => ("handover", 1, 0),
            };
            end = format!("x {how} {busy} {aborted}\n");
        }
    }
    Scenario {
        name: format!("orphan window {window}"),
        events,
        transcript: end,
    }
}

/// Any events on a worker whose supervisor is lost.
#[test]
fn the_orphan_exit_runs_as_its_model() {
    let mut rng = Rng(0x0a7f_a11e);
    let scenarios: Vec<Scenario> = (0..60).map(|_| orphan_scenario(&mut rng)).collect();
    compare("bend/bridge_orphan.bend", scenarios);
}

fn bits(items: &[(bool, WorkGate)], pick: impl Fn(&(bool, WorkGate)) -> bool) -> String {
    items
        .iter()
        .map(|item| if pick(item) { '1' } else { '0' })
        .collect()
}

/// One operation of a replacement scenario.
#[derive(Clone, Copy)]
enum Op {
    Prompt,
    Finish,
    Quiesce,
    Release,
    Commit,
}

fn replacement_scenario(rng: &mut Rng) -> Scenario {
    let count = rng.range(1, 4);
    let mut workers: Vec<(bool, WorkGate)> = (0..count)
        .map(|_| (rng.chance(50), WorkGate::default()))
        .collect();
    let mut events = String::from("w");
    for (busy, _) in &workers {
        write!(events, " {}", u8::from(*busy)).unwrap();
    }
    events.push('\n');
    let mut transcript = String::new();
    let mut stopped = false;
    let mut aborted = 0u64;
    let ops = [Op::Prompt, Op::Finish, Op::Quiesce, Op::Release, Op::Commit];
    for _ in 0..rng.range(5, 30) {
        // One past the last worker too: the model and the code both
        // ignore an operation on a worker that does not exist.
        let index = rng.range(0, count);
        let op = rng.pick(&ops).unwrap();
        match op {
            Op::Prompt => writeln!(events, "p {index}").unwrap(),
            Op::Finish => writeln!(events, "f {index}").unwrap(),
            Op::Quiesce => writeln!(events, "q {index}").unwrap(),
            Op::Release => writeln!(events, "r {index}").unwrap(),
            Op::Commit => events.push_str("c\n"),
        }
        let worker = workers.get_mut(usize::try_from(index).unwrap());
        if !stopped {
            match (op, worker) {
                (Op::Prompt, Some((busy, gate))) => {
                    if gate.admission() == Admission::Open {
                        *busy = true;
                    }
                }
                (Op::Finish, Some((busy, _))) => *busy = false,
                (Op::Quiesce, Some((busy, gate))) => {
                    gate.quiesce(if *busy { Work::Ongoing } else { Work::Idle });
                }
                (Op::Release, Some((_, gate))) => gate.release(),
                (Op::Prompt | Op::Finish | Op::Quiesce | Op::Release, None) => {}
                (Op::Commit, _) => {
                    let answers = workers.iter().map(|(_, gate)| match gate.admission() {
                        Admission::Quiesced => QuiesceAnswer::Quiesced,
                        Admission::Open => QuiesceAnswer::Busy,
                    });
                    if idle_shutdown_commits(answers) {
                        aborted += workers.iter().filter(|(busy, _)| *busy).count() as u64;
                        stopped = true;
                    }
                }
            }
        }
        writeln!(
            transcript,
            "o {} {} {} {aborted}",
            bits(&workers, |(busy, _)| *busy),
            bits(&workers, |(_, gate)| gate.admission()
                == Admission::Quiesced),
            u8::from(stopped)
        )
        .unwrap();
    }
    for _ in 0..3 {
        let supervisor = rng.range(0, 3);
        let worker = rng.chance(80).then(|| rng.range(0, 3));
        let verdict = adoption_verdict(
            &format!("build-{supervisor}"),
            worker.map(|build| format!("build-{build}")).as_deref(),
        );
        let shown = worker.map_or_else(|| "-".to_owned(), |build| build.to_string());
        writeln!(events, "a {supervisor} {shown}").unwrap();
        let name = match verdict {
            Adoption::Adopt => "adopt",
            Adoption::Replace => "replace",
        };
        writeln!(transcript, "a {name}").unwrap();
    }
    Scenario {
        name: format!("replacement of {count} workers"),
        events,
        transcript,
    }
}

/// Prompts, run ends, quiesces, releases and commits in any order, and
/// adoptions of workers of any build.
#[test]
fn the_replacement_runs_as_its_model() {
    let mut rng = Rng(0x1d1e_5407);
    let scenarios: Vec<Scenario> = (0..60).map(|_| replacement_scenario(&mut rng)).collect();
    compare("bend/bridge_launcher.bend", scenarios);
}
