//! The bridge between the jobs ([`super::Job`], [`super::wait_until`],
//! [`super::JobTable::rewind`]) and their Bend model (`bend/job.bend`,
//! whose laws `PROOF.bend` proves): both run the same scenarios and must
//! print the same transcript, byte for byte.
//!
//! A scenario (`bend/bridge_job.bend` documents the format) gives one job
//! its output cap (or the opt-out) and a blocking wait its budget, then
//! feeds the job its events: output, an exit, the kill, a tick of time
//! (the paused tokio clock moves one millisecond). After each event the
//! driver prints the job, the ends the table's writer got, and the wait's
//! answer. Then it fills a job table with running and ended jobs and
//! rewinds it to the jobs a target tree holds, and prints the table.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::time::Duration;

use eukhe_durable::harness::{OutputLimits, Truncation};
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::job::JobId;
use futures::FutureExt;

use super::tree::JobRecord;
use super::{wait_until, Job, JobEnd, JobEvent, JobKind, JobSpec, JobState, JobTable, Wait};

/// The largest slot id of a scenario.
const SLOT_IDS: u64 = 10;

/// A case the scenarios must reach, so that the bridge checks every rule
/// of the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Case {
    /// A capped job drops output.
    Truncation,
    /// An uncapped job keeps output.
    OptOut,
    /// A kill ends a job.
    Kill,
    /// An exit ends a job.
    Quit,
    /// An ended job sees another event.
    AfterEnd,
    /// The wait detaches at its budget.
    Detach,
    /// The wait settles within its budget.
    Settle,
    /// A rewind stops a running job.
    RewindStop,
    /// A rewind keeps a running job.
    RewindKeep,
}

/// The cases the scenarios reached.
type Reached = BTreeSet<Case>;

fn show_end(end: JobEnd) -> String {
    match end {
        JobEnd::Exited(code) => format!("exited:{code}"),
        JobEnd::Killed => "killed".to_owned(),
    }
}

/// A job whose kill ends it at once, as a killed process does.
fn start(table: &JobTable, id: &str, truncation: Truncation) -> Job {
    table.start(JobSpec {
        id: JobId::new(id).expect("a bridge job id"),
        kind: JobKind::UserBash,
        label: String::new(),
        truncation,
        written: 0,
        kill: Box::new(|job| {
            job.record(JobEvent::Killed);
        }),
    })
}

/// One scenario: its events and the Rust transcript.
async fn scenario(rng: &mut Rng, reached: &mut Reached) -> (String, String) {
    let mut events = String::new();
    let mut transcript = String::new();
    let cap = (!rng.chance(25)).then(|| rng.range(0, 40));
    let budget = rng.range(0, 6);
    match cap {
        Some(cap) => writeln!(events, "c {cap}").unwrap(),
        None => events.push_str("c -\n"),
    }
    writeln!(events, "b {budget}").unwrap();
    let truncation = cap.map_or(Truncation::Off, |cap| {
        Truncation::On(OutputLimits {
            max_bytes: usize::try_from(cap).unwrap(),
            ..OutputLimits::default()
        })
    });

    let table = JobTable::default();
    let mut queue = table.take_queue().expect("a new table has its queue");
    let job = start(&table, "job", truncation);
    let mut wait = Box::pin(wait_until(
        tokio::time::Instant::now() + Duration::from_millis(budget),
        job.ended(),
    ));
    let mut answer: Option<Wait<JobEnd>> = None;
    for _ in 0..rng.range(3, 16) {
        let ended_before = !job.is_running();
        match rng.below(100) {
            0..=44 => {
                let bytes = rng.range(0, 15);
                writeln!(events, "o {bytes}").unwrap();
                job.record(JobEvent::Output(bytes));
            }
            45..=69 => {
                events.push_str("t\n");
                tokio::time::advance(Duration::from_millis(1)).await;
            }
            70..=84 => {
                let code = rng.range(0, 3);
                writeln!(events, "q {code}").unwrap();
                job.record(JobEvent::Exited(i64::try_from(code).unwrap()));
            }
            _ => {
                events.push_str("k\n");
                job.kill();
            }
        }
        if ended_before {
            reached.insert(Case::AfterEnd);
        }
        let mut ends = String::new();
        while let Ok(record) = queue.try_recv() {
            match record {
                JobRecord::Start { .. } => {}
                JobRecord::End { end, .. } => {
                    reached.insert(match end {
                        JobEnd::Exited(_) => Case::Quit,
                        JobEnd::Killed => Case::Kill,
                    });
                    write!(ends, " {}", show_end(end)).unwrap();
                }
            }
        }
        if answer.is_none() {
            answer = (&mut wait).now_or_never();
        }
        let state = job.state();
        let shown = match state {
            JobState::Live { kept, dropped } => format!("live {kept} {dropped}"),
            JobState::Ended { kept, dropped, end } => {
                format!("{} {kept} {dropped}", show_end(end))
            }
        };
        let (JobState::Live { kept, dropped } | JobState::Ended { kept, dropped, .. }) = state;
        if dropped > 0 && cap.is_some() {
            reached.insert(Case::Truncation);
        }
        if kept > 0 && cap.is_none() {
            reached.insert(Case::OptOut);
        }
        let waited = match answer {
            None => "none".to_owned(),
            Some(Wait::Detached) => {
                reached.insert(Case::Detach);
                "detached".to_owned()
            }
            Some(Wait::Settled(end)) => {
                reached.insert(Case::Settle);
                show_end(end)
            }
        };
        writeln!(transcript, "j {shown} e{ends} w {waited}").unwrap();
    }
    drop(wait);

    // The job table at a rewind.
    let slots = JobTable::default();
    let mut ids: Vec<u64> = (1..=SLOT_IDS).collect();
    for _ in 0..rng.range(0, 8) {
        let id = ids.remove(usize::try_from(rng.below(ids.len() as u64)).unwrap());
        let running = rng.chance(60);
        writeln!(events, "s {id} {}", u8::from(running)).unwrap();
        let slot = start(&slots, &id.to_string(), Truncation::default());
        if !running {
            slot.record(JobEvent::Exited(0));
        }
    }
    for _ in 0..rng.range(1, 2) {
        let keep: Vec<u64> = (1..=SLOT_IDS).filter(|_| rng.chance(40)).collect();
        events.push('r');
        for id in &keep {
            write!(events, " {id}").unwrap();
        }
        events.push('\n');
        let held = |id: &JobId| keep.iter().any(|kept| kept.to_string() == id.as_str());
        let running_kept = slots
            .jobs()
            .iter()
            .any(|job| job.is_running() && held(job.id()));
        if running_kept {
            reached.insert(Case::RewindKeep);
        }
        if !slots.rewind(|job| held(job.id())).is_empty() {
            reached.insert(Case::RewindStop);
        }
        transcript.push('r');
        for job in slots.jobs() {
            write!(transcript, " {}:{}", job.id(), u8::from(job.is_running())).unwrap();
        }
        transcript.push('\n');
    }
    (events, transcript)
}

#[tokio::test(start_paused = true)]
async fn the_rust_jobs_equal_the_bend_model() {
    let mut rng = Rng(0x5eed_70b5);
    let mut reached = Reached::new();
    let mut scenarios = Vec::new();
    for at in 0..300 {
        let (events, transcript) = scenario(&mut rng, &mut reached).await;
        scenarios.push(Scenario {
            name: at.to_string(),
            events,
            transcript,
        });
    }
    assert_eq!(
        reached,
        Reached::from([
            Case::Truncation,
            Case::OptOut,
            Case::Kill,
            Case::Quit,
            Case::AfterEnd,
            Case::Detach,
            Case::Settle,
            Case::RewindStop,
            Case::RewindKeep,
        ]),
        "the scenarios reach every case"
    );
    compare("bend/bridge_job.bend", scenarios);
}
