//! The bridge between the blocking wait on a job ([`super::wait_until`])
//! and its Bend model (`bend/job.bend` `wait`, whose laws `PROOF.bend`
//! proves): both run the same scenarios and must print the same
//! transcript, byte for byte. The compiled core decides each poll of the
//! wait (`poll`, entry `job_wait`) and each event of the job (`feed`, entry
//! `job`); what the bridge ties is the interleaving the laws do not see:
//! the tokio timer against the job's end.
//!
//! A scenario (`bridge/bridge_job.bend` documents the format) gives a
//! blocking wait its budget, then feeds the job its events: output, an
//! exit, the kill, a tick of time (the paused tokio clock moves one
//! millisecond). After each event the driver prints the wait's answer.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::time::Duration;

use eukhe_durable::harness::Truncation;
use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_types::job::JobId;
use futures::FutureExt;

use super::{wait_until, JobEnd, JobEvent, JobKind, JobSpec, JobTable, Wait};

/// A case the scenarios must reach, so that the bridge checks every way
/// the wait answers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Case {
    /// The wait detaches at its budget.
    Detach,
    /// The wait settles with an exit within its budget.
    SettleExit,
    /// The wait settles with the kill within its budget.
    SettleKill,
    /// The job ends after the wait detached.
    EndAfterDetach,
}

/// The cases the scenarios reached.
type Reached = BTreeSet<Case>;

fn show_end(end: JobEnd) -> String {
    match end {
        JobEnd::Exited(code) => format!("exited:{code}"),
        JobEnd::Killed => "killed".to_owned(),
    }
}

/// One scenario: its events and the Rust transcript.
async fn scenario(rng: &mut Rng, reached: &mut Reached) -> (String, String) {
    let mut events = String::new();
    let mut transcript = String::new();
    let budget = rng.range(0, 6);
    writeln!(events, "b {budget}").unwrap();

    let table = JobTable::default();
    // A job whose kill ends it at once, as a killed process does.
    let job = table.start(JobSpec {
        id: JobId::new("job").expect("a bridge job id"),
        kind: JobKind::UserBash,
        label: String::new(),
        truncation: Truncation::default(),
        written: 0,
        kill: Box::new(|job| {
            job.record(JobEvent::Killed);
        }),
    });
    let mut wait = Box::pin(wait_until(
        tokio::time::Instant::now() + Duration::from_millis(budget),
        job.ended(),
    ));
    let mut answer: Option<Wait<JobEnd>> = None;
    for _ in 0..rng.range(3, 16) {
        let running = job.is_running();
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
        if answer.is_none() {
            answer = (&mut wait).now_or_never();
        }
        let waited = match answer {
            None => "none".to_owned(),
            Some(Wait::Detached) => {
                reached.insert(Case::Detach);
                if running && !job.is_running() {
                    reached.insert(Case::EndAfterDetach);
                }
                "detached".to_owned()
            }
            Some(Wait::Settled(end)) => {
                reached.insert(match end {
                    JobEnd::Exited(_) => Case::SettleExit,
                    JobEnd::Killed => Case::SettleKill,
                });
                show_end(end)
            }
        };
        writeln!(transcript, "w {waited}").unwrap();
    }
    (events, transcript)
}

#[tokio::test(start_paused = true)]
async fn the_rust_wait_equals_the_bend_model() {
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
            Case::Detach,
            Case::SettleExit,
            Case::SettleKill,
            Case::EndAfterDetach,
        ]),
        "the scenarios reach every case"
    );
    compare("bridge/bridge_job.bend", scenarios);
}
