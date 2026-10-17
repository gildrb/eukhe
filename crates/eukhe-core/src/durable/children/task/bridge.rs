//! The bridge between the child task's decisions and their Bend model
//! (`step` in `bend/child.bend`, whose laws `PROOF.bend` proves): both run
//! the same generated events and must print the same transcript, byte for
//! byte. The Rust side runs the task's own decisions: [`watched_next`]
//! after a watch poll, [`report_step`] in the report phase, and
//! [`owed_on_abort`] with [`OwedReport::checkpoint`] at an abort. Around
//! them it keeps the parent as the harness does: every submission of the
//! report by its ordinal (a known request id finds its submission), a run
//! placing a queued one, an abort, a close or a withdrawal of one input
//! withdrawing queued ones, each settling once, and a closing parent
//! admitting none. `bend/bridge_report.bend` documents the format;
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::fmt::Write as _;
use std::time::Duration;

use eukhe_durable::testing::bridge::{compare, Rng, Scenario};
use eukhe_durable::types::{EntryId, InputSubmission, SubmissionState, SubmissionStatus};

use super::super::registry::ChildDeletion;
use super::{
    owed_on_abort, report_ordinal, report_step, watched_next, ChildCheckpoint, ChildFailure,
    ChildReport, ChildRow, ChildStatus, Fate, NextTaskState, Poll, ReportStep, TaskId, Vigil,
    Watched,
};

/// The child task's id.
const CHILD: u64 = 7;
/// The stall budget in ms: the bridge's busy polls always show progress.
const STALL_MS: u32 = 100_000;

/// What a task step's poll reads in the watch phase.
#[derive(Clone, Copy)]
enum Obs {
    /// Unsettled, with this new progress token.
    Busy(u64),
    /// Answered, through an agent message (`replied`) or not.
    Answered { replied: bool },
    /// Failed.
    Broke,
}

/// The task the bridge runs, and its parent.
struct Sim {
    /// The task's checkpoint; `None` once it ended.
    phase: Option<ChildCheckpoint>,
    /// A pending abort of the task: `Some(delete)`.
    mark: Option<bool>,
    row: ChildRow,
    /// The parent is open (not closing).
    open: bool,
    /// The parent's submissions of the report by ordinal, oldest first.
    inbox: Vec<(u32, SubmissionState)>,
    /// Transcript entries placed so far.
    entries: u64,
}

impl Sim {
    fn new() -> Self {
        Self {
            phase: Some(ChildCheckpoint::Watch {
                poll: 0,
                next_poll_at: 0.0,
                vigil: Vigil::default(),
            }),
            mark: None,
            row: ChildRow {
                task_id: CHILD,
                rlm_child_id: "child".to_owned(),
                session_id: "child-session".to_owned(),
                session_name: "child".to_owned(),
                label: "child".to_owned(),
                started_at: 0.0,
                status: ChildStatus::Running,
                active_session_id: None,
                session_dir: None,
                model: None,
                answer_preview: None,
                error: None,
                replied_since_task: false,
                deletion: None,
                settled: false,
                usage: None,
                progress: None,
                reporter: None,
                handback: None,
            },
            open: true,
            inbox: Vec::new(),
            entries: 0,
        }
    }

    /// The newest ordinal the inbox holds (0: none).
    fn newest(&self) -> u32 {
        self.inbox.last().map_or(0, |(ordinal, _)| *ordinal)
    }

    /// A task step: the abort a pending mark runs, else the phase's next
    /// move; a watch-phase poll reads `obs`.
    fn step(&mut self, obs: Obs) {
        if let Some(delete) = self.mark.take() {
            // The abort reads the row as the delete left it.
            self.row.deletion = delete.then_some(ChildDeletion::Requested);
            self.phase = self
                .phase
                .as_ref()
                .and_then(|checkpoint| {
                    owed_on_abort(checkpoint, TaskId::from_number(CHILD), &self.row)
                })
                .map(|owed| owed.checkpoint());
            return;
        }
        self.phase = match self.phase.take() {
            None => None,
            Some(ChildCheckpoint::Watch { poll, vigil, .. }) => {
                let watched = match obs {
                    Obs::Busy(token) => Watched::of(
                        vigil.judge(
                            Poll::Unsettled {
                                progress: Some(token),
                            },
                            1.0,
                            f64::from(STALL_MS),
                        ),
                        Duration::from_millis(u64::from(STALL_MS)),
                        None,
                    ),
                    Obs::Answered { replied } => {
                        self.row.replied_since_task = replied;
                        Watched::Answered {
                            answer_preview: None,
                        }
                    }
                    Obs::Broke => Watched::Failed {
                        failure: ChildFailure::Aborted,
                        error: "the child's run failed".to_owned(),
                    },
                };
                match watched_next(watched, poll, 0.0, &mut self.row) {
                    NextTaskState::Running { checkpoint } => Some(checkpoint),
                    NextTaskState::Waiting { .. } | NextTaskState::Terminal { .. } => None,
                }
            }
            Some(ChildCheckpoint::Report { report, withdrawn }) => {
                let ordinal = report_ordinal(withdrawn);
                let fate = self
                    .inbox
                    .iter()
                    .find(|(known, _)| *known == ordinal)
                    .map(|(_, state)| Fate::of(state, ()));
                match report_step(withdrawn, fate) {
                    ReportStep::Submit(ordinal) => {
                        if self.open {
                            self.inbox
                                .push((ordinal, SubmissionState::Input(InputSubmission::Queued)));
                        }
                        Some(ChildCheckpoint::Report { report, withdrawn })
                    }
                    ReportStep::Wait(()) => Some(ChildCheckpoint::Report { report, withdrawn }),
                    ReportStep::Again(withdrawn) => {
                        Some(ChildCheckpoint::Report { report, withdrawn })
                    }
                    ReportStep::Done => None,
                }
            }
            Some(checkpoint @ (ChildCheckpoint::Spawn | ChildCheckpoint::Prompt)) => {
                Some(checkpoint)
            }
        };
    }

    /// The parent's run places submission `id` if it is queued; a settled
    /// one stays as it is.
    fn place(&mut self, id: u32) {
        let Self { inbox, entries, .. } = self;
        for (ordinal, state) in inbox {
            if *ordinal == id && state.status() == SubmissionStatus::Queued {
                *entries += 1;
                *state = SubmissionState::Input(InputSubmission::Placed {
                    entry: EntryId::from_number(*entries),
                });
            }
        }
    }

    /// The parent withdraws the queued submissions `hit` picks; a settled
    /// one stays as it is (a withdrawal that loses to a placement).
    fn withdraw(&mut self, hit: impl Fn(u32) -> bool) {
        for (ordinal, state) in &mut self.inbox {
            if hit(*ordinal) && state.status() == SubmissionStatus::Queued {
                *state = SubmissionState::Input(InputSubmission::Unanswered {
                    entry: None,
                    reason: "withdrawn".to_owned(),
                    detail: None,
                });
            }
        }
    }

    fn show(&self, out: &mut String) {
        let letter = |report: &ChildReport| match report {
            ChildReport::CompletedWithoutReply { .. } => 'C',
            ChildReport::Cancelled { .. } => 'X',
            ChildReport::Failed {
                failure: Some(ChildFailure::Stalled),
                ..
            } => 'S',
            ChildReport::Failed {
                failure: Some(ChildFailure::Unreachable),
                ..
            } => 'U',
            ChildReport::Failed { .. } => 'F',
        };
        match &self.phase {
            None => out.push('E'),
            Some(ChildCheckpoint::Watch { .. }) => out.push('W'),
            Some(ChildCheckpoint::Report { report, withdrawn }) => {
                write!(out, "O{}{}", letter(report), report_ordinal(*withdrawn)).unwrap();
            }
            Some(ChildCheckpoint::Spawn | ChildCheckpoint::Prompt) => out.push('?'),
        }
        let mark = match self.mark {
            None => '-',
            Some(false) => 'c',
            Some(true) => 'd',
        };
        write!(out, " {mark} {}", if self.open { 'o' } else { 'x' }).unwrap();
        for (ordinal, state) in self.inbox.iter().rev() {
            let fate = match Fate::of(state, ()) {
                Fate::Queued(()) => 'q',
                Fate::Withdrawn => 'w',
                Fate::Placed => 'p',
            };
            write!(out, " {ordinal}:{fate}").unwrap();
        }
        out.push('\n');
    }
}

/// One scenario of `events` events: its lines, for the model, and what
/// the Rust task printed.
fn scenario(seed: u64, events: usize) -> (String, String) {
    let mut rng = Rng(seed);
    let mut sim = Sim::new();
    let mut token = 0;
    let (mut lines, mut transcript) = (String::new(), String::new());
    for _ in 0..events {
        // Ids around the ones the inbox holds, one past them, and 0.
        let id = u32::try_from(rng.range(0, u64::from(sim.newest()) + 1)).unwrap();
        match rng.range(1, 100) {
            1..=40 => {
                let (kind, obs) = match rng.range(0, 9) {
                    0..=5 => {
                        token += 1;
                        (0, Obs::Busy(token))
                    }
                    6 => (1, Obs::Answered { replied: false }),
                    7 => (2, Obs::Answered { replied: true }),
                    _ => (3, Obs::Broke),
                };
                writeln!(lines, "0 {kind} {token}").unwrap();
                sim.step(obs);
            }
            41..=55 => {
                writeln!(lines, "1 {id}").unwrap();
                sim.place(id);
            }
            56..=62 => {
                writeln!(lines, "2 {id}").unwrap();
                sim.withdraw(|ordinal| ordinal == id);
            }
            63..=72 => {
                lines.push_str("3\n");
                sim.withdraw(|_| true);
            }
            73..=79 => {
                lines.push_str("4\n");
                sim.withdraw(|_| true);
                sim.open = false;
            }
            80..=90 => {
                lines.push_str("5\n");
                sim.open = true;
            }
            _ => {
                let delete = rng.range(0, 1) == 1;
                writeln!(lines, "6 {}", u8::from(delete)).unwrap();
                sim.mark = Some(sim.mark.unwrap_or(false) || delete);
            }
        }
        sim.show(&mut transcript);
    }
    (lines, transcript)
}

/// Whether an event and the state after it reach a path.
type Reaches = fn(&str, &str) -> bool;

#[test]
fn the_rust_report_rule_equals_the_bend_model() {
    // The paths the scenarios must reach, on an event and the state after
    // it: a delete's handed-on report, a resubmission placed, a placed
    // submission an abort cannot withdraw, a report owed while closing.
    let paths: [(&str, Reaches); 4] = [
        ("a delete's report", |_, state| state.starts_with("OX")),
        ("a resubmission placed", |_, state| state.contains(" 2:p")),
        ("an abort after a placement", |event, state| {
            event == "3" && state.contains(":p")
        }),
        ("a report owed while closing", |_, state| {
            state.starts_with('O') && state.contains(" x")
        }),
    ];
    let mut reached = [false; 4];
    let scenarios: Vec<Scenario> = (1..=300)
        .map(|seed| {
            let (events, transcript) = scenario(seed, 80);
            for (event, state) in events.lines().zip(transcript.lines()) {
                for ((_, on), seen) in paths.iter().zip(&mut reached) {
                    *seen |= on(event, state);
                }
            }
            Scenario {
                name: seed.to_string(),
                events,
                transcript,
            }
        })
        .collect();
    compare("bend/bridge_report.bend", scenarios);
    for ((path, _), seen) in paths.iter().zip(reached) {
        assert!(seen, "no scenario reached {path}");
    }
}
