//! What one agent is doing, typed: the working indicator's one vocabulary.
//!
//! [`TurnPhase`] names where a running turn is, from the user's Enter until
//! the turn ends. [`AgentActivity`] adds what a session is between turns:
//! parked on a provider usage reset, or still running background work.
//! [`AgentActivity::indicator`] is the one mapping a surface renders: the
//! root session's row above the composer, and any per-agent live panel the
//! same way (build an [`AgentActivity`] per agent, render its indicator).

use std::time::Instant;

use crate::chat::format_working_elapsed;
use crate::glyphs::{DASH, SEP};

/// The phase of one agent's turn, from the user's Enter until it ends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TurnPhase {
    /// The prompt left the composer; the daemon has not admitted it yet.
    Sending,
    /// The daemon admitted the prompt; its run has not started yet (the
    /// turn prepares, or waits behind another run).
    Queued,
    /// The link to the session's worker dropped mid-turn; the client is
    /// re-attaching.
    Reconnecting,
    /// The request is out and no token has arrived yet.
    Requesting,
    /// The model streams its reasoning.
    Thinking,
    /// The model streams its answer.
    Writing,
    /// The model streams a tool call's arguments.
    WritingCode,
    /// A tool call runs.
    RunningTool,
    /// The context is being compacted.
    Compacting,
    /// A provider failure waits for its retry, or the turn re-routes to a
    /// backup model.
    Retrying,
}

impl TurnPhase {
    /// The phase's label on the working indicator.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Self::Sending => "Sending",
            Self::Queued => "Queued",
            Self::Reconnecting => "Reconnecting",
            Self::Requesting => "Waiting",
            Self::Thinking => "Thinking",
            Self::Writing => "Writing",
            Self::WritingCode => "Writing code",
            Self::RunningTool => "Executing",
            Self::Compacting => "Compacting",
            Self::Retrying => "Retrying",
        }
    }
}

/// A session parked until its provider's usage resets (the session
/// summary's `quotaPark`): no turn runs, and the session resumes on its
/// own at `resume_at`.
pub use eukhe_types::daemon::QuotaPark;

/// The work a session waits on between turns (the session summary's
/// `waitingOn`): each one's end wakes the session into another turn.
pub use eukhe_types::daemon::{WaitingJob, WaitingOn};

/// What one agent is doing at a glance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AgentActivity {
    /// A turn runs: its phase, and when it started (the user's Enter, or
    /// the run's start when another client or a wake started it).
    Working { phase: TurnPhase, since: Instant },
    /// No turn runs: the session waits for its provider's usage reset.
    Parked(QuotaPark),
    /// No turn runs, but the session waits on work whose end wakes it
    /// (its jobs, its subagents, its workflow runs): it is not done.
    Waiting(WaitingOn),
    /// No turn runs, but `tasks` background tasks do (subagents, workflow
    /// runs, shells, factory runs).
    Background { tasks: usize },
    /// Nothing runs.
    Idle,
}

/// What the indicator shows for one [`AgentActivity`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Indicator {
    /// The indicator text.
    pub text: String,
    /// Whether work runs (the indicator animates); a parked session waits.
    pub busy: bool,
}

impl AgentActivity {
    /// The indicator for this activity at `now` (`now_ms`: the wall clock
    /// in Unix milliseconds, for a park's countdown); `None` when idle.
    #[must_use]
    pub fn indicator(&self, now: Instant, now_ms: u64) -> Option<Indicator> {
        match self {
            Self::Working { phase, since } => Some(Indicator {
                text: format!(
                    "{}{SEP}{}",
                    phase.label(),
                    format_working_elapsed(now.saturating_duration_since(*since).as_secs())
                ),
                busy: true,
            }),
            Self::Parked(park) => Some(Indicator {
                text: park_label(park, now_ms),
                busy: false,
            }),
            Self::Waiting(waiting) => Some(Indicator {
                text: waiting_label(waiting, now_ms),
                busy: true,
            }),
            Self::Background { tasks } => Some(Indicator {
                text: format!(
                    "{tasks} background {} running",
                    if *tasks == 1 { "task" } else { "tasks" }
                ),
                busy: true,
            }),
            Self::Idle => None,
        }
    }
}

/// `Parked until <time> UTC (<countdown>): <provider> usage limit -- ...`.
#[must_use]
pub fn park_label(park: &QuotaPark, now_ms: u64) -> String {
    let until = crate::heartbeats_picker::format_timestamp(&park.resume_at);
    let countdown = crate::heartbeats_picker::next_run_label(Some(&park.resume_at), now_ms);
    let limit = match &park.provider {
        Some(provider) => format!("{provider} usage limit"),
        None => "provider usage limit".to_string(),
    };
    format!(
        "Parked until {until} UTC ({countdown}): {limit} {DASH} resumes automatically; /model switches models now"
    )
}

/// What a job runs and for how long: `<label>, <elapsed>` (each part only
/// when known); `None` when neither is.
#[must_use]
pub fn job_detail(job: &WaitingJob, now_ms: u64) -> Option<String> {
    let elapsed = job
        .started_at_ms
        .map(|start| format_working_elapsed(now_ms.saturating_sub(start) / 1_000));
    let parts: Vec<String> = [(!job.label.is_empty()).then(|| job.label.clone()), elapsed]
        .into_iter()
        .flatten()
        .collect();
    (!parts.is_empty()).then(|| parts.join(", "))
}

/// ` (<detail>)` of [`job_detail`], or nothing.
fn job_suffix(job: &WaitingJob, now_ms: u64) -> String {
    job_detail(job, now_ms).map_or_else(String::new, |detail| format!(" ({detail})"))
}

/// The between-turns wording of what a session waits on: the agreed
/// [`WaitingOn::label`], its job part naming the longest-running job's
/// label and elapsed time.
#[must_use]
pub fn waiting_label(waiting: &WaitingOn, now_ms: u64) -> String {
    match waiting
        .longest_running_job()
        .and_then(|job| job_detail(job, now_ms))
    {
        Some(detail) => waiting.label_with_job_detail(SEP, &detail),
        None => waiting.label(SEP),
    }
}

/// The row under a running turn's loader while its tool call waits on a
/// job: `Waiting on job <id> (<label>, <elapsed>)`.
#[must_use]
pub fn waited_job_label(job: &WaitingJob, now_ms: u64) -> String {
    format!("Waiting on job {}{}", job.id, job_suffix(job, now_ms))
}

/// The row under a running turn's loader while the session's jobs run:
/// `<n> jobs running (<label>, <elapsed>)` of the longest-running job;
/// `None` when none runs.
#[must_use]
pub fn running_jobs_label(waiting: &WaitingOn, now_ms: u64) -> Option<String> {
    let longest = waiting.longest_running_job()?;
    let count = waiting.jobs.len();
    Some(format!(
        "{count} {} running{}",
        if count == 1 { "job" } else { "jobs" },
        job_suffix(longest, now_ms)
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    /// Every phase, each with the label its indicator shows. The match is
    /// exhaustive: a new phase fails to compile here until it has a label
    /// and a place in this table.
    #[test]
    fn every_phase_maps_to_its_indicator() {
        let started = Instant::now();
        let now = started + Duration::from_secs(65);
        let phases = [
            TurnPhase::Sending,
            TurnPhase::Queued,
            TurnPhase::Reconnecting,
            TurnPhase::Requesting,
            TurnPhase::Thinking,
            TurnPhase::Writing,
            TurnPhase::WritingCode,
            TurnPhase::RunningTool,
            TurnPhase::Compacting,
            TurnPhase::Retrying,
        ];
        for phase in phases {
            let label = match phase {
                TurnPhase::Sending => "Sending",
                TurnPhase::Queued => "Queued",
                TurnPhase::Reconnecting => "Reconnecting",
                TurnPhase::Requesting => "Waiting",
                TurnPhase::Thinking => "Thinking",
                TurnPhase::Writing => "Writing",
                TurnPhase::WritingCode => "Writing code",
                TurnPhase::RunningTool => "Executing",
                TurnPhase::Compacting => "Compacting",
                TurnPhase::Retrying => "Retrying",
            };
            assert_eq!(
                AgentActivity::Working {
                    phase,
                    since: started
                }
                .indicator(now, 0),
                Some(Indicator {
                    text: format!("{label} - 1m 05s"),
                    busy: true,
                }),
                "{phase:?}"
            );
        }
    }

    /// Between turns: a park names its wake time, its countdown, and its
    /// provider and never reads as idle; the work a session waits on is
    /// named in the agreed wording (ASCII separator); background work
    /// counts; an idle agent shows nothing.
    #[test]
    fn between_turns_the_indicator_names_parks_and_background_work() {
        let now = Instant::now();
        // 2026-10-23T14:05:00Z, two days after `now_ms`.
        let resume_ms = 1_792_764_300_000;
        let now_ms = resume_ms - 2 * 24 * 3_600_000;
        let parked = AgentActivity::Parked(QuotaPark {
            resume_at: "2026-10-23T14:05:00.000Z".to_string(),
            provider: Some("anthropic".to_string()),
        });
        let cases = [
            (
                parked,
                Some(Indicator {
                    text: "Parked until 2026-10-23 14:05 UTC (in 2d): anthropic usage limit -- resumes automatically; /model switches models now".to_string(),
                    busy: false,
                }),
            ),
            (
                AgentActivity::Waiting(WaitingOn {
                    jobs: vec![job("j1", "sleep 45", Some(now_ms - 723_000))],
                    subagents: 2,
                    ..WaitingOn::default()
                }),
                Some(Indicator {
                    text: "waiting on job j1 (sleep 45, 12m 03s) - 2 subagents".to_string(),
                    busy: true,
                }),
            ),
            (
                AgentActivity::Waiting(WaitingOn {
                    jobs: vec![job("j1", "sleep 45", None)],
                    ..WaitingOn::default()
                }),
                Some(Indicator {
                    text: "waiting on job j1 (sleep 45)".to_string(),
                    busy: true,
                }),
            ),
            (
                AgentActivity::Background { tasks: 1 },
                Some(Indicator {
                    text: "1 background task running".to_string(),
                    busy: true,
                }),
            ),
            (
                AgentActivity::Background { tasks: 3 },
                Some(Indicator {
                    text: "3 background tasks running".to_string(),
                    busy: true,
                }),
            ),
            (AgentActivity::Idle, None),
        ];
        for (activity, expected) in cases {
            match &activity {
                AgentActivity::Working { .. } => unreachable!("covered by the phase table"),
                AgentActivity::Parked(_)
                | AgentActivity::Waiting(_)
                | AgentActivity::Background { .. }
                | AgentActivity::Idle => {}
            }
            assert_eq!(activity.indicator(now, now_ms), expected, "{activity:?}");
        }
    }

    fn job(id: &str, label: &str, started_at_ms: Option<u64>) -> WaitingJob {
        WaitingJob {
            id: eukhe_types::job::JobId::new(id).expect("a job id"),
            kind: eukhe_types::daemon::WaitingJobKind::Cell,
            label: label.to_string(),
            started_at_ms,
        }
    }

    /// The rows under a running turn's loader: the job its tool call
    /// waits on, else the count of running jobs with the longest-running
    /// one's label and elapsed time; nothing when no job runs.
    #[test]
    fn a_running_turn_names_its_jobs() {
        let now_ms = 10_000_000;
        assert_eq!(
            waited_job_label(&job("cell-7", "train model", Some(now_ms - 42_000)), now_ms),
            "Waiting on job cell-7 (train model, 42s)"
        );
        assert_eq!(
            waited_job_label(&job("cell-7", "", None), now_ms),
            "Waiting on job cell-7"
        );
        let cases = [
            (vec![], None),
            (
                vec![job("cell-1", "train model", Some(now_ms - 723_000))],
                Some("1 job running (train model, 12m 03s)"),
            ),
            (
                vec![
                    job("cell-1", "fetch", Some(now_ms - 5_000)),
                    job("shell-2", "cargo test", Some(now_ms - 65_000)),
                ],
                Some("2 jobs running (cargo test, 1m 05s)"),
            ),
        ];
        for (jobs, expected) in cases {
            let waiting = WaitingOn {
                jobs,
                ..WaitingOn::default()
            };
            assert_eq!(
                running_jobs_label(&waiting, now_ms).as_deref(),
                expected,
                "{waiting:?}"
            );
        }
    }
}
