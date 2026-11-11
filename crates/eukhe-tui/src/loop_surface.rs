//! `/loop` view state: the `loop_update` surface. The status line's loop
//! label shows the iterations or time left and the stop condition, plus
//! the last check of the condition, so the user sees why the loop still
//! runs. Pure state and formatting; the status line owns the row.

use eukhe_types::loop_mode::{LoopCondition, LoopEvidence, LoopLimit, LoopPhase, LoopStatus};

/// The columns the condition part takes at most: a longer command is cut
/// with the ellipsis.
const CONDITION_MAX_WIDTH: usize = 40;

/// The status line's loop segment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoopLabel {
    pub text: String,
    /// A paused loop reads in the warning tone.
    pub paused: bool,
}

/// The loop's status-line label at `now_ms` (milliseconds since the
/// epoch): the phase, then the limit, the condition and the last check,
/// each when the loop has one. A session without a loop, or whose loop
/// ended, carries no label.
#[must_use]
pub fn tray_loop_label(status: &LoopStatus, now_ms: u64) -> Option<LoopLabel> {
    let state = &status.state;
    let phase = match state.phase {
        LoopPhase::Off | LoopPhase::Ended { .. } => return None,
        LoopPhase::Armed => "Loop: next prompt repeats",
        LoopPhase::Turn => "Loop running",
        LoopPhase::Judging => "Loop checking",
        LoopPhase::Paused => "Loop paused",
    };
    let mut parts = vec![phase.to_string()];
    parts.extend(limit_text(status, now_ms));
    parts.extend(state.condition.as_ref().map(condition_text));
    parts.extend(state.last_check.map(|check| check_text(check.evidence)));
    Some(LoopLabel {
        text: parts.join(" "),
        paused: state.phase == LoopPhase::Paused,
    })
}

/// `<remaining>/<initial>` of an iteration limit,
/// the time left of a duration.
fn limit_text(status: &LoopStatus, now_ms: u64) -> Option<String> {
    match status.limit? {
        LoopLimit::Iterations { iterations } => status
            .state
            .remaining
            .map(|remaining| format!("{remaining}/{iterations}")),
        LoopLimit::Duration { .. } => status
            .state
            .deadline_ms
            .map(|deadline| time_left(deadline.saturating_sub(now_ms))),
    }
}

/// `2h5m left`, `5m30s left`, `42s left`: the two largest units, a zero
/// smaller one dropped; a started second counts whole.
fn time_left(left_ms: u64) -> String {
    let total = left_ms.div_ceil(1_000);
    let (hours, minutes, seconds) = (total / 3_600, total % 3_600 / 60, total % 60);
    match (hours, minutes, seconds) {
        (0, 0, seconds) => format!("{seconds}s left"),
        (0, minutes, 0) => format!("{minutes}m left"),
        (0, minutes, seconds) => format!("{minutes}m{seconds}s left"),
        (hours, 0, _) => format!("{hours}h left"),
        (hours, minutes, _) => format!("{hours}h{minutes}m left"),
    }
}

/// `until: <command>` or `while: <command>`
/// on one line, the command cut to the part's width.
fn condition_text(condition: &LoopCondition) -> String {
    let label = if condition.until { "until" } else { "while" };
    let command = condition
        .command
        .split(|c: char| c.is_whitespace() || c.is_control())
        .filter(|word| !word.is_empty())
        .collect::<Vec<_>>()
        .join(" ");
    let room = CONDITION_MAX_WIDTH - label.len() - 2;
    format!(
        "{label}: {}",
        crate::goal_surface::truncate_plain(&command, room)
    )
}

/// What the last run of the condition command showed.
fn check_text(evidence: LoopEvidence) -> String {
    match evidence {
        LoopEvidence::Exited { code } => format!("last: exit {code}"),
        LoopEvidence::NoStatus => "last: no status".to_string(),
        LoopEvidence::TimedOut => "last: timed out".to_string(),
        LoopEvidence::SpawnFailed => "last: could not run".to_string(),
        LoopEvidence::Cancelled => "last: cancelled".to_string(),
    }
}

/// The session view's loop state: the current `loop_update` payload.
#[derive(Debug, Default)]
pub struct LoopView {
    pub status: LoopStatus,
}

impl LoopView {
    /// Seed the state from an attach snapshot (`state.loop`).
    pub fn seed(&mut self, status: LoopStatus) {
        self.status = status;
    }

    /// Apply one `loop_update`: `true` when the status changed.
    pub fn apply_update(&mut self, status: LoopStatus) -> bool {
        if self.status == status {
            return false;
        }
        self.status = status;
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::loop_mode::{LoopCheck, LoopEnd, LoopState};

    /// The clock of the table.
    const NOW: u64 = 1_000_000;

    fn status(phase: LoopPhase) -> LoopStatus {
        LoopStatus {
            state: LoopState {
                phase,
                iteration: 3,
                prompt: "fix it".to_string(),
                ..LoopState::default()
            },
            ..LoopStatus::default()
        }
    }

    fn counted(phase: LoopPhase, remaining: u64, iterations: u64) -> LoopStatus {
        let mut status = status(phase);
        status.state.remaining = Some(remaining);
        status.limit = Some(LoopLimit::Iterations { iterations });
        status
    }

    fn timed(left_ms: u64) -> LoopStatus {
        let mut status = status(LoopPhase::Turn);
        status.state.deadline_ms = Some(NOW + left_ms);
        status.limit = Some(LoopLimit::Duration {
            duration_ms: 7_200_000,
        });
        status
    }

    fn conditioned(phase: LoopPhase, command: &str, until: bool) -> LoopStatus {
        let mut status = status(phase);
        status.state.condition = Some(LoopCondition {
            command: command.to_string(),
            until,
        });
        status
    }

    fn checked(evidence: LoopEvidence) -> LoopStatus {
        let mut status = conditioned(LoopPhase::Turn, "test -f done", true);
        status.state.last_check = Some(LoopCheck {
            iteration: 2,
            evidence,
        });
        status
    }

    fn label(text: &str) -> Option<LoopLabel> {
        Some(LoopLabel {
            text: text.to_string(),
            paused: false,
        })
    }

    /// One row per phase, limit shape, condition shape and last check.
    #[test]
    fn the_label_table() {
        let mut full = counted(LoopPhase::Turn, 7, 10);
        full.state.condition = Some(LoopCondition {
            command: "test -f done".to_string(),
            until: true,
        });
        full.state.last_check = Some(LoopCheck {
            iteration: 2,
            evidence: LoopEvidence::Exited { code: 1 },
        });
        let overdue = {
            let mut status = timed(0);
            status.state.deadline_ms = Some(NOW - 5_000);
            status
        };
        let table = [
            // No loop, or one that ended: no label.
            (status(LoopPhase::Off), None),
            (
                status(LoopPhase::Ended {
                    end: LoopEnd::Satisfied,
                }),
                None,
            ),
            // The phases.
            (status(LoopPhase::Armed), label("Loop: next prompt repeats")),
            (status(LoopPhase::Turn), label("Loop running")),
            (status(LoopPhase::Judging), label("Loop checking")),
            (
                status(LoopPhase::Paused),
                Some(LoopLabel {
                    text: "Loop paused".to_string(),
                    paused: true,
                }),
            ),
            // An iteration limit: remaining of initial.
            (
                counted(LoopPhase::Armed, 10, 10),
                label("Loop: next prompt repeats 10/10"),
            ),
            (counted(LoopPhase::Turn, 7, 10), label("Loop running 7/10")),
            // A duration: the time left, a started second counted whole.
            (timed(7_500_000), label("Loop running 2h5m left")),
            (timed(7_200_000), label("Loop running 2h left")),
            (timed(330_000), label("Loop running 5m30s left")),
            (timed(300_000), label("Loop running 5m left")),
            (timed(41_001), label("Loop running 42s left")),
            (overdue, label("Loop running 0s left")),
            // The condition, by polarity; a long command is cut and a
            // multi-line one reads on one line.
            (
                conditioned(LoopPhase::Judging, "test -f done", true),
                label("Loop checking until: test -f done"),
            ),
            (
                conditioned(LoopPhase::Turn, "pgrep  -f\n\tserver", false),
                label("Loop running while: pgrep -f server"),
            ),
            (
                conditioned(
                    LoopPhase::Turn,
                    "cargo test --workspace --all-targets -- --nocapture",
                    true,
                ),
                label("Loop running until: cargo test --workspace --all-t..."),
            ),
            // The last check.
            (
                checked(LoopEvidence::Exited { code: 1 }),
                label("Loop running until: test -f done last: exit 1"),
            ),
            (
                checked(LoopEvidence::NoStatus),
                label("Loop running until: test -f done last: no status"),
            ),
            (
                checked(LoopEvidence::TimedOut),
                label("Loop running until: test -f done last: timed out"),
            ),
            (
                checked(LoopEvidence::SpawnFailed),
                label("Loop running until: test -f done last: could not run"),
            ),
            (
                checked(LoopEvidence::Cancelled),
                label("Loop running until: test -f done last: cancelled"),
            ),
            // Everything at once: limit, condition, last check.
            (
                full,
                label("Loop running 7/10 until: test -f done last: exit 1"),
            ),
        ];
        for (status, expected) in table {
            assert_eq!(tray_loop_label(&status, NOW), expected, "{status:?}");
        }
    }

    /// A `loop_update` replaces the status the label reads; the same
    /// status again changes nothing; an attach seed is the baseline.
    #[test]
    fn an_update_replaces_the_status() {
        let mut view = LoopView::default();
        assert_eq!(tray_loop_label(&view.status, NOW), None);
        assert!(!view.apply_update(LoopStatus::default()));

        let running = counted(LoopPhase::Turn, 7, 10);
        assert!(view.apply_update(running.clone()));
        assert_eq!(view.status, running);
        assert_eq!(
            tray_loop_label(&view.status, NOW),
            label("Loop running 7/10")
        );
        assert!(!view.apply_update(running));

        let ended = status(LoopPhase::Ended {
            end: LoopEnd::OutOfTurns,
        });
        assert!(view.apply_update(ended.clone()));
        assert_eq!(view.status, ended);
        assert_eq!(tray_loop_label(&view.status, NOW), None);

        let paused = status(LoopPhase::Paused);
        view.seed(paused.clone());
        assert!(!view.apply_update(paused));
    }
}
