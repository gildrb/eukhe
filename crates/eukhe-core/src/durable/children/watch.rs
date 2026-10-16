//! The watch's verdict on one poll of a child (rule H5,
//! `docs/harness.md`): a pure function of the watch's clock and what the
//! poll read. `bend/child.bend` models it (`look`), `LAWS.bend` states
//! what it guarantees (a child with no progress is reported within
//! `subagentStallMs`, failed polls within [`CHILD_POLL_FAILURES`], a child
//! that progresses never), and the bridge test runs both on the same
//! scenarios.

use serde::{Deserialize, Serialize};

#[cfg(test)]
mod bridge;

/// Failed polls in a row that report a child unreachable.
pub(crate) const CHILD_POLL_FAILURES: u32 = 5;

/// The watch's clock on one child, kept in its checkpoint.
#[derive(Debug, Clone, Copy, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Vigil {
    /// The child's progress token at the last poll that read one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) progress: Option<u64>,
    /// How long the child has shown no progress, in ms.
    #[serde(default)]
    pub(crate) quiet_ms: f64,
    /// Failed polls in a row.
    #[serde(default)]
    pub(crate) failures: u32,
}

/// What one poll read, as far as the clock is concerned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Poll {
    /// The child is unsettled (running, or idle with background jobs),
    /// with its progress token when the host read one.
    Unsettled { progress: Option<u64> },
    /// The poll got no answer.
    Failed,
}

/// The verdict on one poll.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum Verdict {
    /// Watch on with this clock.
    Watch(Vigil),
    /// No progress for the stall budget: stop the child, report it stalled.
    Stalled,
    /// [`CHILD_POLL_FAILURES`] failed polls in a row: report it unreachable.
    Unreachable,
}

impl Vigil {
    /// The verdict on `poll`, which ended `elapsed_ms` after the last one,
    /// for a child that may show no progress for `stall_ms`. A new token
    /// is progress: the clock starts over. Anything else adds the time to
    /// the quiet time; a failed poll also counts toward unreachable.
    pub(crate) fn judge(self, poll: Poll, elapsed_ms: f64, stall_ms: f64) -> Verdict {
        let quiet = |failures| {
            let quiet_ms = self.quiet_ms + elapsed_ms;
            if quiet_ms >= stall_ms {
                Verdict::Stalled
            } else {
                Verdict::Watch(Vigil {
                    quiet_ms,
                    failures,
                    ..self
                })
            }
        };
        match poll {
            Poll::Unsettled {
                progress: Some(token),
            } if self.progress != Some(token) => Verdict::Watch(Vigil {
                progress: Some(token),
                quiet_ms: 0.0,
                failures: 0,
            }),
            Poll::Unsettled { .. } => quiet(0),
            Poll::Failed => match self.failures.saturating_add(1) {
                failures if failures >= CHILD_POLL_FAILURES => Verdict::Unreachable,
                failures => quiet(failures),
            },
        }
    }
}
