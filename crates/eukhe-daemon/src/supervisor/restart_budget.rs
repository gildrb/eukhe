//! The restart budget of one worker: the failures inside the restart
//! window, on the monotonic clock. A failure past the budget gives the
//! worker up; any other failure relaunches it after a pause that doubles
//! with each failure in the window. The model is bend/supervise.bend; the
//! law `restart_gives_up` (LAWS.bend, D1) proves that a crash loop always
//! reaches the give-up.

use std::collections::VecDeque;
use std::time::{Duration, Instant};

use crate::timeouts::{
    RESTART_BASE_BACKOFF_MS, RESTART_GIVE_UP_AFTER, RESTART_MAX_BACKOFF_MS, RESTART_WINDOW_MS,
};

/// What the supervisor does after a worker failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RestartVerdict {
    /// Relaunch after `backoff`; `failure` failures (this one included)
    /// are in the window.
    Relaunch { failure: u32, backoff: Duration },
    /// More than [`RESTART_GIVE_UP_AFTER`] failures are in the window.
    GiveUp { failures: u32 },
}

/// The failures of one worker inside the restart window, oldest first.
#[derive(Debug, Default)]
pub(crate) struct RestartBudget {
    failures: VecDeque<Instant>,
}

impl RestartBudget {
    /// Count a failure at `now` (a monotonic instant, never earlier than
    /// the failure before it) and decide what follows.
    pub(crate) fn on_failure(&mut self, now: Instant) -> RestartVerdict {
        let window = Duration::from_millis(RESTART_WINDOW_MS);
        while self
            .failures
            .front()
            .is_some_and(|failed| now.saturating_duration_since(*failed) >= window)
        {
            self.failures.pop_front();
        }
        self.failures.push_back(now);
        let failures = u32::try_from(self.failures.len()).unwrap_or(u32::MAX);
        if failures > RESTART_GIVE_UP_AFTER {
            return RestartVerdict::GiveUp { failures };
        }
        let doublings = (failures - 1).min(7);
        let backoff_ms = (RESTART_BASE_BACKOFF_MS << doublings).min(RESTART_MAX_BACKOFF_MS);
        RestartVerdict::Relaunch {
            failure: failures,
            backoff: Duration::from_millis(backoff_ms),
        }
    }

    /// Forget every failure (a client reopened the worker: a new start).
    pub(crate) fn clear(&mut self) {
        self.failures.clear();
    }
}
