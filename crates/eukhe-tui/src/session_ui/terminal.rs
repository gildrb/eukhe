//! The terminal status concern: what this view reports to the terminal
//! (`crate::terminal_status`) -- the session's state, how its latest run
//! ended, the running subagents, and the progress setting.

use super::{AgentView, SessionUi};
use crate::terminal_status::{blocked, first_line, run_end, RunEnd, State, TerminalProgress};

impl SessionUi {
    /// The session's state for the terminal: a panel waiting on the user,
    /// a run in progress (named by its prompt's first line), the latest
    /// run's end while the user has not pressed a key since
    /// (`seen_run_ends`: [`Self::run_ends`] at that key), else idle.
    pub(crate) fn terminal_state<'a>(
        &'a self,
        view: &'a AgentView,
        seen_run_ends: u64,
    ) -> State<'a> {
        if let Some(waiting) = blocked(view) {
            return waiting;
        }
        let runs = self.turn_active
            || self.run_open
            || view.working.is_some()
            || view.compaction.is_some()
            || view.retry.is_some();
        if runs {
            return State::Working {
                msg: self.last_user_text.as_deref().and_then(first_line),
            };
        }
        match &self.last_run_end {
            Some(end) if self.run_ends > seen_run_ends => end.state(),
            Some(_) | None => State::Idle,
        }
    }

    /// Runs this view saw end.
    pub(crate) fn run_ends(&self) -> u64 {
        self.run_ends
    }

    /// How the latest run this view saw ended.
    pub(crate) fn last_run_end(&self) -> Option<&RunEnd> {
        self.last_run_end.as_ref()
    }

    /// Changes each time the pinned agents block is rebuilt.
    pub(crate) fn family_generation(&self) -> u64 {
        self.family_generation
    }

    /// `terminal.showTerminalProgress`.
    pub(crate) fn terminal_progress(&self) -> TerminalProgress {
        self.terminal_progress
    }

    /// A run ended: how, from `stop` and the rows it left.
    pub(super) fn record_run_end(&mut self, stop: RunStop, view: &AgentView) {
        self.run_ends += 1;
        self.last_run_end = Some(match stop {
            RunStop::Interrupted => RunEnd::Interrupted,
            RunStop::Ended => run_end(&view.chat),
        });
    }
}

/// Whether this client stopped the run that ended.
#[derive(Debug, Clone, Copy)]
pub(super) enum RunStop {
    Interrupted,
    Ended,
}
