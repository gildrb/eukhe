//! The run loop's edge to the terminal status reports
//! (`crate::terminal_status`): reads the session each iteration, writes
//! only the reports that change what the terminal holds, and leaves the
//! terminal as the exit needs.

use crate::clipboard::OscSink;
use crate::session_ui::SessionUi;
use crate::terminal_status::{child_records, Family, Leave, Reporter};
use crate::view::AgentView;

pub(super) struct StatusLink {
    reporter: Reporter,
    /// Stdout in the terminal, a captured buffer in headless runs.
    sink: OscSink,
    /// [`SessionUi::run_ends`] at the user's latest key: a run that ended
    /// after it is unread.
    seen_run_ends: u64,
    /// The pinned agents block generation the reporter last read.
    family_generation: Option<u64>,
}

impl StatusLink {
    pub(super) fn new(sink: OscSink) -> Self {
        StatusLink {
            reporter: Reporter::default(),
            sink,
            seen_run_ends: 0,
            family_generation: None,
        }
    }

    /// Bring the terminal to the session's state now.
    pub(super) fn sync(&mut self, session: &SessionUi, view: &AgentView) -> std::io::Result<()> {
        let generation = session.family_generation();
        let family = if self.family_generation == Some(generation) {
            Family::Unchanged
        } else {
            self.family_generation = Some(generation);
            Family::Now(child_records(&view.agents_panel.agents))
        };
        let state = session.terminal_state(view, self.seen_run_ends);
        let (reporter, out) =
            std::mem::take(&mut self.reporter).step(state, family, session.terminal_progress());
        self.reporter = reporter;
        if out.is_empty() {
            Ok(())
        } else {
            self.sink.write_sequence(&out)
        }
    }

    /// The user pressed a key, pasted or submitted: every run that ended
    /// so far is read.
    pub(super) fn user_acted(&mut self, session: &SessionUi) {
        self.seen_run_ends = session.run_ends();
    }

    /// Leave the terminal as `leave` needs; the headless capture of every
    /// report this run wrote.
    pub(super) fn leave(mut self, leave: Leave<'_>) -> std::io::Result<Vec<String>> {
        let out = std::mem::take(&mut self.reporter).leave(leave);
        if !out.is_empty() {
            self.sink.write_sequence(&out)?;
        }
        Ok(self.sink.captured())
    }
}
