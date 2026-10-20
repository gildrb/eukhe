//! The `/workflows` page: one panel per dynamic workflow run of the
//! session (newest first) -- its name, size, agent counts, phases with
//! their agents, and log tail -- on the activity pages' keyset: the
//! arrows walk the agent rows, Enter opens the agents view, `c` asks to
//! cancel the selected row's running run (`y` confirms), Esc closes.
//!
//! The view is presentation and selection only: the session UI polls the
//! daemon's `workflow_activity` lane every 2 seconds while the page or
//! the dock shows, and runs the cancel through `workflow_cancel`.

use eukhe_types::workflow::{WorkflowAgentStatus, WorkflowRunSnapshot, WorkflowRunState};
use serde_json::Value;

use crate::keybindings::KeybindingsManager;
use crate::theme::Theme;
use crate::Line;

mod render;
#[cfg(test)]
mod tests;

/// The poll cadence of the page and the dock count (ms).
pub const WORKFLOW_REFRESH_MS: u64 = 2_000;

/// Parse the `workflow_activity` reply `{runs: [...]}`; `None` when the
/// reply has no runs list.
#[must_use]
pub fn parse_workflow_runs(data: &Value) -> Option<Vec<WorkflowRunSnapshot>> {
    let runs = data.get("runs")?.as_array()?;
    Some(
        runs.iter()
            .filter_map(|run| serde_json::from_value(run.clone()).ok())
            .collect(),
    )
}

/// Runs still running (the dock count).
#[must_use]
pub fn running_runs(runs: &[WorkflowRunSnapshot]) -> usize {
    runs.iter()
        .filter(|run| run.state == WorkflowRunState::Running)
        .count()
}

/// What a key press asks the session UI to do.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorkflowViewAction {
    None,
    /// Open the agents view (on an agent row).
    OpenAgents,
    /// Cancel the run (the confirmation was given).
    Cancel {
        run_id: String,
    },
    Close,
}

/// One selectable row: an agent of a run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Cursor {
    run: usize,
    agent: usize,
}

/// The page's state.
#[derive(Debug)]
pub struct WorkflowView {
    runs: Vec<WorkflowRunSnapshot>,
    /// The selected agent, by run id and ordinal, so a refresh keeps it.
    selected: Option<(String, u32)>,
    /// The run whose cancel waits for `y`.
    confirming: Option<String>,
    error: Option<String>,
    viewport_rows: usize,
}

impl WorkflowView {
    /// The page over `runs` (newest first), the first agent selected.
    #[must_use]
    pub fn new(runs: Vec<WorkflowRunSnapshot>, viewport_rows: usize) -> Self {
        let mut view = Self {
            runs,
            selected: None,
            confirming: None,
            error: None,
            viewport_rows,
        };
        view.selected = view.cursor_key(view.first_cursor());
        view
    }

    /// Apply a refreshed batch; the selection stays on the same agent.
    pub fn apply_runs(&mut self, runs: Vec<WorkflowRunSnapshot>) {
        self.runs = runs;
        if self.cursor().is_none() {
            self.selected = self.cursor_key(self.first_cursor());
        }
        if let Some(run_id) = &self.confirming {
            let running = self
                .runs
                .iter()
                .any(|run| &run.run_id == run_id && run.state == WorkflowRunState::Running);
            if !running {
                self.confirming = None;
            }
        }
    }

    /// The page's error line (a failed refresh or cancel).
    pub fn set_error(&mut self, error: Option<String>) {
        self.error = error.map(|text| crate::menu_panel::scrub_controls(&text));
    }

    /// The runs shown.
    #[must_use]
    pub fn runs(&self) -> &[WorkflowRunSnapshot] {
        &self.runs
    }

    fn cursors(&self) -> Vec<Cursor> {
        self.runs
            .iter()
            .enumerate()
            .flat_map(|(run, snapshot)| {
                (0..snapshot.agents.len()).map(move |agent| Cursor { run, agent })
            })
            .collect()
    }

    fn first_cursor(&self) -> Option<Cursor> {
        self.cursors().first().copied()
    }

    fn cursor_key(&self, cursor: Option<Cursor>) -> Option<(String, u32)> {
        let cursor = cursor?;
        let run = self.runs.get(cursor.run)?;
        let agent = run.agents.get(cursor.agent)?;
        Some((run.run_id.clone(), agent.ordinal))
    }

    fn cursor(&self) -> Option<Cursor> {
        let (run_id, ordinal) = self.selected.as_ref()?;
        let run = self.runs.iter().position(|run| &run.run_id == run_id)?;
        let agent = self.runs[run]
            .agents
            .iter()
            .position(|agent| agent.ordinal == *ordinal)?;
        Some(Cursor { run, agent })
    }

    fn selected_run(&self) -> Option<&WorkflowRunSnapshot> {
        self.cursor()
            .and_then(|cursor| self.runs.get(cursor.run))
            .or_else(|| self.runs.first())
    }

    fn step(&mut self, delta: isize) {
        let cursors = self.cursors();
        if cursors.is_empty() {
            return;
        }
        let current = self
            .cursor()
            .and_then(|cursor| cursors.iter().position(|candidate| *candidate == cursor))
            .unwrap_or(0);
        let last = cursors.len() - 1;
        let next = match delta {
            ..0 => current.saturating_sub(1),
            0 => current,
            1.. => (current + 1).min(last),
        };
        self.selected = self.cursor_key(Some(cursors[next]));
    }

    /// One key id.
    pub fn handle_key(&mut self, key: &str, kb: &KeybindingsManager) -> WorkflowViewAction {
        if let Some(run_id) = self.confirming.take() {
            if key == "y" {
                return WorkflowViewAction::Cancel { run_id };
            }
            return WorkflowViewAction::None;
        }
        if key == "ctrl+c" || kb.matches(key, "tui.select.cancel") {
            return WorkflowViewAction::Close;
        }
        if kb.matches(key, "tui.select.up") {
            self.step(-1);
            return WorkflowViewAction::None;
        }
        if kb.matches(key, "tui.select.down") {
            self.step(1);
            return WorkflowViewAction::None;
        }
        if kb.matches(key, "tui.select.confirm") {
            return match self.cursor() {
                Some(_) => WorkflowViewAction::OpenAgents,
                None => WorkflowViewAction::None,
            };
        }
        if key == "c" {
            if let Some(run) = self
                .selected_run()
                .filter(|run| run.state == WorkflowRunState::Running)
            {
                self.confirming = Some(run.run_id.clone());
            }
        }
        WorkflowViewAction::None
    }

    /// The page's rows.
    #[must_use]
    pub fn render(&self, theme: &Theme, width: usize, kb: &KeybindingsManager) -> Vec<Line> {
        render::render(self, theme, width, kb)
    }
}

/// The status glyph of an agent.
#[must_use]
pub fn agent_glyph(status: WorkflowAgentStatus) -> &'static str {
    match status {
        WorkflowAgentStatus::Queued => "·",
        WorkflowAgentStatus::Running => "▶",
        WorkflowAgentStatus::Done => "✓",
        WorkflowAgentStatus::Cached => "↺",
        WorkflowAgentStatus::Failed => "✗",
        WorkflowAgentStatus::Cancelled => "⊘",
    }
}
