//! The `/workflows` page rows: per run a header, the phase list with the
//! agents under each phase, and the log tail; then the error line and
//! the key hint.

use eukhe_types::workflow::{
    WorkflowAgent, WorkflowAgentStatus, WorkflowPhaseState, WorkflowRunSnapshot, WorkflowRunState,
};

use super::{agent_glyph, Cursor, WorkflowView};
use crate::keybindings::{format_key_text, KeybindingsManager};
use crate::menu_panel::scrub_controls;
use crate::theme::{Theme, ThemeColor};
use crate::width::truncate_line;
use crate::{Line, Span};

/// Log lines a panel shows.
const LOG_ROWS: usize = 5;

fn state_text(state: &WorkflowRunState) -> (String, ThemeColor) {
    match state {
        WorkflowRunState::Running => ("running".to_owned(), ThemeColor::Accent),
        WorkflowRunState::Done => ("done".to_owned(), ThemeColor::Success),
        WorkflowRunState::Failed { error } => (
            format!("failed: {}", scrub_controls(error)),
            ThemeColor::Error,
        ),
        WorkflowRunState::Cancelled => ("cancelled".to_owned(), ThemeColor::Warning),
    }
}

fn agent_color(status: WorkflowAgentStatus) -> ThemeColor {
    match status {
        WorkflowAgentStatus::Queued => ThemeColor::Dim,
        WorkflowAgentStatus::Running => ThemeColor::Accent,
        WorkflowAgentStatus::Done | WorkflowAgentStatus::Cached => ThemeColor::Success,
        WorkflowAgentStatus::Failed => ThemeColor::Error,
        WorkflowAgentStatus::Cancelled => ThemeColor::Warning,
    }
}

fn agent_row(theme: &Theme, agent: &WorkflowAgent, selected: bool, indent: &str) -> Line {
    let marker = if selected { "› " } else { "  " };
    let mut row = vec![
        Span::raw(format!("{indent}{marker}")),
        theme.fg_span(agent_color(agent.status), agent_glyph(agent.status)),
        Span::raw(" "),
    ];
    let label = theme.fg_span(ThemeColor::Text, scrub_controls(&agent.label));
    row.push(if selected { theme.bold(label) } else { label });
    if let Some(note) = &agent.note {
        row.push(theme.fg_span(ThemeColor::Muted, format!("  {}", scrub_controls(note))));
    }
    row
}

fn run_panel(
    view: &WorkflowView,
    theme: &Theme,
    index: usize,
    run: &WorkflowRunSnapshot,
    cursor: Option<Cursor>,
    rows: &mut Vec<Line>,
) {
    let (state, color) = state_text(&run.state);
    let running = run
        .agents
        .iter()
        .filter(|agent| agent.status == WorkflowAgentStatus::Running)
        .count();
    rows.push(vec![
        Span::raw("  "),
        theme.bold(theme.fg_span(ThemeColor::Text, scrub_controls(&run.name))),
        theme.fg_span(
            ThemeColor::Muted,
            format!(
                "  {} | {}/{} agents | {running} running | {} done | {} failed | ",
                run.size.as_str(),
                run.spawned,
                run.max_agents,
                run.done,
                run.failed
            ),
        ),
        theme.fg_span(color, state),
    ]);
    rows.push(vec![
        Span::raw("  "),
        theme.fg_span(
            ThemeColor::Dim,
            format!("run {}  {}", run.run_id, scrub_controls(&run.description)),
        ),
    ]);
    let selected = |agent: usize| cursor == Some(Cursor { run: index, agent });
    for phase in &run.phases {
        let (glyph, color) = match phase.state {
            WorkflowPhaseState::Done => ("✓", ThemeColor::Success),
            WorkflowPhaseState::Active => ("▶", ThemeColor::Accent),
            WorkflowPhaseState::Pending => ("·", ThemeColor::Dim),
        };
        rows.push(vec![
            Span::raw("  "),
            theme.fg_span(color, glyph),
            Span::raw(" "),
            theme.fg_span(ThemeColor::Text, scrub_controls(&phase.title)),
        ]);
        for (position, agent) in run.agents.iter().enumerate() {
            if agent.phase.as_deref() == Some(phase.title.as_str()) {
                rows.push(agent_row(theme, agent, selected(position), "    "));
            }
        }
    }
    let unphased: Vec<(usize, &WorkflowAgent)> = run
        .agents
        .iter()
        .enumerate()
        .filter(|(_, agent)| {
            !run.phases
                .iter()
                .any(|phase| agent.phase.as_deref() == Some(phase.title.as_str()))
        })
        .collect();
    if !unphased.is_empty() {
        if !run.phases.is_empty() {
            rows.push(vec![
                Span::raw("  "),
                theme.fg_span(ThemeColor::Muted, "other agents"),
            ]);
        }
        for (position, agent) in unphased {
            rows.push(agent_row(theme, agent, selected(position), "    "));
        }
    }
    let skip = run.logs.len().saturating_sub(LOG_ROWS);
    for line in run.logs.iter().skip(skip) {
        rows.push(vec![
            Span::raw("    "),
            theme.fg_span(ThemeColor::Dim, format!("log: {}", scrub_controls(line))),
        ]);
    }
    if view.confirming.as_deref() == Some(run.run_id.as_str()) {
        rows.push(vec![
            Span::raw("  "),
            theme.fg_span(
                ThemeColor::Warning,
                "Cancel this run and its running agents? y: cancel, any other key: keep",
            ),
        ]);
    }
}

fn hint(kb: &KeybindingsManager) -> String {
    let key = |binding: &str, fallback: &str| {
        kb.first_key(binding)
            .map_or_else(|| fallback.to_string(), |key| format_key_text(&key))
    };
    format!(
        "{}/{} move - {} agents view - c cancel run - {} close",
        key("tui.select.up", "up"),
        key("tui.select.down", "down"),
        key("tui.select.confirm", "enter"),
        key("tui.select.cancel", "esc"),
    )
}

pub(super) fn render(
    view: &WorkflowView,
    theme: &Theme,
    width: usize,
    kb: &KeybindingsManager,
) -> Vec<Line> {
    let mut panels: Vec<Line> = vec![vec![
        Span::raw("  "),
        theme.fg_span(ThemeColor::Accent, "Workflows"),
    ]];
    if view.runs.is_empty() {
        panels.push(vec![Span::raw("")]);
        panels.push(vec![
            Span::raw("  "),
            theme.fg_span(ThemeColor::Text, "No workflow runs in this session."),
        ]);
        panels.push(vec![
            Span::raw("  "),
            theme.fg_span(ThemeColor::Muted, "Start one: /dynamic-workflow <request>"),
        ]);
    }
    let cursor = view.cursor();
    let mut focus_row = 0;
    for (index, run) in view.runs.iter().enumerate() {
        panels.push(vec![Span::raw("")]);
        if cursor.is_some_and(|cursor| cursor.run == index) {
            focus_row = panels.len();
        }
        run_panel(view, theme, index, run, cursor, &mut panels);
    }
    let mut chrome: Vec<Line> = Vec::new();
    if let Some(error) = &view.error {
        chrome.push(vec![Span::raw("")]);
        chrome.push(vec![
            Span::raw("  "),
            theme.fg_span(ThemeColor::Error, format!("Error: {error}")),
        ]);
    }
    chrome.push(vec![Span::raw("")]);
    chrome.push(vec![
        Span::raw("  "),
        theme.fg_span(ThemeColor::Dim, hint(kb)),
    ]);
    let budget = view.viewport_rows.max(1);
    let panel_budget = budget.saturating_sub(chrome.len());
    if panels.len() > panel_budget {
        // Keep the selected run's panel in sight.
        let start = focus_row.min(panels.len().saturating_sub(panel_budget));
        panels.drain(..start);
        panels.truncate(panel_budget);
    }
    let mut rows = panels;
    rows.extend(chrome);
    if rows.len() > budget {
        rows.drain(..rows.len() - budget);
    }
    rows.into_iter()
        .map(|row| truncate_line(&row, width, ""))
        .collect()
}
