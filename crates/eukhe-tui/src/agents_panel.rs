//! The pinned agents block (omp's subagent HUD): above the composer, one
//! row per running subagent of this session (its family tree, nested by
//! depth) and per running job (a kernel shell, a workflow run), visible
//! while anything runs and gone when nothing does.
//!
//! An agent row names what the agent does, from its pushed roster row
//! only: the [`AgentActivity`] indicator (the phase and how long the
//! agent runs), its model and reasoning level, the tool it runs and for
//! how long, a retry wait, its context use, its spend, and a quiet signal
//! when nothing was heard from it for `terminal.stuckAfterSecs`. The
//! block renders from state already in memory: a frame never waits on
//! the daemon.

use std::time::{Duration, Instant};

use serde_json::Value;

use eukhe_types::daemon::agent_roster::{summary_admission, AgentRosterStatus, ModelAdmission};
use eukhe_types::daemon::{CurrentTool, RetryWait};
use eukhe_types::workflow::{WorkflowPhaseState, WorkflowRunSnapshot, WorkflowRunState};

use crate::activity::{AgentActivity, QuotaPark, TurnPhase};
use crate::agents_view_state::iso_to_unix_ms;
use crate::bash_view::BashActivity;
use crate::chat::{format_working_elapsed, working_icon_frame};
use crate::chrome::{format_token_count, ContextUsage};
use crate::glyphs::{ARROW, DOT_HALF, ELLIPSIS, WARN};
use crate::style::Modifier;
use crate::subagents::{entry_status, SessionIdentity};
use crate::swarm_block::{family_members, kept_members, roster_lines, RosterLine};
use crate::theme::{Theme, ThemeColor};
use crate::width::truncate_line;
use crate::{Line, Span};

/// `terminal.stuckAfterSecs`'s default.
pub const DEFAULT_STUCK_AFTER_SECS: u64 = 60;

/// Rows the collapsed block shows before its `... N more` row.
pub const COLLAPSED_ROWS: usize = 3;

/// A tool call running longer than this shows its elapsed time in the
/// warning color.
pub const SLOW_TOOL_SECS: u64 = 5;

/// A context use at or past this percent shows in the warning color.
const CONTEXT_WARN_PERCENT: f64 = 90.0;

/// How the block shows (`terminal.pinnedAgents`, omp
/// `display.pinnedAgents`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum PinnedAgents {
    /// No block.
    Off,
    /// The first [`COLLAPSED_ROWS`] rows and a count of the rest.
    #[default]
    Collapsed,
    /// Every row.
    Full,
}

impl PinnedAgents {
    /// The setting's value; anything else reads as the default.
    #[must_use]
    pub fn parse(text: &str) -> Self {
        match text {
            "off" => Self::Off,
            "full" => Self::Full,
            _ => Self::Collapsed,
        }
    }

    /// The expand key: a collapsed block opens in full, a full one (or
    /// one the setting turned off) folds to collapsed.
    #[must_use]
    pub fn toggled(self) -> Self {
        match self {
            Self::Collapsed => Self::Full,
            Self::Full | Self::Off => Self::Collapsed,
        }
    }
}

/// A tool call an agent runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ToolRun {
    pub name: String,
    /// When it started (Unix ms); unknown for a call a restarted worker
    /// found running.
    pub started_ms: Option<u64>,
}

/// One running subagent.
#[derive(Debug, Clone, PartialEq)]
pub struct AgentRow {
    /// The family row: tree connectors, name, status, admission, depth,
    /// model with its reasoning level, and note.
    pub line: RosterLine,
    /// What the agent does; a working agent counts from its creation.
    pub activity: AgentActivity,
    pub tool: Option<ToolRun>,
    pub retry: Option<RetryWait>,
    pub context: Option<ContextUsage>,
    /// Its own spend (USD).
    pub cost: Option<f64>,
    /// The last word from the agent (Unix ms): the supervisor's last
    /// delta, its newest message, its tool's start, or its creation.
    pub heard_ms: Option<u64>,
}

/// One running job.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JobRow {
    /// A kernel shell.
    Bash {
        command: String,
        started_ms: Option<u64>,
    },
    /// A dynamic workflow run.
    Workflow {
        name: String,
        /// The active phase's title.
        phase: Option<String>,
        done: u32,
        failed: u32,
        spawned: u32,
    },
}

/// The block's content: the running agents in tree order, then the
/// running jobs.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct AgentsPanel {
    pub agents: Vec<AgentRow>,
    pub jobs: Vec<JobRow>,
}

/// How the expand key reaches the block from where the keys go now: the
/// "N more" row names only keys that work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ExpandReach<'a> {
    /// The dock holds the focus: the expand key toggles the block.
    Focused,
    /// The editor holds the keys (a space there is text): this key hands
    /// the focus to the dock first.
    AfterFocus(&'a str),
    /// The dock refuses the focus now (the armed exit hint, or the
    /// streaming follow-up hint over a draft): no key expands the block.
    Blocked,
}

/// What a render of the block needs besides its content.
#[derive(Debug, Clone, Copy)]
pub(crate) struct PanelView<'a> {
    pub(crate) mode: PinnedAgents,
    /// `terminal.stuckAfterSecs`; `0` turns the quiet signal off.
    pub(crate) stuck_after_secs: u64,
    /// The dock's focus rests on the subagents group: the title shows the
    /// keys.
    pub(crate) focused: bool,
    /// The key that opens the agents view.
    pub(crate) open_key: &'a str,
    /// The key that expands or collapses the block.
    pub(crate) expand_key: &'a str,
    /// How the expand key reaches the block now.
    pub(crate) expand_reach: ExpandReach<'a>,
    pub(crate) frame: usize,
    pub(crate) now: Instant,
    pub(crate) now_ms: u64,
}

impl AgentsPanel {
    /// The block of the session `root` from the roster, the session's
    /// shells, and its workflow runs. `anchor` and `anchor_ms` name one
    /// instant on the monotonic and the wall clock ([`clock_anchor`]):
    /// an agent's creation time maps through them onto the monotonic
    /// clock its indicator counts on.
    #[must_use]
    pub(crate) fn build(
        roster: &[Value],
        root: &SessionIdentity,
        bash: &[BashActivity],
        workflows: &[WorkflowRunSnapshot],
        anchor: Instant,
        anchor_ms: u64,
    ) -> Self {
        let family = family_members(roster, root);
        let live = kept_members(&family, |member| is_live(member.entry));
        let agents = live
            .iter()
            .zip(roster_lines(&live))
            .enumerate()
            .map(|(index, (member, line))| {
                let children = live
                    .iter()
                    .filter(|other| other.parent == Some(index))
                    .count();
                agent_row(member.entry, line, children, anchor, anchor_ms)
            })
            .collect();
        let shells = bash
            .iter()
            .filter(|activity| activity.running())
            .map(|activity| JobRow::Bash {
                command: activity.command.clone(),
                started_ms: activity.started_at.as_deref().and_then(wall_ms),
            });
        let runs = workflows
            .iter()
            .filter(|run| run.state == WorkflowRunState::Running)
            .map(|run| JobRow::Workflow {
                name: run.name.clone(),
                phase: run
                    .phases
                    .iter()
                    .find(|phase| phase.state == WorkflowPhaseState::Active)
                    .map(|phase| phase.title.clone()),
                done: run.done,
                failed: run.failed,
                spawned: run.spawned,
            });
        Self {
            agents,
            jobs: shells.chain(runs).collect(),
        }
    }

    /// Whether the block shows: the setting leaves it on and something
    /// runs.
    #[must_use]
    pub fn shown(&self, mode: PinnedAgents) -> bool {
        match mode {
            PinnedAgents::Off => false,
            PinnedAgents::Collapsed | PinnedAgents::Full => {
                !self.agents.is_empty() || !self.jobs.is_empty()
            }
        }
    }
}

/// A running family member, or a child run admitted but not started.
fn is_live(entry: &Value) -> bool {
    entry_status(entry) == AgentRosterStatus::Running
        || entry.get("queuedChild").and_then(Value::as_bool) == Some(true)
}

/// An RFC 3339 time as Unix ms.
fn wall_ms(iso: &str) -> Option<u64> {
    iso_to_unix_ms(iso).and_then(|ms| u64::try_from(ms).ok())
}

/// One instant on the monotonic clock and the wall clock, taken once per
/// process: the anchor every [`AgentsPanel::build`] maps wall times
/// through.
static CLOCK_ANCHOR: std::sync::LazyLock<(Instant, u64)> =
    std::sync::LazyLock::new(|| (Instant::now(), crate::agents_view_state::now_ms()));

/// The process's [`CLOCK_ANCHOR`].
#[must_use]
pub(crate) fn clock_anchor() -> (Instant, u64) {
    *CLOCK_ANCHOR
}

/// The monotonic instant of the wall time `at_ms`, through the anchor.
fn instant_at(anchor: Instant, anchor_ms: u64, at_ms: u64) -> Instant {
    if at_ms <= anchor_ms {
        anchor
            .checked_sub(Duration::from_millis(anchor_ms - at_ms))
            .unwrap_or(anchor)
    } else {
        anchor + Duration::from_millis(at_ms - anchor_ms)
    }
}

/// One summary field read as its wire type.
fn typed<T: serde::de::DeserializeOwned>(summary: &Value, name: &str) -> Option<T> {
    summary
        .get(name)
        .and_then(|value| T::deserialize(value).ok())
}

fn agent_row(
    entry: &Value,
    line: RosterLine,
    children: usize,
    anchor: Instant,
    anchor_ms: u64,
) -> AgentRow {
    let summary = &entry["summary"];
    let time = |value: Option<&Value>| value.and_then(Value::as_str).and_then(wall_ms);
    let current: Option<CurrentTool> = typed(summary, "currentTool");
    let retry: Option<RetryWait> = typed(summary, "retry");
    let park: Option<QuotaPark> = typed(summary, "quotaPark");
    let created_ms = time(summary.get("created"));
    let tool = current.map(|tool| ToolRun {
        started_ms: tool.started_at.as_deref().and_then(wall_ms),
        name: tool.name,
    });
    let heard_ms = [
        time(entry.get("lastHeardFromAt")),
        time(summary.get("lastActivityAt")),
        tool.as_ref().and_then(|tool| tool.started_ms),
        created_ms,
    ]
    .into_iter()
    .flatten()
    .max();
    let flag = |name: &str| summary.get(name).and_then(Value::as_bool) == Some(true);
    let activity = match park {
        Some(park) => AgentActivity::Parked(park),
        None if flag("hasRunningSubagents") && !flag("isStreaming") && !flag("isCompacting") => {
            AgentActivity::Background {
                tasks: children.max(1),
            }
        }
        None => AgentActivity::Working {
            phase: phase(entry, retry.is_some(), tool.is_some()),
            since: created_ms.map_or(anchor, |created| instant_at(anchor, anchor_ms, created)),
        },
    };
    AgentRow {
        line,
        activity,
        tool,
        retry,
        context: summary
            .get("contextUsage")
            .and_then(ContextUsage::from_wire),
        cost: summary
            .get("usage")
            .and_then(|usage| usage.get("cost"))
            .and_then(Value::as_f64),
        heard_ms,
    }
}

/// The turn phase a running agent's row reads as.
fn phase(entry: &Value, retrying: bool, tool_running: bool) -> TurnPhase {
    let summary = &entry["summary"];
    let flag = |name: &str| summary.get(name).and_then(Value::as_bool) == Some(true);
    let label = entry.get("statusLabel").and_then(Value::as_str);
    let worker_state = summary.get("workerState").and_then(Value::as_str);
    if label == Some("queued") || entry.get("queuedChild").and_then(Value::as_bool) == Some(true) {
        TurnPhase::Queued
    } else if label == Some("recovering") || worker_state.is_some_and(|state| state != "ready") {
        TurnPhase::Reconnecting
    } else if retrying {
        TurnPhase::Retrying
    } else if flag("isCompacting") {
        TurnPhase::Compacting
    } else if summary_admission(summary) == Some(ModelAdmission::Queued) {
        TurnPhase::Queued
    } else if tool_running || flag("isRunningTools") || flag("isBashRunning") {
        TurnPhase::RunningTool
    } else if flag("isStreaming") {
        TurnPhase::Thinking
    } else {
        TurnPhase::Requesting
    }
}

impl AgentRow {
    /// Seconds since the last word from a working agent, once that reaches
    /// `stuck_after_secs` (`0` turns the signal off). A retry wait, a
    /// park, and background work wait on purpose and never read as quiet.
    #[must_use]
    pub fn quiet_secs(&self, stuck_after_secs: u64, now_ms: u64) -> Option<u64> {
        match &self.activity {
            AgentActivity::Working { phase, .. } => {
                if stuck_after_secs == 0 || *phase == TurnPhase::Retrying {
                    return None;
                }
                let quiet = now_ms.saturating_sub(self.heard_ms?) / 1_000;
                (quiet >= stuck_after_secs).then_some(quiet)
            }
            AgentActivity::Parked(_) | AgentActivity::Background { .. } | AgentActivity::Idle => {
                None
            }
        }
    }
}

/// The block's rows: a title, then one row per agent and job (the first
/// [`COLLAPSED_ROWS`] and a `... N more` row while collapsed). Empty while
/// [`AgentsPanel::shown`] is false.
pub(crate) fn render_agents_panel(
    panel: &AgentsPanel,
    view: &PanelView<'_>,
    theme: &Theme,
    width: usize,
) -> Vec<Line> {
    if !panel.shown(view.mode) {
        return Vec::new();
    }
    let mut rows: Vec<Line> = panel
        .agents
        .iter()
        .map(|row| agent_line(row, view, theme))
        .chain(panel.jobs.iter().map(|job| job_line(job, view, theme)))
        .collect();
    let total = rows.len();
    let hidden = match view.mode {
        PinnedAgents::Collapsed if total > COLLAPSED_ROWS => total - COLLAPSED_ROWS,
        PinnedAgents::Off | PinnedAgents::Collapsed | PinnedAgents::Full => 0,
    };
    rows.truncate(total - hidden);
    if hidden > 0 {
        let keys = match view.expand_reach {
            ExpandReach::Focused => format!(" ({}: expand)", view.expand_key),
            ExpandReach::AfterFocus(focus_key) => {
                format!(" ({focus_key}, {}: expand)", view.expand_key)
            }
            ExpandReach::Blocked => String::new(),
        };
        rows.push(vec![Span::styled(
            format!("   {ELLIPSIS} {hidden} more{keys}"),
            theme.fg_style(ThemeColor::Muted),
        )]);
    }
    let mut out = vec![title_line(panel, view, theme)];
    out.extend(rows);
    out.iter()
        .map(|row| truncate_line(row, width, ELLIPSIS))
        .collect()
}

/// `Agents  2 running - 1 job`, the quiet count in the warning color, and
/// the keys while focused.
fn title_line(panel: &AgentsPanel, view: &PanelView<'_>, theme: &Theme) -> Line {
    let quiet = panel
        .agents
        .iter()
        .filter(|row| row.quiet_secs(view.stuck_after_secs, view.now_ms).is_some())
        .count();
    let mut counts = Vec::new();
    if !panel.agents.is_empty() {
        counts.push(format!("{} running", panel.agents.len()));
    }
    if !panel.jobs.is_empty() {
        let jobs = panel.jobs.len();
        counts.push(format!("{jobs} {}", if jobs == 1 { "job" } else { "jobs" }));
    }
    let title = theme
        .fg_style(ThemeColor::Accent)
        .add_modifier(Modifier::BOLD);
    let mut line = vec![
        Span::raw(" "),
        Span::styled(
            "Agents",
            if view.focused {
                title.add_modifier(Modifier::REVERSED)
            } else {
                title
            },
        ),
        Span::styled(
            format!("  {}", counts.join(" - ")),
            theme.fg_style(ThemeColor::Muted),
        ),
    ];
    if quiet > 0 {
        line.push(Span::styled(
            format!("  {WARN} {quiet} quiet"),
            theme.fg_style(ThemeColor::Warning),
        ));
    }
    if view.focused {
        line.push(Span::styled(
            format!(
                "  {}: agents view - {}: expand",
                view.open_key, view.expand_key
            ),
            theme.fg_style(ThemeColor::Dim),
        ));
    }
    line
}

/// Elapsed seconds from `start_ms` to `now_ms`.
fn since_secs(start_ms: u64, now_ms: u64) -> u64 {
    now_ms.saturating_sub(start_ms) / 1_000
}

fn agent_line(row: &AgentRow, view: &PanelView<'_>, theme: &Theme) -> Line {
    let muted = theme.fg_style(ThemeColor::Muted);
    let dim = theme.fg_style(ThemeColor::Dim);
    let warning = theme.fg_style(ThemeColor::Warning);
    let quiet = row.quiet_secs(view.stuck_after_secs, view.now_ms);
    let indicator = row.activity.indicator(view.now, view.now_ms);
    let busy = indicator.as_ref().is_some_and(|indicator| indicator.busy);
    let waiting = matches!(
        row.activity,
        AgentActivity::Working {
            phase: TurnPhase::Queued,
            ..
        }
    );
    let icon = match (quiet, busy && !waiting) {
        (Some(_), _) => Span::styled(WARN, warning),
        (None, true) => Span::styled(
            working_icon_frame(view.frame),
            theme.fg_style(ThemeColor::Success),
        ),
        (None, false) => Span::styled(DOT_HALF, warning),
    };
    let mut line = vec![
        Span::raw(" "),
        icon,
        Span::raw(" "),
        Span::styled(row.line.tree.clone(), dim),
        Span::styled(row.line.name.clone(), theme.fg_style(ThemeColor::Accent)),
        Span::styled(format!("  {}", row.line.model), muted),
    ];
    if let Some(indicator) = indicator {
        line.push(Span::styled(
            format!("  {}", indicator.text),
            theme.fg_style(ThemeColor::Text),
        ));
    }
    if let Some(tool) = &row.tool {
        let elapsed = tool.started_ms.map(|start| since_secs(start, view.now_ms));
        line.push(Span::styled(format!("  {ARROW} {}", tool.name), muted));
        if let Some(elapsed) = elapsed {
            line.push(Span::styled(
                format!(" {}", format_working_elapsed(elapsed)),
                if elapsed >= SLOW_TOOL_SECS {
                    warning
                } else {
                    muted
                },
            ));
        }
    }
    if let Some(retry) = &row.retry {
        let attempts = match retry.max_attempts {
            Some(max) => format!("{}/{max}", retry.attempt),
            None => retry.attempt.to_string(),
        };
        let wait = wall_ms(&retry.retry_at).map_or_else(String::new, |at| {
            format!(" in {}s", at.saturating_sub(view.now_ms).div_ceil(1_000))
        });
        line.push(Span::styled(
            format!("  retry {attempts}{wait}: {}", retry.error),
            warning,
        ));
    }
    if let Some(quiet) = quiet {
        line.push(Span::styled(
            format!("  no activity for {}", format_working_elapsed(quiet)),
            warning,
        ));
    }
    if let Some(context) = row.context {
        let percent = context.percent();
        line.push(Span::styled(
            format!(
                "  ctx {}/{} {percent:.0}%",
                format_token_count(context.tokens),
                format_token_count(context.context_window)
            ),
            if percent >= CONTEXT_WARN_PERCENT {
                warning
            } else {
                dim
            },
        ));
    }
    if let Some(cost) = row.cost.filter(|cost| *cost > 0.0) {
        line.push(Span::styled(format!("  ${cost:.2}"), dim));
    }
    if let Some(note) = &row.line.note {
        line.push(Span::styled(format!("  {note}"), dim));
    }
    line
}

fn job_line(job: &JobRow, view: &PanelView<'_>, theme: &Theme) -> Line {
    let muted = theme.fg_style(ThemeColor::Muted);
    let mut line = vec![
        Span::raw(" "),
        Span::styled(
            working_icon_frame(view.frame),
            theme.fg_style(ThemeColor::Success),
        ),
        Span::raw(" "),
    ];
    match job {
        JobRow::Bash {
            command,
            started_ms,
        } => {
            line.push(Span::styled(
                format!("$ {command}"),
                theme.fg_style(ThemeColor::BashMode),
            ));
            if let Some(start) = started_ms {
                line.push(Span::styled(
                    format!(
                        "  {}",
                        format_working_elapsed(since_secs(*start, view.now_ms))
                    ),
                    muted,
                ));
            }
        }
        JobRow::Workflow {
            name,
            phase,
            done,
            failed,
            spawned,
        } => {
            line.push(Span::styled(
                format!("workflow {name}"),
                theme.fg_style(ThemeColor::Accent),
            ));
            if let Some(phase) = phase {
                line.push(Span::styled(format!("  {phase}"), muted));
            }
            let progress = if *failed > 0 {
                format!("  {done}/{spawned} done, {failed} failed")
            } else {
                format!("  {done}/{spawned} done")
            };
            line.push(Span::styled(progress, muted));
        }
    }
    line
}

#[cfg(test)]
mod tests;
