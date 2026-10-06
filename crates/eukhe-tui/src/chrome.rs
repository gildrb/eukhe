//! Chat chrome: the chat state the status line reads, the activity dock's
//! groups, the brand splash header, and the `/speed` footer. Ports the TS
//! component `BrandSplashHeader` (interactive-mode.ts); the status line
//! itself lives in `status_line`.

use crate::style::Style;
use crate::width::str_width;
use crate::{Line, Span};
use serde_json::Value;

use crate::theme::{Theme, ThemeColor};

/// Truncate a plain string to a visible width (TS `truncateToWidth` for
/// plain strings: cut on grapheme boundaries, appending the ellipsis).
fn truncate_to_width(value: &str, max_width: usize, ellipsis: &str) -> String {
    if str_width(value) <= max_width {
        return value.to_string();
    }
    if max_width == 0 {
        return String::new();
    }
    let mut out = String::new();
    for ch in value.chars() {
        if str_width(&out) + crate::width::char_width(ch) > max_width {
            break;
        }
        out.push(ch);
    }
    format!("{out}{ellipsis}")
}

/// Where a session runs; drives labels that depend on persistence.
#[derive(Debug, Clone, Default)]
pub struct ChromeState {
    /// Product version shown in the splash (`eukhe vX`).
    pub version: String,
    /// Session working directory (splash `cwd` line; `~`-compressed).
    pub cwd: String,
    /// Current model id (splash `model` line; `None` hides the line).
    pub model_id: Option<String>,
    /// The current model's provider (the daemon state's `model.provider`),
    /// when the session reports one: the picker matches the current-model
    /// catalog entry by provider plus id -- two providers can carry the
    /// same id, and only the provider disambiguates them.
    pub model_provider: Option<String>,
    /// Extra metadata lines under the splash (`label value` each; e.g. the
    /// agents view's `agents N running, ...` count row and, in scoped
    /// mode, the `depth N` row). Empty renders none.
    pub extra_metadata: Vec<(String, String)>,
    /// The session's name; `None` while it is unnamed (the status line
    /// shows a name segment only for a named session).
    pub session_name: Option<String>,
    /// Session spend (USD): the family rollup (the session's own
    /// whole-file spend plus every subagent descendant's -- the same
    /// number the agents view bills the row).
    pub cost_usd: Option<f64>,
    /// Context usage: tokens and window (the status line's right side).
    pub context: Option<ContextUsage>,
    /// Where the cwd sits in git, from the background probe; `None`
    /// outside a repository or before the first probe lands.
    pub git: Option<crate::git_placement::GitPlacement>,
    /// The attached session's RLM depth (TS `formatAgentDepthLabel`): a
    /// subagent session shows a `depth N` segment; a root session (depth
    /// 0 or unknown) none.
    pub tray_depth: Option<u32>,
    /// The model's thinking level (wire name), shown after the model (TS
    /// `getModelContextLabel`); `None` for a model without reasoning.
    pub thinking_suffix: Option<String>,
    /// The session's effective service tier as its wire name (TS
    /// `connectionState.serviceTier`): the badge after the model -- `>>`
    /// for priority, the tier name for any other non-default tier.
    /// `None` (or `default`) renders no badge.
    pub service_tier: Option<String>,
    /// Startup warning (tmux keyboard setup), rendered as a status row.
    pub tmux_notice: Option<String>,
    /// The status line's leading hint (TS `getTrayOverrideLabel`): the
    /// armed Ctrl+C exit hint or the streaming follow-up hint.
    pub tray_override: Option<String>,
    /// The activity groups the status line shows while they count
    /// something; `None` means no session owns this view (the replay and
    /// app surfaces).
    pub activity: Option<ActivityDock>,
    /// The footer's tok/sec readout (TS `FooterComponent` under `/speed`):
    /// the dim bottom row's text; `None` renders no row. The client keeps
    /// `None` until the first completed response while the display is on
    /// (TS renders nothing when enabled without text).
    pub speed_text: Option<String>,
    /// Hide the splash `cwd` line (TS `getSplashCwd` returns `undefined`
    /// for the scoped agents view, so its metadata rows stay centered
    /// against the logo without the cwd row).
    pub splash_hide_cwd: bool,
}

/// Which actionable group owns the activity-dock selection. Every
/// group is arrow-traversable whether or not it has rows (the
/// operator's 2026-09-26 muscle-memory directive): emptiness never
/// removes a group from the cycle.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum ActivityGroup {
    #[default]
    Subagents,
    Heartbeats,
    Bash,
    /// The factory page: live factory runs. Its group renders exactly
    /// while the daemon advertises the `factory_activity` lane (the
    /// opt-in gate; an advertised empty one reads its zero count) and
    /// opens the factory page over the lane -- the same navigation family
    /// as the subagents, heartbeats, and shells pages.
    Factory,
    /// The active goal: its group is mounted while a goal is being
    /// pursued and opens the read-only goal panel (the objective and
    /// its facts); a goal that ended unmounts the row with it.
    Goal,
}

/// Which way an arrow key steps along the dock's rendered groups.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActivityDirection {
    /// The left arrow: the previous group, wrapping past the first.
    Prev,
    /// The right arrow: the next group, wrapping past the last.
    Next,
}

/// The activity groups behind the status line's activity segments: every
/// group stays arrow-traversable while the dock is focused (a focused dock
/// shows every group, the zero counts included).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ActivityDock {
    /// The directly-running children right now (one addend of the
    /// dock's single running total).
    pub subagents_running_direct: usize,
    /// The further running descendants below them (subagents of
    /// subagents): the total's other addend. Idle and dead registry
    /// rows never count -- they render in the scoped agents view.
    pub subagents_running_nested: usize,
    /// The CURRENT session's heartbeats (nested sessions' jobs do not
    /// surface here, operator scoping).
    pub heartbeats: usize,
    /// How many of the scoped heartbeats are paused.
    pub heartbeats_paused: usize,
    /// Bash processes actively running right now (the current session's
    /// kernel registry only): finished runs never inflate the indicator
    /// -- they stay as rows inside the bash view.
    pub bash_running: usize,
    /// Factory runs actively live right now (a live state -- running,
    /// stopping, or paused -- or a terminal run whose children are still
    /// in flight, the residents teardown; the current session's kernel
    /// registry only): fully terminal runs never inflate the indicator,
    /// exactly like the bash group's running-only count.
    pub factory_runs: usize,
    /// Whether the factory group renders at all: the daemon's
    /// `factory_activity` advertisement (the factory's opt-in gate --
    /// `factory.enabled`, off by default). A daemon without the lane
    /// mounts no factory group anywhere: no row, no traversal, no
    /// click, no page.
    pub factory_group: bool,
    /// The active goal's dock label -- `Pursuing goal (12m 05s)`-style,
    /// the elapsed-time form (the operator's 2026-09-24 directive: the
    /// row reads the time, the token budget lives inside the goal
    /// panel); `None` unless the goal is actively being pursued (a
    /// completed or idle goal carries no dock segment).
    pub goal_label: Option<String>,
    pub selected: ActivityGroup,
    pub focused: bool,
}

impl ActivityDock {
    /// The groups this dock renders, left to right -- the arrow
    /// traversal order. The subagents, heartbeats, and shells groups
    /// always render (an empty one reads its zero count and stays
    /// traversable); the factory group renders exactly while the daemon
    /// advertises the `factory_activity` lane (the opt-in gate), and the
    /// goal group exactly while a live goal keeps its row mounted.
    #[must_use]
    pub fn groups(&self) -> Vec<ActivityGroup> {
        let mut groups = vec![
            ActivityGroup::Subagents,
            ActivityGroup::Heartbeats,
            ActivityGroup::Bash,
        ];
        if self.factory_group {
            groups.push(ActivityGroup::Factory);
        }
        if self.goal_label.is_some() {
            groups.push(ActivityGroup::Goal);
        }
        groups
    }

    /// One arrow step along the rendered groups: the neighbor in
    /// `direction`, wrapping at the row's ends. A group's emptiness
    /// never skips it, so the cycle is deterministic -- N rendered
    /// groups take N presses to return to the start. A `current` that
    /// no longer renders (a goal group whose row unmounted) steps
    /// from the row's start.
    #[must_use]
    pub fn step(&self, current: ActivityGroup, direction: ActivityDirection) -> ActivityGroup {
        let groups = self.groups();
        let len = groups.len();
        let position = groups
            .iter()
            .position(|group| *group == current)
            .unwrap_or(0);
        let neighbor = match direction {
            ActivityDirection::Prev => position + len - 1,
            ActivityDirection::Next => position + 1,
        };
        groups[neighbor % len]
    }
}

/// Context usage for the tray label (`N (P%)`).
#[derive(Debug, Clone, Copy)]
pub struct ContextUsage {
    pub tokens: u64,
    pub context_window: u64,
}

impl ContextUsage {
    #[must_use]
    pub fn percent(&self) -> f64 {
        if self.context_window == 0 {
            0.0
        } else {
            (self.tokens as f64 / self.context_window as f64) * 100.0
        }
    }
}

/// `formatTokenCount` (agent-activity.ts): 999, 1.0k-9.9k, 10k, 1.2M.
#[must_use]
pub fn format_token_count(count: u64) -> String {
    if count < 1_000 {
        return count.to_string();
    }
    if count < 10_000 {
        return format!("{:.1}k", count as f64 / 1_000.0);
    }
    if count < 1_000_000 {
        return format!("{}k", (count as f64 / 1_000.0).round() as u64);
    }
    if count < 10_000_000 {
        return format!("{:.1}M", count as f64 / 1_000_000.0);
    }
    format!("{}M", (count as f64 / 1_000_000.0).round() as u64)
}

/// The `~`-compressed cwd for the splash line (TS `formatSplashCwd`).
#[must_use]
pub fn format_splash_cwd(cwd: &str, home: Option<&str>) -> String {
    let Some(home) = home else {
        return cwd.replace('\\', "/");
    };
    let home = home.replace('\\', "/");
    let normalized = cwd.replace('\\', "/");
    if home.is_empty() {
        return normalized;
    }
    if normalized == home {
        return "~".to_string();
    }
    if let Some(rest) = normalized.strip_prefix(&format!("{home}/")) {
        return format!("~/{rest}");
    }
    normalized
}

/// Middle-truncate a path: keep the last two segments (`~/.../parent/leaf`).
pub fn truncate_path_middle(value: &str, width: usize) -> String {
    if str_width(value) <= width {
        return value.to_string();
    }
    if width <= 1 {
        return truncate_to_width(value, width, "");
    }
    let normalized = value.replace('\\', "/");
    let prefix = if normalized.starts_with("~/") {
        "~/"
    } else if normalized.starts_with('/') {
        "/"
    } else {
        ""
    };
    let body = normalized[prefix.len()..].to_string();
    let mut parts: Vec<&str> = body.split('/').filter(|part| !part.is_empty()).collect();
    let last = parts.pop().unwrap_or_default().to_string();
    let previous = parts.pop().map(str::to_string);
    let suffix = previous
        .map(|previous| format!("{previous}/{last}"))
        .unwrap_or(last);
    let candidate = format!("{prefix}{}/{suffix}", crate::glyphs::ELLIPSIS);
    if str_width(&candidate) <= width {
        return candidate;
    }
    truncate_to_width(&candidate, width, crate::glyphs::ELLIPSIS)
}

/// The brand splash: product name, version, model, and cwd metadata
/// (TS `BrandSplashHeader`; `topPadding` is always on in the chat header).
#[must_use]
pub fn render_splash(state: &ChromeState, theme: &Theme, width: usize) -> Vec<Line> {
    let safe_width = width.max(1);
    let padding_x = usize::from(safe_width > 1);
    let meta_width = safe_width.saturating_sub(padding_x * 2).max(1);

    let text = theme.fg_style(ThemeColor::Text);
    let muted = theme.fg_style(ThemeColor::Muted);
    let dim = theme.fg_style(ThemeColor::Dim);
    let title = "eukhe";
    let version = format!("v{}", state.version);
    let mut meta_lines: Vec<Line> = Vec::new();
    if str_width(&format!("{title} {version}")) <= meta_width {
        meta_lines.push(vec![
            Span::styled(title.to_string(), text),
            Span::styled(" ".to_string(), Style::default()),
            Span::styled(version, muted),
        ]);
    } else {
        meta_lines.push(vec![Span::styled(title.to_string(), text)]);
        meta_lines.push(vec![Span::styled(version, muted)]);
    }
    for (label_text, value_text) in &state.extra_metadata {
        let label = format!("{label_text} ");
        let value = truncate_to_width(
            value_text,
            meta_width.saturating_sub(str_width(&label)).max(1),
            "",
        );
        meta_lines.push(vec![Span::styled(label, dim), Span::styled(value, muted)]);
    }
    if let Some(model_id) = &state.model_id {
        let label = "model ";
        let value = truncate_to_width(
            model_id,
            meta_width.saturating_sub(str_width(label)).max(1),
            "",
        );
        meta_lines.push(vec![
            Span::styled(label.to_string(), dim),
            Span::styled(value, muted),
        ]);
    }
    if !state.splash_hide_cwd {
        let cwd_label = "cwd ";
        let home =
            eukhe_types::platform::home_dir().map(|home| home.to_string_lossy().into_owned());
        let cwd = truncate_path_middle(
            &format_splash_cwd(&state.cwd, home.as_deref()),
            meta_width.saturating_sub(str_width(cwd_label)).max(1),
        );
        meta_lines.push(vec![
            Span::styled(cwd_label.to_string(), dim),
            Span::styled(cwd, muted),
        ]);
    }

    let mut lines: Vec<Line> = vec![Vec::new()];
    let pad = if padding_x > 0 { " " } else { "" };
    for meta_line in meta_lines {
        let mut spans: Line = Vec::with_capacity(meta_line.len() + 2);
        spans.push(Span::styled(pad.to_string(), Style::default()));
        spans.extend(meta_line);
        let used: usize = spans.iter().map(|s| str_width(&s.content)).sum();
        spans.push(Span::styled(
            " ".repeat(safe_width.saturating_sub(used + padding_x)),
            Style::default(),
        ));
        lines.push(spans);
    }
    // Header container: the splash row block trails one blank row.
    lines.push(Vec::new());
    lines
}

/// The model's thinking-level label (TS `getModelContextLabel`:
/// `model.reasoning ? connectionState.thinkingLevel : undefined` -- a model
/// without reasoning shows the bare id, and so does a level outside the
/// wire vocabulary). The state's level parses to its wire name, so the
/// label is always one of the TS `ThinkingLevel` strings, including "off"
/// when the session explicitly turned thinking off.
pub(crate) fn tray_thinking_suffix(state: &Value) -> Option<String> {
    let reasoning = state
        .get("model")
        .and_then(|model| model.get("reasoning"))
        .and_then(Value::as_bool)
        .unwrap_or(false);
    if !reasoning {
        return None;
    }
    state
        .get("thinkingLevel")
        .and_then(Value::as_str)
        .and_then(eukhe_types::ai::thinking_level_from_str)
        .map(|level| level.wire_name().to_string())
}

/// Truncate a styled span row to a visible width, replacing the tail with
/// the ellipsis when it does not fit (TS `truncateToWidth` on the composed
/// row).
pub(crate) fn truncate_spans_to_width(spans: &[crate::Span], width: usize) -> Vec<crate::Span> {
    let mut out: Vec<crate::Span> = Vec::new();
    let mut remaining = width;
    for (index, span) in spans.iter().enumerate() {
        if remaining == 0 {
            // The frame filled on a span boundary: the later spans still
            // exist, so the ellipsis must land (a silent drop would hide
            // content the reader cannot know about).
            if content_follows(spans, index) {
                land_marker(&mut out, width);
            }
            break;
        }
        let mut text = String::new();
        let mut consumed = 0usize;
        for ch in span.content.chars() {
            let char_width = crate::width::char_width(ch);
            if consumed + char_width > remaining {
                break;
            }
            text.push(ch);
            consumed += char_width;
        }
        if text.is_empty() {
            // This span's first character cannot fit: nothing of it
            // renders, and the ellipsis must still mark the cut.
            if content_follows(spans, index) {
                land_marker(&mut out, width);
            }
            break;
        }
        if consumed < str_width(&span.content) {
            // The span could not fit whole: the ellipsis borrows its
            // columns from the span's last kept characters -- a span that
            // fills the edge exactly gives characters back, and a span
            // too short to hold the ellipsis hands the cut to the spans
            // before it, so the row always ends INSIDE the width.
            let ellipsis = str_width(crate::glyphs::ELLIPSIS);
            while consumed + ellipsis > remaining {
                match text.pop() {
                    Some(dropped) => consumed -= crate::width::char_width(dropped),
                    None => break,
                }
            }
            if consumed + ellipsis > remaining {
                land_marker(&mut out, width);
                break;
            }
            text.push_str(crate::glyphs::ELLIPSIS);
            let mut piece = span.clone();
            piece.content = text;
            out.push(piece);
            break;
        }
        let mut piece = span.clone();
        piece.content = text;
        out.push(piece);
        remaining -= consumed;
    }
    out
}

/// Whether any span from `index` (inclusive) still carries content -- a
/// cut there must leave a marker.
fn content_follows(spans: &[crate::Span], index: usize) -> bool {
    spans[index..].iter().any(|span| !span.content.is_empty())
}

/// Land the truncation marker on a row that filled the frame on a span
/// boundary: the ellipsis borrows a column from the last kept character
/// (however wide it was), and a row too narrow for any content keeps
/// the marker alone when it fits at all.
fn land_marker(out: &mut Vec<crate::Span>, width: usize) {
    let ellipsis = str_width(crate::glyphs::ELLIPSIS);
    let row_width = |out: &Vec<crate::Span>| {
        out.iter()
            .map(|piece| crate::width::str_width(&piece.content))
            .sum::<usize>()
    };
    while row_width(out) + ellipsis > width {
        match out.last_mut() {
            Some(piece) => {
                if piece.content.pop().is_none() {
                    out.pop();
                }
            }
            None => break,
        }
    }
    match out.last_mut() {
        Some(piece) => piece.content.push_str(crate::glyphs::ELLIPSIS),
        None => {
            if ellipsis <= width {
                out.push(crate::Span::raw(crate::glyphs::ELLIPSIS));
            }
        }
    }
}

/// The footer's tok/sec row (TS `FooterComponent::render` under `/speed`):
/// one dim line -- the dock's last row -- truncated with no ellipsis when it
/// overflows the width.
#[must_use]
pub fn render_speed_footer(text: &str, theme: &Theme, width: usize) -> Line {
    let dim = theme.fg_style(ThemeColor::Dim);
    let text = truncate_to_width(text, width, "");
    vec![Span::styled(text, dim)]
}

#[cfg(test)]
mod tests;
