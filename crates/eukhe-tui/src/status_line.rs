//! The status line under the prompt (omp `statusLine`, ascii preset,
//! transparent): the model and its thinking level, the cwd, the git
//! branch, then the segments that show only while they carry something
//! (a hint, the session name and spend, the detail level, live activity);
//! the context usage sits on the right.

use crate::chat::Detail;
use crate::chrome::{ActivityDock, ActivityGroup, ChromeState};
use crate::git_placement::GitPlacement;
use crate::theme::{Theme, ThemeColor};
use crate::width::line_width;
use crate::{Line, Span};

/// The widest the path segment's text gets (omp `path.maxLength`).
const PATH_MAX_WIDTH: usize = 35;

/// The status line row for `width` columns: one margin column on each
/// side, the left segments, and the context usage flush right. The left
/// side gives way first when the row is short.
#[must_use]
pub fn render_status_line(
    state: &ChromeState,
    detail: Detail,
    theme: &Theme,
    width: usize,
) -> Line {
    let home = eukhe_types::platform::home_dir().map(|home| home.to_string_lossy().into_owned());
    let temp = std::env::temp_dir().to_string_lossy().into_owned();
    let roots = PathRoots {
        home: home.as_deref(),
        temp: &temp,
    };
    let mut segments: Vec<Line> = Vec::new();
    if let Some(hint) = &state.tray_override {
        segments.push(vec![theme.fg(ThemeColor::Muted, hint.clone())]);
    }
    if let Some(model) = model_segment(state, theme) {
        segments.push(model);
    }
    segments.push(vec![theme.fg(
        ThemeColor::Dim,
        path_label(&state.cwd, state.git.as_ref(), &roots),
    )]);
    if let Some(branch) = state.git.as_ref().and_then(|git| git.branch.as_ref()) {
        segments.push(vec![theme.fg(ThemeColor::Dim, format!("@ {branch}"))]);
    }
    if let Some(name) = state.session_name.as_deref().map(str::trim) {
        if !name.is_empty() {
            segments.push(vec![theme.fg(ThemeColor::Dim, name.to_string())]);
        }
    }
    if let Some(cost) = state.cost_usd.filter(|cost| *cost > 0.0) {
        segments.push(vec![theme.fg(ThemeColor::Dim, format!("${cost:.2}"))]);
    }
    if let Some(depth) = state.tray_depth.filter(|depth| *depth > 0) {
        segments.push(vec![theme.fg(ThemeColor::Dim, format!("depth {depth}"))]);
    }
    match detail {
        Detail::Overview => {}
        Detail::Details => segments.push(vec![theme.fg(ThemeColor::Dim, "details")]),
        Detail::All => segments.push(vec![theme.fg(ThemeColor::Dim, "expanded")]),
    }
    if let Some(dock) = &state.activity {
        segments.extend(activity_segments(dock, theme));
    }
    let mut left: Line = Vec::new();
    for (index, segment) in segments.into_iter().enumerate() {
        if index > 0 {
            left.push(theme.fg(ThemeColor::Dim, crate::glyphs::SEP));
        }
        left.extend(segment);
    }
    let mut right: Line = state
        .context
        .map(|context| context_segment(context, theme))
        .unwrap_or_default();
    let inner = width.saturating_sub(2);
    if line_width(&right) + 1 > inner {
        right.clear();
    }
    let room = inner.saturating_sub(line_width(&right) + usize::from(!right.is_empty()));
    let left = crate::chrome::truncate_spans_to_width(&left, room);
    let mut row: Line = vec![Span::raw(" ")];
    let used = line_width(&left) + line_width(&right);
    row.extend(left);
    if !right.is_empty() {
        row.push(Span::raw(" ".repeat(inner.saturating_sub(used))));
        row.extend(right);
    }
    row
}

/// `[M] <model>`, the service-tier badge, and the thinking level in the
/// model color (omp `statusLineModel`).
fn model_segment(state: &ChromeState, theme: &Theme) -> Option<Line> {
    let model = state.model_id.as_ref()?;
    let mut text = format!("[M] {model}");
    match state.service_tier.as_deref() {
        Some("priority") => text.push_str(" >>"),
        Some("default") | None => {}
        Some(tier) => {
            text.push(' ');
            text.push_str(tier);
        }
    }
    if let Some(level) = &state.thinking_suffix {
        text.push_str(crate::glyphs::SEP);
        text.push_str(&thinking_label(level));
    }
    Some(vec![theme.fg(ThemeColor::Muted, text)])
}

/// The bracketed thinking-level label (omp's ascii `thinking.*` symbols).
fn thinking_label(level: &str) -> String {
    use eukhe_types::ai::ModelThinkingLevel;
    let Some(parsed) = eukhe_types::ai::thinking_level_from_str(level) else {
        return format!("[{level}]");
    };
    match parsed {
        ModelThinkingLevel::Off => "[ ] off",
        ModelThinkingLevel::Minimal => "[min]",
        ModelThinkingLevel::Low => "[low]",
        ModelThinkingLevel::Medium => "[med]",
        ModelThinkingLevel::High => "[high]",
        ModelThinkingLevel::Xhigh => "[xhi]",
        ModelThinkingLevel::Max => "[max]",
    }
    .to_string()
}

/// The directories the path segment shortens against.
struct PathRoots<'a> {
    home: Option<&'a str>,
    temp: &'a str,
}

/// The path segment's text (omp `path` with `abbreviate` and
/// `stripWorkPrefix`): a linked worktree reads `project/worktree` (the
/// project alone when the branch is named like the worktree); a scratch
/// directory reads relative to its temp root; any other cwd drops a
/// `~/Projects` or `/work` prefix and abbreviates the home directory.
/// Longer text keeps its tail behind a leading `...`.
fn path_label(cwd: &str, git: Option<&GitPlacement>, roots: &PathRoots) -> String {
    if let Some(worktree) = git.and_then(|git| git.worktree.as_ref()) {
        let label = if git.and_then(|git| git.branch.as_deref()) == Some(worktree.name.as_str()) {
            worktree.project.clone()
        } else {
            format!("{}/{}", worktree.project, worktree.name)
        };
        return format!("[wt] {}", clamp_path(&label));
    }
    let home = roots.home.filter(|home| !home.is_empty());
    let home_tmp = home.map(|home| format!("{home}/tmp"));
    let scratch_roots = [
        Some(roots.temp),
        home_tmp.as_deref(),
        Some("/tmp"),
        Some("/var/tmp"),
    ];
    let scratch = scratch_roots
        .into_iter()
        .flatten()
        .find_map(|root| relative_to(cwd, root));
    let (icon, path) = if let Some(relative) = scratch {
        ("[T]", if relative.is_empty() { cwd } else { relative })
    } else {
        let projects = home.map(|home| format!("{home}/Projects"));
        let work = [projects.as_deref(), Some("/work")]
            .into_iter()
            .flatten()
            .find_map(|root| relative_to(cwd, root).filter(|relative| !relative.is_empty()));
        ("[D]", work.unwrap_or(cwd))
    };
    let path = match home.and_then(|home| relative_to(path, home)) {
        Some("") => "~".to_string(),
        Some(rest) => format!("~/{rest}"),
        None => path.to_string(),
    };
    format!("{icon} {}", clamp_path(&path))
}

/// `path` relative to `root` when it is `root` or inside it.
fn relative_to<'a>(path: &'a str, root: &str) -> Option<&'a str> {
    let root = root.trim_end_matches('/');
    if root.is_empty() {
        return None;
    }
    let rest = path.strip_prefix(root)?;
    if rest.is_empty() {
        return Some("");
    }
    rest.strip_prefix('/')
}

/// Keep the tail of a path longer than the segment's limit.
fn clamp_path(path: &str) -> String {
    let chars = path.chars().count();
    if chars <= PATH_MAX_WIDTH {
        return path.to_string();
    }
    let keep = PATH_MAX_WIDTH - crate::glyphs::ELLIPSIS.len();
    let tail: String = path.chars().skip(chars - keep).collect();
    format!("{}{tail}", crate::glyphs::ELLIPSIS)
}

/// `ctx: <pct>%/<window>` (omp `context_pct`): the label bright, the
/// usage in the context color, warning and error tones as it fills.
fn context_segment(context: crate::chrome::ContextUsage, theme: &Theme) -> Line {
    let percent = context.percent();
    let value = if context.context_window == 0 {
        format!("{}/?", format_count(context.tokens))
    } else {
        format!("{percent:.1}%/{}", format_count(context.context_window))
    };
    vec![
        theme.fg(ThemeColor::Text, "ctx: "),
        theme.fg(context_color(percent, context.context_window), value),
    ]
}

/// The usage tone (omp `getContextUsageLevel`): each level starts at its
/// percentage, or earlier when the window is large enough for the
/// level's absolute token count to come first.
fn context_color(percent: f64, window: u64) -> ThemeColor {
    let reached = |level_percent: f64, level_tokens: f64| {
        if percent <= 0.0 {
            return false;
        }
        if window == 0 {
            return percent >= level_percent;
        }
        percent >= level_percent.min(level_tokens / window as f64 * 100.0)
    };
    if reached(90.0, 500_000.0) {
        ThemeColor::Error
    } else if reached(70.0, 270_000.0) {
        ThemeColor::ThinkingHigh
    } else if reached(50.0, 150_000.0) {
        ThemeColor::Warning
    } else {
        ThemeColor::Dim
    }
}

/// omp `formatNumber`: 999, 1.5K, 128K, 1M, 2.5M, 1B.
fn format_count(count: u64) -> String {
    let scaled = |value: f64, unit: &str| {
        let text = format!("{value:.1}");
        format!("{}{unit}", text.strip_suffix(".0").unwrap_or(&text))
    };
    let count_f = count as f64;
    match count {
        0..1_000 => count.to_string(),
        1_000..10_000 => scaled(count_f / 1e3, "K"),
        10_000..1_000_000 => format!("{}K", (count_f / 1e3).round()),
        1_000_000..10_000_000 => scaled(count_f / 1e6, "M"),
        10_000_000..1_000_000_000 => format!("{}M", (count_f / 1e6).round()),
        1_000_000_000..10_000_000_000 => scaled(count_f / 1e9, "B"),
        _ => format!("{}B", (count_f / 1e9).round()),
    }
}

/// The live activity segments: a group renders while it counts something
/// (live subagents, heartbeats, running shells, live factory runs, the
/// pursued goal). A focused dock renders every group, the selected one
/// behind the selection band, so the arrows always land on a visible
/// segment.
fn activity_segments(dock: &ActivityDock, theme: &Theme) -> Vec<Line> {
    let running = dock.subagents_running_direct + dock.subagents_running_nested;
    let color = |count: usize| {
        if count > 0 {
            ThemeColor::Success
        } else {
            ThemeColor::Muted
        }
    };
    let plural = |count: usize, one: &str, many: &str| {
        format!("{count} {}", if count == 1 { one } else { many })
    };
    let mut segments = Vec::new();
    for group in dock.groups() {
        let (live, spans) = match group {
            ActivityGroup::Subagents => (
                running > 0,
                vec![theme.fg(color(running), plural(running, "subagent", "subagents"))],
            ),
            ActivityGroup::Heartbeats => {
                let mut spans = vec![theme.fg(
                    color(dock.heartbeats),
                    plural(dock.heartbeats, "heartbeat", "heartbeats"),
                )];
                if dock.heartbeats_paused > 0 {
                    spans.push(theme.fg(ThemeColor::Dim, crate::glyphs::SEP));
                    spans.push(theme.fg(
                        ThemeColor::Warning,
                        format!("{} paused", dock.heartbeats_paused),
                    ));
                }
                (dock.heartbeats > 0, spans)
            }
            ActivityGroup::Bash => (
                dock.bash_running > 0,
                vec![theme.fg(
                    color(dock.bash_running),
                    plural(dock.bash_running, "shell", "shells"),
                )],
            ),
            ActivityGroup::Factory => (
                dock.factory_runs > 0,
                vec![theme.fg(
                    color(dock.factory_runs),
                    format!("{} factory", dock.factory_runs),
                )],
            ),
            // A pursued goal reads green; its paused and budget-limited
            // states read amber.
            ActivityGroup::Goal => {
                let goal = dock.goal_label.as_deref().unwrap_or_default();
                let tone = if goal.starts_with("Pursuing goal") {
                    ThemeColor::Success
                } else {
                    ThemeColor::Warning
                };
                (true, vec![theme.fg(tone, goal.to_string())])
            }
        };
        if !(live || dock.focused) {
            continue;
        }
        if dock.focused && dock.selected == group {
            let band = theme.selection_row_style();
            segments.push(
                spans
                    .into_iter()
                    .map(|span| Span::styled(span.content, span.style.patch(band)))
                    .collect(),
            );
        } else {
            segments.push(spans);
        }
    }
    segments
}

#[cfg(test)]
mod tests;
