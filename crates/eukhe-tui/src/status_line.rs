//! The status line under the prompt (omp `statusLine`, ascii preset,
//! transparent): the model and its thinking level, the cwd, the git
//! branch, then the segments that show only while they carry something
//! (a hint, the session name and spend, the detail level, the chat
//! memory's `mem` gauge, live activity); the context usage sits on the
//! right.
//!
//! The `mem` gauge is the only place the chat memory's compactor shows
//! its progress (its live updates never make transcript rows): `mem
//! 1.1K/128K` is the view's size against its ceiling, in the context
//! segment's size form (`format_count`); while the compactor works -- from
//! the first live update of a request to the request's end -- it reads
//! `mem 1.1K/128K ~`. Never a count of nodes or pairs, never a node id.
//!
//! When the row is short, the session title gives way first (cut with
//! `...`), then the speed text, then the title drops; the model, its
//! thinking level, the `mem` gauge, the detail label and the right-aligned
//! context usage stay whole.

use crate::chat::Detail;
use crate::chrome::{ActivityDock, ActivityGroup, ChromeState};
use crate::git_placement::GitPlacement;
use crate::theme::{Theme, ThemeColor};
use crate::width::line_width;
use crate::{Line, Span};

/// The widest the path segment's text gets (omp `path.maxLength`).
const PATH_MAX_WIDTH: usize = 35;

/// The narrowest cut of the speed segment worth showing; with less room
/// the segment drops.
const SPEED_MIN_WIDTH: usize = 12;

/// The narrowest cut of the session title worth showing; with less room
/// the title drops.
const TITLE_MIN_WIDTH: usize = 8;

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
    match state.dictation {
        Some(crate::dictation::Phase::Recording) => segments.push(vec![
            theme.fg(ThemeColor::Error, "[REC] recording, esc cancels")
        ]),
        Some(crate::dictation::Phase::Transcribing) => segments.push(vec![
            theme.fg(ThemeColor::Accent, "[STT] transcribing, esc cancels")
        ]),
        None => {}
    }
    if let Some(hint) = &state.tray_override {
        segments.push(vec![theme.fg(ThemeColor::Muted, hint.clone())]);
    }
    if let Some(model) = model_segment(state, theme) {
        segments.push(model);
    }
    // The speed segment sits after the model; it and the session title
    // are the segments that give way when the row is short (`fit`).
    let speed_at = state.speed.as_ref().map(|speed| {
        segments.push(vec![
            theme.fg(ThemeColor::Muted, speed.text(std::time::Instant::now()))
        ]);
        segments.len() - 1
    });
    segments.push(vec![theme.fg(
        ThemeColor::Dim,
        path_label(&state.cwd, state.git.as_ref(), &roots),
    )]);
    if let Some(branch) = state.git.as_ref().and_then(|git| git.branch.as_ref()) {
        segments.push(vec![theme.fg(ThemeColor::Dim, format!("@ {branch}"))]);
    }
    let title_at = state
        .session_name
        .as_deref()
        .map(str::trim)
        .filter(|name| !name.is_empty())
        .map(|name| {
            segments.push(vec![theme.fg(ThemeColor::Dim, name.to_string())]);
            segments.len() - 1
        });
    if let Some(cost) = state.cost_usd.filter(|cost| *cost > 0.0) {
        segments.push(vec![theme.fg(ThemeColor::Dim, format!("${cost:.2}"))]);
    }
    if let Some(depth) = state.tray_depth.filter(|depth| *depth > 0) {
        segments.push(vec![theme.fg(ThemeColor::Dim, format!("depth {depth}"))]);
    }
    if let Some(memory) = &state.memory {
        segments.push(vec![theme.fg(ThemeColor::Dim, memory.text())]);
    }
    match detail {
        Detail::Overview => {}
        Detail::Details => segments.push(vec![theme.fg(ThemeColor::Dim, "details")]),
        Detail::All => segments.push(vec![theme.fg(ThemeColor::Dim, "expanded")]),
    }
    if let Some(dock) = &state.activity {
        segments.extend(activity_segments(dock, theme));
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
    let separator = theme.fg(ThemeColor::Dim, crate::glyphs::SEP);
    fit(
        &mut segments,
        Yielding {
            title: title_at,
            speed: speed_at,
        },
        room,
        line_width(std::slice::from_ref(&separator)),
    );
    let mut left: Line = Vec::new();
    for (index, segment) in segments.into_iter().enumerate() {
        if index > 0 {
            left.push(separator.clone());
        }
        left.extend(segment);
    }
    // The last resort for a row too short even for the fixed segments:
    // the composed left side cuts at the edge.
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

/// The segments that give way when the row is short, as indexes into
/// the segment list.
#[derive(Clone, Copy)]
struct Yielding {
    /// The session title.
    title: Option<usize>,
    /// The generation speed.
    speed: Option<usize>,
}

/// The columns `segments` take, joined by separators of `separator`
/// columns.
fn segments_width(segments: &[Line], separator: usize) -> usize {
    segments
        .iter()
        .map(|segment| line_width(segment))
        .sum::<usize>()
        + separator * segments.len().saturating_sub(1)
}

/// Cut the segment at `index` (never below `min` columns) by the
/// columns the row overflows `room`.
fn shrink(segments: &mut [Line], index: usize, min: usize, room: usize, separator: usize) {
    let overflow = segments_width(segments, separator).saturating_sub(room);
    let width = line_width(&segments[index]);
    let target = width.saturating_sub(overflow).max(min);
    if target < width {
        segments[index] = crate::chrome::truncate_spans_to_width(&segments[index], target);
    }
}

/// Fit `segments` into `room` columns: the title cuts first (down to
/// its narrowest cut), then the speed text (down to its narrowest cut),
/// then the title drops and the speed takes the room that frees -- or
/// drops too when that is less than its narrowest cut. The model, its
/// thinking level, the path, the `mem` gauge, the detail label and the
/// activity never cut here.
fn fit(segments: &mut Vec<Line>, yielding: Yielding, room: usize, separator: usize) {
    let speed_full = yielding.speed.map(|index| segments[index].clone());
    if let Some(title) = yielding.title {
        shrink(segments, title, TITLE_MIN_WIDTH, room, separator);
    }
    if let Some(speed) = yielding.speed {
        shrink(segments, speed, SPEED_MIN_WIDTH, room, separator);
    }
    if segments_width(segments, separator) <= room {
        return;
    }
    let mut speed = yielding.speed;
    if let Some(title) = yielding.title {
        segments.remove(title);
        speed = speed.map(|index| if index > title { index - 1 } else { index });
    }
    if let (Some(index), Some(full)) = (speed, speed_full) {
        let others = segments_width(segments, separator) - line_width(&segments[index]);
        let spare = room.saturating_sub(others);
        if line_width(&full) <= spare {
            segments[index] = full;
        } else if spare >= SPEED_MIN_WIDTH {
            segments[index] = crate::chrome::truncate_spans_to_width(&full, spare);
        } else {
            segments.remove(index);
        }
    }
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
    let Some(parsed) = ModelThinkingLevel::parse(level) else {
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
        theme.fg(context_color(context.tokens, context.context_window), value),
    ]
}

/// The tone of each usage band (omp `getContextUsageLevel`): dim below the
/// first band, then the tone of the highest band reached. The compiled
/// core decides the band (`bend/tui_color.bend` `band`: the shares 1/2,
/// 7/10 and 9/10 of the window the daemon serves; an unknown window
/// reaches none).
const CONTEXT_TONES: [ThemeColor; 4] = [
    ThemeColor::Dim,
    ThemeColor::Warning,
    ThemeColor::ContextHigh,
    ThemeColor::Error,
];

/// The usage tone of `tokens` in a `window`-token context.
fn context_color(tokens: u64, window: u64) -> ThemeColor {
    CONTEXT_TONES[eukhe_bend::rules::tui_color::band(tokens, window)]
}

/// omp `formatNumber`: 999, 1.5K, 128K, 1M, 2.5M, 1B.
pub(crate) fn format_count(count: u64) -> String {
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
            ActivityGroup::Subagents => {
                let mut spans =
                    vec![theme.fg(color(running), plural(running, "subagent", "subagents"))];
                // Running agents waiting for their provider's admission
                // slot (`providerMaxInFlight`).
                if dock.subagents_queued > 0 {
                    spans.push(theme.fg(ThemeColor::Dim, crate::glyphs::SEP));
                    spans.push(theme.fg(
                        ThemeColor::Warning,
                        format!("{} queued", dock.subagents_queued),
                    ));
                }
                (running > 0, spans)
            }
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
            ActivityGroup::Workflow => (
                dock.workflow_runs > 0,
                vec![theme.fg(
                    color(dock.workflow_runs),
                    plural(dock.workflow_runs, "workflow", "workflows"),
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
