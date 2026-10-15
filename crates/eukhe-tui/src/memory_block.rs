//! The chat memory in the transcript (`OptChat`): the live `memory_update`
//! rows the compactor's progress shows as, plus the status header and the
//! sanitizing helpers the `/memory` tree ([`crate::memory_tree`]) shares.
//! Client-side display only: never logged into the chat, never replayed.
//! Line text is raw, never markdown.

use eukhe_types::daemon::{
    MemoryStatusSnapshot, MemoryUpdate, MEMORY_VIEW_CEILING, MEMORY_VIEW_FLOOR,
};

use crate::chat::Detail;
use crate::style::Style;
use crate::theme::{Theme, ThemeColor};
use crate::{Line, Span};

/// A size in kilobytes (1000 bytes) to one decimal, rounded: `87.2 KB`.
/// The memory's sizes are decimal (its ceiling is 128,000 bytes), and the
/// startup chat-view row shares the convention.
#[must_use]
pub(crate) fn format_kb(bytes: u64) -> String {
    let tenths = bytes.saturating_mul(10).saturating_add(500) / 1000;
    format!("{}.{} KB", tenths / 10, tenths % 10)
}

/// `n thing` / `n things`.
fn count(n: u64, one: &str, many: &str) -> String {
    format!("{n} {}", if n == 1 { one } else { many })
}

/// How many of a coalesced row's newest node ids the summary names; older
/// ones read as `... +N more`.
const SHOWN_IDS: usize = 8;

/// The live row's text: `memory: summarized 41+1, 42+1 (view 87.2 KB)`
/// (past [`SHOWN_IDS`] nodes, `memory: summarized ... +12 more, 6+2, ...`)
/// or `memory: merged 37 pairs, view 128.4 KB -> 63.9 KB`.
#[must_use]
pub(crate) fn memory_update_summary(update: &MemoryUpdate) -> String {
    match update {
        MemoryUpdate::Summarized { lines, view_bytes } => {
            let hidden = lines.len().saturating_sub(SHOWN_IDS);
            let more = (hidden > 0).then(|| format!("{} +{hidden} more", crate::glyphs::ELLIPSIS));
            let ids = more
                .into_iter()
                .chain(
                    lines[hidden..]
                        .iter()
                        .map(|line| format!("{}+{}", line.id, line.count)),
                )
                .collect::<Vec<_>>()
                .join(", ");
            format!("memory: summarized {ids} (view {})", format_kb(*view_bytes))
        }
        MemoryUpdate::Merged {
            pairs,
            before_bytes,
            after_bytes,
        } => format!(
            "memory: merged {}, view {} {} {}",
            count(*pairs, "pair", "pairs"),
            format_kb(*before_bytes),
            crate::glyphs::ARROW,
            format_kb(*after_bytes),
        ),
    }
}

/// Fold `update` into the live row `row` when both are the same kind:
/// summaries accumulate their nodes and take the newest view size; merges
/// add their pairs and span the first size to the last. A different kind
/// comes back unfolded (it starts its own row).
pub(crate) fn fold_memory_update(
    row: &mut MemoryUpdate,
    update: MemoryUpdate,
) -> Option<MemoryUpdate> {
    match (row, update) {
        (
            MemoryUpdate::Summarized { lines, view_bytes },
            MemoryUpdate::Summarized {
                lines: more,
                view_bytes: newest,
            },
        ) => {
            lines.extend(more);
            *view_bytes = newest;
            None
        }
        (
            MemoryUpdate::Merged {
                pairs, after_bytes, ..
            },
            MemoryUpdate::Merged {
                pairs: more,
                after_bytes: newest,
                ..
            },
        ) => {
            *pairs = pairs.saturating_add(more);
            *after_bytes = newest;
            None
        }
        (MemoryUpdate::Summarized { .. }, update @ MemoryUpdate::Merged { .. })
        | (MemoryUpdate::Merged { .. }, update @ MemoryUpdate::Summarized { .. }) => Some(update),
    }
}

/// The view's size after `update`, for the status gauge.
#[must_use]
pub(crate) fn memory_update_view_bytes(update: &MemoryUpdate) -> u64 {
    match update {
        MemoryUpdate::Summarized { view_bytes, .. } => *view_bytes,
        MemoryUpdate::Merged { after_bytes, .. } => *after_bytes,
    }
}

/// The `/memory` tree's header: `memory: T messages, view 87.2 KB / 128.0 KB
/// (floor 64.0 KB), 214 lines, 2 unsummarized, 1 compaction running, model
/// anthropic/claude-haiku-4-5`.
#[must_use]
pub(crate) fn memory_status_header(status: &MemoryStatusSnapshot) -> String {
    format!(
        "memory: {}, view {} / {} (floor {}), {}, {} unsummarized, {} running, model {}",
        count(status.messages, "message", "messages"),
        format_kb(status.view_bytes),
        format_kb(MEMORY_VIEW_CEILING),
        format_kb(MEMORY_VIEW_FLOOR),
        count(status.lines, "line", "lines"),
        status.unsummarized,
        count(status.running, "compaction", "compactions"),
        status.model.as_deref().unwrap_or("default"),
    )
}

/// `text` wrapped under a hanging indent: the first row after `indent`
/// columns, the continuation rows two columns deeper, every row within
/// `width`.
pub(crate) fn wrapped(text: &str, indent: usize, style: Style, width: usize) -> Vec<Line> {
    let content = width.saturating_sub(indent + 2).max(1);
    crate::width::wrap_text(text, content)
        .into_iter()
        .enumerate()
        .map(|(index, row)| styled_row(row, if index == 0 { indent } else { indent + 2 }, style))
        .collect()
}

fn styled_row(row: Line, indent: usize, style: Style) -> Line {
    let mut out: Line = vec![Span::raw(" ".repeat(indent))];
    out.extend(
        row.into_iter()
            .map(|span| Span::styled(span.content, style)),
    );
    out
}

/// `text` as one display line: line breaks (`\r\n`, `\n`, `\r`, the
/// Unicode separators), escape sequences and every other control character
/// (a tab, a backspace) as spaces, so a row never moves the terminal's
/// cursor and keeps its `id+n|` prefix. Display sanitization only: the view
/// the model sees is the core's.
pub(crate) fn one_line(text: &str) -> String {
    crate::ansi::strip_ansi(&text.replace("\r\n", " "))
        .chars()
        .map(|c| match c {
            '\u{2028}' | '\u{2029}' => ' ',
            c if c.is_control() => ' ',
            c => c,
        })
        .collect()
}

/// One live `memory_update` row: an optional leading blank, the summary,
/// and -- at the `all` level only -- each summarized line as an indented
/// `id+n|text` row (its text on one line).
pub(crate) fn render_memory_update(
    update: &MemoryUpdate,
    detail: Detail,
    theme: &Theme,
    width: usize,
    leading: bool,
) -> Vec<Line> {
    let mut out = Vec::new();
    if leading {
        out.push(Vec::new());
    }
    let muted = theme.fg_style(ThemeColor::Muted);
    out.extend(wrapped(&memory_update_summary(update), 1, muted, width));
    let show_lines = match detail {
        Detail::Overview | Detail::Details => false,
        Detail::All => true,
    };
    match update {
        MemoryUpdate::Summarized { lines, .. } if show_lines => {
            let dim = theme.fg_style(ThemeColor::Dim);
            for line in lines {
                let flat = one_line(&line.text);
                let text = format!("{}+{}|{flat}", line.id, line.count);
                out.extend(wrapped(&text, 3, dim, width));
            }
        }
        MemoryUpdate::Summarized { .. } | MemoryUpdate::Merged { .. } => {}
    }
    out
}

/// The status line's gauge: `mem 87/128K`, the view's size against the
/// ceiling in whole kilobytes.
#[must_use]
pub(crate) fn memory_gauge(view_bytes: u64) -> String {
    format!(
        "mem {}/{}K",
        view_bytes.saturating_add(500) / 1000,
        MEMORY_VIEW_CEILING / 1000
    )
}

#[cfg(test)]
mod tests;
