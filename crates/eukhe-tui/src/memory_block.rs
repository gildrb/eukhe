//! The chat memory in the chrome (`OptChat`): the status line's `mem`
//! gauge the compactor's live `memory_update`s move, plus the status
//! header and the sanitizing helpers the `/memory` tree
//! ([`crate::memory_tree`]) shares. Client-side display only: never
//! logged into the chat, never replayed, never a transcript row. Line
//! text is raw, never markdown.

use eukhe_types::daemon::{
    MemoryStatusSnapshot, MemoryUpdate, MEMORY_VIEW_CEILING, MEMORY_VIEW_FLOOR,
};

use crate::style::Style;
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

/// What the compactor did since the current request began, as the
/// gauge's suffix. Folded from each live update like the compactor's own
/// batches: summaries accumulate their nodes; a merge replaces whatever
/// came before (the view dropped, the earlier nodes are in it) and later
/// merges add their pairs; a summary after a merge starts a fresh count.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryActivity {
    /// Nodes built: `~N`.
    Summarized { nodes: u64 },
    /// Pairs merged down: `vN`.
    Merged { pairs: u64 },
}

impl MemoryActivity {
    /// `previous` folded with `update`.
    #[must_use]
    fn fold(previous: Option<Self>, update: &MemoryUpdate) -> Self {
        match (previous, update) {
            (Some(Self::Summarized { nodes }), MemoryUpdate::Summarized { lines, .. }) => {
                Self::Summarized {
                    nodes: nodes.saturating_add(lines.len() as u64),
                }
            }
            (None | Some(Self::Merged { .. }), MemoryUpdate::Summarized { lines, .. }) => {
                Self::Summarized {
                    nodes: lines.len() as u64,
                }
            }
            (Some(Self::Merged { pairs }), MemoryUpdate::Merged { pairs: more, .. }) => {
                Self::Merged {
                    pairs: pairs.saturating_add(*more),
                }
            }
            (None | Some(Self::Summarized { .. }), MemoryUpdate::Merged { pairs, .. }) => {
                Self::Merged { pairs: *pairs }
            }
        }
    }

    /// The gauge suffix: `~3` (nodes summarized), `v37` (pairs merged).
    fn suffix(self) -> String {
        match self {
            Self::Summarized { nodes } => format!("{}{nodes}", crate::glyphs::DOT_HALF),
            Self::Merged { pairs } => format!("{}{pairs}", crate::glyphs::DOWN),
        }
    }
}

/// The status line's `mem` gauge: the view's size, and what the compactor
/// did to it since the current request began.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemoryGauge {
    /// The view's size, in bytes of line text.
    pub view_bytes: u64,
    /// The compactor's activity since the request began; `None` once a
    /// request begins, until the next update.
    pub activity: Option<MemoryActivity>,
}

impl MemoryGauge {
    /// The gauge a `get_memory` status seeds: the size, no activity yet.
    #[must_use]
    pub fn seeded(view_bytes: u64) -> Self {
        Self {
            view_bytes,
            activity: None,
        }
    }

    /// `gauge` after one live `update`: the view's new size, the activity
    /// folded in. A gauge the status never seeded starts here.
    #[must_use]
    pub fn after(gauge: Option<Self>, update: &MemoryUpdate) -> Self {
        let view_bytes = match update {
            MemoryUpdate::Summarized { view_bytes, .. } => *view_bytes,
            MemoryUpdate::Merged { after_bytes, .. } => *after_bytes,
        };
        Self {
            view_bytes,
            activity: Some(MemoryActivity::fold(
                gauge.and_then(|gauge| gauge.activity),
                update,
            )),
        }
    }

    /// A request began: the activity count starts over.
    pub fn begin_request(&mut self) {
        self.activity = None;
    }

    /// `mem 87/128K`: the view's size against the ceiling in whole
    /// kilobytes; then, after a live update, the activity: `mem 91/128K
    /// ~3` (3 nodes summarized since the request began), `mem 64/128K
    /// v37` (37 pairs merged). Never a node id.
    #[must_use]
    pub fn text(&self) -> String {
        let mut text = format!(
            "mem {}/{}K",
            self.view_bytes.saturating_add(500) / 1000,
            MEMORY_VIEW_CEILING / 1000
        );
        if let Some(activity) = self.activity {
            text.push(' ');
            text.push_str(&activity.suffix());
        }
        text
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

#[cfg(test)]
mod tests;
