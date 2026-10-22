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

/// When a live `memory_update` lands, relative to the model requests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UpdateTiming {
    /// During a request: the compactor works alongside it.
    InRequest,
    /// Between requests (the tail of a turn, an idle session): the view
    /// moves, the gauge stays at rest.
    Idle,
}

/// The status line's `mem` gauge: the view's size, and whether the
/// compactor is working on it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemoryGauge {
    /// The view's size, in bytes of line text.
    pub view_bytes: u64,
    /// The compactor is working: a live update landed during the current
    /// request and the request has not ended.
    pub working: bool,
}

impl MemoryGauge {
    /// The gauge a `get_memory` status seeds: the size, the compactor at
    /// rest.
    #[must_use]
    pub fn seeded(view_bytes: u64) -> Self {
        Self {
            view_bytes,
            working: false,
        }
    }

    /// The gauge after one live `update`: the view's new size, the
    /// compactor working when the update lands inside a request. A
    /// gauge the status never seeded starts here.
    #[must_use]
    pub fn after(update: &MemoryUpdate, timing: UpdateTiming) -> Self {
        let view_bytes = match update {
            MemoryUpdate::Summarized { view_bytes, .. } => *view_bytes,
            MemoryUpdate::Merged { after_bytes, .. } => *after_bytes,
        };
        let working = match timing {
            UpdateTiming::InRequest => true,
            UpdateTiming::Idle => false,
        };
        Self {
            view_bytes,
            working,
        }
    }

    /// A request began or ended: the compactor's work of the last request
    /// is over.
    pub fn settle(&mut self) {
        self.working = false;
    }

    /// `mem 1.1K/128K`: the view's size against the ceiling, formatted
    /// like the context segment's sizes (`format_count`); ` ~` follows
    /// while the compactor works. Never a count, never a node id.
    #[must_use]
    pub fn text(&self) -> String {
        let mut text = format!(
            "mem {}/{}",
            crate::status_line::format_count(self.view_bytes),
            crate::status_line::format_count(MEMORY_VIEW_CEILING)
        );
        if self.working {
            text.push(' ');
            text.push_str(crate::glyphs::DOT_HALF);
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
