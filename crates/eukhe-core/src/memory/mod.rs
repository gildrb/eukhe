//! The chat memory, after Victor Taelin's `OptChat` spec
//! (<https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449>):
//! one endless, append-only chat log,
//! a binary tree of one-line summaries over it, the fixed-budget view every
//! root turn starts from, and the background compactor that builds the tree.
//!
//! Layout under `<agent-dir>/chat/`:
//!
//! - `main/YYYY-MM-DD.jsonl`: one message per line, `{i, kind, text, size, date}`.
//! - `images/<i>.json`: the images message `i` carried, written and fsynced
//!   before its line and never changed; `zoom(i, 1)` gives them back (§5).
//! - `tree/YYYY-MM-DD.jsonl`: one node per line, `{l, i, text, size}`, and
//!   one line per merge batch of the view, `{merge: [[l, i], ...]}`.
//! - `view.json`: the live view as `[l, i]` pairs, a cache: the view is the
//!   fold of the messages and the merge batches (§3.2), checked against it
//!   at load.
//! - `prompt.json`: the turns' system prompt and tools, which compactions
//!   reuse so they read the turns' cache entry (§4).
//! - `lock`: the owner's Unix socket. One process owns the chat for its whole
//!   life and is the only writer; every other process is its client.
//! - `turn`: locked by the process whose root turn holds the chat's
//!   root-turn lease (one root turn at a time across every process).
//!
//! Node `(l, i)` covers messages `[i·2^l, (i+1)·2^l)` and is named `id+n`
//! with `id = i·2^l` and `n = 2^l`. Level 0 summarizes one message; level
//! `l > 0` merges its two children. Nothing in the logs is ever edited or
//! deleted.

mod browse;
mod chat;
mod compactor;
mod import;
mod prompts;
mod saved;
mod service;
mod store;
mod summarizer;
mod tree;
mod view;

use std::time::Duration;

pub use browse::{read_view, write_browse_page, BrowseSummary, ReadView};
pub use compactor::{ResponseStarted, Summarizer, SummarizerFuture};
pub use import::{import_sessions, ImportReport};
pub use prompts::{
    memory_system_layer, subagent_system_layer, AGENT_NAME, DATE_TOOL_DESCRIPTION,
    ZOOM_TOOL_DESCRIPTION,
};
pub use saved::CompactionPrompt;
pub use service::{
    KeyedAppend, Memory, MemoryStatus, MemoryUpdates, RenderedView, TurnLease, Zoomed,
};
pub use summarizer::{configured_memory_model, SettingsSummarizer};

/// Target size of one summary line, in UTF-8 bytes.
pub const NODE: usize = 512;
/// The view's ceiling, in UTF-8 bytes of line text: once the view passes
/// it, one batch merges it down to [`VIEW_FLOOR`] (§3.2).
pub const VIEW_CEILING: usize = 128_000;
/// The size a batch merges the view down to.
pub const VIEW_FLOOR: usize = 64_000;
/// The compaction view's ceiling: past it, it merges down to
/// [`COMPACTION_FLOOR`] (§4).
pub const COMPACTION_CEILING: usize = 32_000;
/// The size the compaction view merges down to.
pub const COMPACTION_FLOOR: usize = 16_000;
/// View lines per cache block: one cache mark sits on the last whole block
/// (§3.3).
pub const BLOCK: usize = 4;
/// Compactor calls running at once; also how many unbuilt lines may sit
/// before a message whose node starts.
pub const JOBS: usize = 8;
/// Attempts per node to get a line under [`NODE`].
pub const TRIES: usize = 5;
/// Wait before a failed node is tried again while a turn waits for the
/// view. A new message or a turn's wait tries every failed node again at
/// once; an idle chat makes no call for a failed node (§4).
pub const RETRY: Duration = Duration::from_secs(10);
/// Largest logged tool result, in characters; head and tail are kept. Any
/// other text longer than this is logged as several messages in a row.
pub const CAP: usize = 30_000;
/// The text of a view line whose message is not summarized yet.
pub const PLACEHOLDER: &str = "(not summarized yet: zoom it)";

/// Which side of the chat a session is: the root logs to the chat and
/// starts every fresh turn from the view; a subagent starts from the view
/// at its spawn and logs nothing to the chat (§6: its own steps stay in its
/// own log).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryRole {
    Root,
    Subagent,
}

/// The directory of the chat memory under an agent directory.
#[must_use]
pub fn chat_dir(agent_dir: &std::path::Path) -> std::path::PathBuf {
    agent_dir.join("chat")
}

/// The idempotency key of a keyed append ([`Memory::append_keyed`]): the
/// appender's scope (one logger, e.g. one conversation of one session) and
/// the message's position in that scope, counted from 0 in log order.
/// Stored on the logged line, so the owner knows every scope's newest key
/// after a restart.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct AppendKey {
    pub scope: String,
    pub seq: u64,
}

/// What a logged message is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Kind {
    /// The user's words.
    User,
    /// The agent's replies (the gist's `unii`, renamed to the agent).
    /// Logs written before the rename call them `talk`.
    #[serde(alias = "talk")]
    Eukhe,
    /// The agent's tool calls, as text: name and JSON input.
    Tool,
    /// Tool results.
    Echo,
    /// A subagent's or background task's report, starting `[Name]`.
    Work,
    /// A memory imported from before the chat (§1).
    Note,
}

impl Kind {
    /// The wire and display name.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Kind::User => "user",
            Kind::Eukhe => "eukhe",
            Kind::Tool => "tool",
            Kind::Echo => "echo",
            Kind::Work => "work",
            Kind::Note => "note",
        }
    }
}

impl std::fmt::Display for Kind {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// `kind + ": " + text`: a message as the tree and `zoom` show it.
#[must_use]
pub fn labeled(kind: Kind, text: &str) -> String {
    format!("{kind}: {text}")
}

/// Cap a text at [`CAP`] characters in all (§1), keeping its head and tail
/// and naming what was cut; the marker counts against the cap. Texts
/// within the cap pass through unchanged.
#[must_use]
pub fn cap_text(text: &str) -> String {
    let total = text.chars().count();
    if total <= CAP {
        return text.to_string();
    }
    let marker = |cut: usize| format!("\n[... {cut} characters cut ...]\n");
    // The marker's length depends on the count it names: settle both.
    let mut cut = total - CAP;
    let keep = loop {
        let keep = CAP - marker(cut).chars().count();
        if total - keep == cut {
            break keep;
        }
        cut = total - keep;
    };
    let head = keep / 2;
    let head_end = text
        .char_indices()
        .nth(head)
        .map_or(text.len(), |(at, _)| at);
    let tail_start = text
        .char_indices()
        .nth(head + cut)
        .map_or(text.len(), |(at, _)| at);
    format!(
        "{}{}{}",
        &text[..head_end],
        marker(cut),
        &text[tail_start..]
    )
}

/// Split a text longer than [`CAP`] characters into pieces of at most
/// [`CAP`] characters, each ending at its last line break when one falls in
/// its second half; the pieces concatenate back to `text` (§1: a long text
/// is never cut, it is logged as several messages in a row). A text within
/// the cap is one piece.
#[must_use]
pub fn split_text(text: &str) -> Vec<String> {
    let mut pieces = Vec::new();
    let mut rest = text;
    loop {
        let Some((limit, _)) = rest.char_indices().nth(CAP) else {
            pieces.push(rest.to_string());
            return pieces;
        };
        let window = &rest[..limit];
        let half = window
            .char_indices()
            .nth(CAP / 2)
            .map_or(limit, |(at, _)| at);
        let end = window
            .rfind('\n')
            .filter(|at| *at >= half)
            .map_or(limit, |at| at + 1);
        pieces.push(rest[..end].to_string());
        rest = &rest[end..];
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The clipped text is [`CAP`] characters in all, marker included: so
    /// a clipped tool result is never split again.
    #[test]
    fn cap_keeps_head_and_tail_within_the_cap() {
        let text = format!("{}{}{}", "a".repeat(CAP), "b".repeat(10), "c".repeat(CAP));
        let capped = cap_text(&text);
        assert_eq!(
            (capped.chars().count(), capped, cap_text("short")),
            (
                CAP,
                format!(
                    "{}\n[... 30042 characters cut ...]\n{}",
                    "a".repeat(14_984),
                    "c".repeat(14_984)
                ),
                "short".to_string()
            )
        );
    }

    #[test]
    fn cap_counts_characters_not_bytes() {
        let within = "é".repeat(CAP);
        let over = "é".repeat(CAP + 2);
        assert_eq!(
            (cap_text(&within), cap_text(&over)),
            (
                within,
                format!(
                    "{}\n[... 31 characters cut ...]\n{}",
                    "é".repeat(14_985),
                    "é".repeat(14_986)
                )
            )
        );
    }

    /// A long text is split, never cut: at a line break in a piece's second
    /// half, else at the cap; the pieces join back to the text.
    #[test]
    fn long_texts_split_into_messages_without_losing_anything() {
        let first = format!("{}\n", "a".repeat(CAP - 10));
        let second = "é".repeat(CAP + 5);
        let text = format!("{first}{second}");
        assert_eq!(
            (split_text(&text), split_text("short")),
            (
                vec![first, "é".repeat(CAP), "é".repeat(5)],
                vec!["short".to_string()]
            )
        );
    }

    /// Logs written before the agent-reply kind took the agent's name say
    /// `talk`: they keep loading, as `eukhe`, and new lines say `eukhe`.
    #[test]
    fn old_talk_lines_read_as_eukhe() {
        let old: Kind = serde_json::from_str("\"talk\"").unwrap();
        assert_eq!(
            (old, serde_json::to_string(&old).unwrap()),
            (Kind::Eukhe, "\"eukhe\"".to_string())
        );
    }
}
