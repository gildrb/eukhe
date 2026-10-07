//! The chat memory, after Victor Taelin's `OptChat` spec
//! (<https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449>):
//! one endless, append-only chat log,
//! a binary tree of one-line summaries over it, the fixed-budget view every
//! root turn starts from, and the background compactor that builds the tree.
//!
//! Layout under `<agent-dir>/chat/`:
//!
//! - `main/YYYY-MM-DD.jsonl`: one message per line, `{i, kind, text, size, date}`.
//! - `tree/YYYY-MM-DD.jsonl`: one node per line, `{l, i, text, size}`.
//! - `lock`: the owner's Unix socket. One process owns the chat for its whole
//!   life and is the only writer; every other process is its client.
//! - `turn`: locked by the process whose root turn holds the chat's
//!   root-turn lease (one root turn at a time across every process).
//!
//! Node `(l, i)` covers messages `[i·2^l, (i+1)·2^l)` and is named `id+n`
//! with `id = i·2^l` and `n = 2^l`. Level 0 summarizes one message; level
//! `l > 0` merges its two children. Nothing in these files is ever edited
//! or deleted.

mod browse;
mod chat;
mod compactor;
mod import;
mod prompts;
mod service;
mod store;
mod summarizer;
mod view;

use std::time::Duration;

pub use browse::{read_view, write_browse_page, BrowseSummary, ReadView};
pub use compactor::{Summarizer, SummarizerFuture};
pub use import::{import_optmem, import_sessions, ImportReport};
pub use prompts::{
    memory_system_layer, subagent_system_layer, AGENT_NAME, DATE_TOOL_DESCRIPTION,
    ZOOM_TOOL_DESCRIPTION,
};
pub use service::{KeyedAppend, Memory, MemoryStatus, RenderedView, TurnLease};
pub use summarizer::SettingsSummarizer;

/// Target size of one summary line, in UTF-8 bytes.
pub const NODE: usize = 512;
/// Budget of the view, in UTF-8 bytes of line text.
pub const VIEW: usize = 128_000;
/// Compactor calls running at once.
pub const JOBS: usize = 8;
/// Attempts per node to get a line under [`NODE`].
pub const TRIES: usize = 5;
/// Wait before a failed node is tried again.
pub const RETRY: Duration = Duration::from_secs(10);
/// Largest logged tool result, in characters; head and tail are kept.
pub const CAP: usize = 30_000;
/// Cache breakpoints inside the view, in characters.
pub const MARKS: [usize; 3] = [50_000, 80_000, 100_000];
/// The text of a view line whose message is not summarized yet.
pub const PLACEHOLDER: &str = "(not summarized yet: zoom it)";

/// Which side of the chat a session is: the root logs to the chat and
/// starts every fresh turn from the view; a subagent starts from the view
/// at its spawn and logs nothing (§9).
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
    /// The user's words; also reports of subagents and background work,
    /// which start with `[id] `.
    User,
    /// The agent's replies.
    Talk,
    /// The agent's tool calls, as text: name and JSON input.
    Tool,
    /// Tool results.
    Echo,
    /// Memories imported from an older system.
    Note,
}

impl Kind {
    /// The wire and display name.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Kind::User => "user",
            Kind::Talk => "talk",
            Kind::Tool => "tool",
            Kind::Echo => "echo",
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

/// Cap a text at [`CAP`] characters, keeping its head and tail and naming
/// what was cut. Texts within the cap pass through unchanged.
#[must_use]
pub fn cap_text(text: &str) -> String {
    let total = text.chars().count();
    if total <= CAP {
        return text.to_string();
    }
    let keep = CAP / 2;
    let cut = total - 2 * keep;
    let head_end = text
        .char_indices()
        .nth(keep)
        .map_or(text.len(), |(at, _)| at);
    let tail_start = text
        .char_indices()
        .nth(total - keep)
        .map_or(text.len(), |(at, _)| at);
    format!(
        "{}\n[... {cut} characters cut ...]\n{}",
        &text[..head_end],
        &text[tail_start..]
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cap_keeps_head_and_tail() {
        let text = format!("{}{}{}", "a".repeat(CAP), "b".repeat(10), "c".repeat(CAP));
        let cut = CAP + 10;
        assert_eq!(
            (cap_text(&text), cap_text("short")),
            (
                format!(
                    "{}\n[... {cut} characters cut ...]\n{}",
                    "a".repeat(CAP / 2),
                    "c".repeat(CAP / 2)
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
                    "{}\n[... 2 characters cut ...]\n{}",
                    "é".repeat(CAP / 2),
                    "é".repeat(CAP / 2)
                )
            )
        );
    }
}
