//! Parsing the compaction head of a durable conversation: the previous
//! summary the update-mode summarizer merges, and the anchors and file
//! lists it carries. The old engine stored these on the compaction entry
//! (`summary`, `details.readFiles`/`modifiedFiles`); the durable
//! `pi.compaction` entry carries only the wrapped summary text, so the
//! update-mode inputs are read back out of that text — the summary the
//! eukhe extension writes is canonical (digest block, `[compaction-summary]`
//! wrapper, file-list blocks), so the parse is exact.

use eukhe_types::pi_ai::{AssistantContentBlock, Message};
use eukhe_types::session::AgentMessage;

use crate::session_engine::compaction_utils::strip_file_list_blocks;
use crate::session_engine::messages::{
    COMPACTION_SUMMARY_PREFIX, COMPACTION_SUMMARY_SUFFIX, HARNESS_DIGEST_PREFIX,
    HARNESS_DIGEST_SUFFIX,
};

/// The wrapper the durable compaction task places around every summary
/// (pi-durable `compaction/prompt.ts` `SUMMARY_PREFIX`/`SUMMARY_SUFFIX`).
const DURABLE_SUMMARY_PREFIX: &str =
    "The conversation history before this point was compacted into the following summary:\n\n<summary>\n";
const DURABLE_SUMMARY_SUFFIX: &str = "\n</summary>";

/// The summary as the user reads it: the durable wrapper, the leading
/// harness-digest block, and the `[compaction-summary]` wrapper off; the
/// file-list blocks stay (the old engine's entry `summary`).
#[must_use]
pub fn summary_body(wrapped: &str) -> &str {
    let unwrapped = wrapped
        .strip_prefix(DURABLE_SUMMARY_PREFIX)
        .and_then(|text| text.strip_suffix(DURABLE_SUMMARY_SUFFIX))
        .unwrap_or(wrapped);
    let without_digest = strip_digest_block(unwrapped);
    without_digest
        .strip_prefix(COMPACTION_SUMMARY_PREFIX)
        .and_then(|text| text.strip_suffix(COMPACTION_SUMMARY_SUFFIX))
        .unwrap_or(without_digest)
}

/// The raw summary of a wrapped compaction-summary text: [`summary_body`]
/// with the file-list blocks stripped (they are re-appended mechanically
/// after the summarizer answers, exactly like the old engine's TS #2385
/// rule; the digest is re-rendered fresh per compaction). The result is
/// the update-mode `previousSummary`; `None` when nothing summarizable
/// remains (a digest-only or file-lists-only head).
#[must_use]
pub fn previous_summary(wrapped: &str) -> Option<String> {
    let stripped = strip_file_list_blocks(summary_body(wrapped));
    (!stripped.is_empty()).then_some(stripped)
}

/// Remove a leading harness-digest frame (the block the eukhe summary
/// leads with when the digest rendered); the following blank line strips
/// with it. A digest frame later in the text is a hand-written summary and
/// stays.
#[must_use]
pub fn strip_digest_block(text: &str) -> &str {
    let Some(after_prefix) = text.strip_prefix(HARNESS_DIGEST_PREFIX) else {
        return text;
    };
    let Some(end) = after_prefix.find(HARNESS_DIGEST_SUFFIX) else {
        return text;
    };
    let mut rest = &after_prefix[end + HARNESS_DIGEST_SUFFIX.len()..];
    if rest.starts_with("\n\n") {
        rest = &rest[2..];
    }
    rest
}

/// The digest frame the compaction summary leads with when the digest
/// rendered (the old engine's `HARNESS_DIGEST_PREFIX` block).
#[must_use]
pub fn digest_block(digest: &str) -> String {
    format!("{HARNESS_DIGEST_PREFIX}{digest}{HARNESS_DIGEST_SUFFIX}\n\n")
}

/// The `[compaction-summary]`-wrapped presentation of a summary body (the
/// old engine's compaction-summary user message).
#[must_use]
pub fn wrapped_summary(body: &str) -> String {
    format!("{COMPACTION_SUMMARY_PREFIX}{body}{COMPACTION_SUMMARY_SUFFIX}")
}

/// The file lists a previous summary's `<read-files>`/`<modified-files>`
/// blocks carried, one path per line, empty names dropped. The durable
/// entry has no `details`, so the blocks in the summary text are the
/// carrier the next compaction's merged lists continue from.
#[must_use]
pub fn file_lists(text: &str) -> (Vec<String>, Vec<String>) {
    (
        block_lines(text, "read-files"),
        block_lines(text, "modified-files"),
    )
}

/// The non-empty lines of the `<name>` block, when the block is present.
fn block_lines(text: &str, name: &str) -> Vec<String> {
    let open = format!("<{name}>\n");
    let close = format!("\n</{name}>");
    let Some(start) = text.find(&open) else {
        return Vec::new();
    };
    let after = &text[start + open.len()..];
    let Some(end) = after.find(&close) else {
        return Vec::new();
    };
    after[..end]
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect()
}

/// Maximum characters kept from the retained tail for the recency anchor
/// (TS #2385 `RECENT_STATE_ANCHOR_MAX_CHARS`); the end holds the newest
/// state.
const RECENT_STATE_ANCHOR_MAX_CHARS: usize = 2_000;

/// The newest retained assistant text — the recency anchor (TS #2385
/// `extractRecentStateAnchor`) — over the kept tail's model messages,
/// oldest-first: scanning newest-first, the first assistant message whose
/// text blocks join to non-empty trimmed text wins; a longer text keeps
/// its tail. Assistants without text (tool-call or thinking-only) skip.
#[must_use]
pub fn recent_state_anchor(messages: &[&Message]) -> Option<String> {
    for message in messages.iter().rev() {
        let Message::Assistant(assistant) = message else {
            continue;
        };
        let text = assistant
            .content
            .iter()
            .filter_map(|block| match block {
                AssistantContentBlock::Text(text) => Some(text.text.as_str()),
                _ => None,
            })
            .collect::<Vec<_>>()
            .join("\n")
            .trim()
            .to_owned();
        if text.is_empty() {
            continue;
        }
        let chars = text.chars().count();
        return Some(if chars > RECENT_STATE_ANCHOR_MAX_CHARS {
            text.chars()
                .skip(chars - RECENT_STATE_ANCHOR_MAX_CHARS)
                .collect()
        } else {
            text
        });
    }
    None
}

/// The first user text of a model context (the summary a compaction head
/// entry carries).
#[must_use]
pub fn user_text(messages: &[Message]) -> Option<&str> {
    messages.first().and_then(|message| match message {
        Message::User(user) => match &user.content {
            eukhe_types::pi_ai::UserContent::Text(text) => Some(text.as_str()),
            eukhe_types::pi_ai::UserContent::Blocks(blocks) => {
                blocks.iter().find_map(|block| match block {
                    eukhe_types::pi_ai::UserContentBlock::Text(text) => Some(text.text.as_str()),
                    eukhe_types::pi_ai::UserContentBlock::Image(_) => None,
                })
            }
        },
        _ => None,
    })
}

/// The messages of `entries` in order, flattened (each entry's model
/// context in entry order).
#[must_use]
pub fn flattened_models<'a>(
    entries: &'a [&'a eukhe_durable::types::EntryRecord],
) -> Vec<&'a Message> {
    entries
        .iter()
        .filter_map(|entry| entry.model.as_deref())
        .flatten()
        .collect()
}

/// The session wire shape of `messages` (the summarizer's serializer
/// input): the same JSON round-trip the refinement planner uses.
pub fn agent_messages(messages: &[&Message]) -> anyhow::Result<Vec<AgentMessage>> {
    messages
        .iter()
        .filter(|message| !matches!(message, Message::System(_)))
        .map(|message| Ok(serde_json::from_value(serde_json::to_value(message)?)?))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const WRAPPED: &str = "The conversation history before this point was compacted into the following summary:\n\n<summary>\n[harness-digest]\n\nThe persistent memories produced across this session so far:\n\n<harness_state>\ndigest text\n</harness_state>\n\n[compaction-summary]\n\nThe conversation history before this point was compacted into the following summary.\nThe retained messages below are authoritative; this summary may lag behind them.\n\n<summary>\nThe story so far.\n<read-files>\n/a.rs\n/b.rs\n</read-files>\n</summary>\n</summary>";

    #[test]
    fn previous_summary_strips_every_mechanical_layer() {
        assert_eq!(
            previous_summary(WRAPPED).as_deref(),
            Some("The story so far.")
        );
    }

    #[test]
    fn previous_summary_is_none_for_a_digest_only_head() {
        let digest_only = format!(
            "{DURABLE_SUMMARY_PREFIX}{HARNESS_DIGEST_PREFIX}d{HARNESS_DIGEST_SUFFIX}\n\n{DURABLE_SUMMARY_SUFFIX}"
        );
        assert_eq!(previous_summary(&digest_only), None);
    }

    #[test]
    fn a_foreign_wrapped_text_still_yields_its_body() {
        // A summary the harness placed without the eukhe layers (the
        // built-in pi-durable summarizer, or an imported session): the
        // durable wrapper strips and the body passes through.
        assert_eq!(
            previous_summary("The conversation history before this point was compacted into the following summary:\n\n<summary>\nplain\n</summary>").as_deref(),
            Some("plain")
        );
    }

    #[test]
    fn strip_digest_block_keeps_a_mid_text_frame() {
        let text = format!("a\n\n{HARNESS_DIGEST_PREFIX}d{HARNESS_DIGEST_SUFFIX}\n\nb");
        assert_eq!(strip_digest_block(&text), text);
    }

    #[test]
    fn file_lists_read_both_blocks() {
        let (read, modified) = file_lists(WRAPPED);
        assert_eq!(read, vec!["/a.rs", "/b.rs"]);
        assert!(modified.is_empty());
    }

    #[test]
    fn wrapped_summary_round_trips_through_previous_summary() {
        let body = "body text";
        assert_eq!(
            previous_summary(&wrapped_summary(body)).as_deref(),
            Some(body)
        );
    }

    #[test]
    fn digest_block_leads_the_wrapped_body() {
        let text = format!("{}{}", digest_block("d"), wrapped_summary("s"));
        assert!(text.starts_with(HARNESS_DIGEST_PREFIX));
        assert_eq!(previous_summary(&text).as_deref(), Some("s"));
    }
}
