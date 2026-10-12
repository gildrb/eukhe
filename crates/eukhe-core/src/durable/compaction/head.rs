//! The compaction head of a durable conversation: the typed summary a
//! `pi.compaction` entry carries, its rendering (the entry's model text),
//! what update mode reads from it, and the inputs the summarizer gets.

use eukhe_chord::json::JsonError;
use eukhe_durable::entries::{CompactionSummary, COMPACTION_ENTRY};
use eukhe_durable::types::EntryRecord;
use eukhe_types::pi_ai::{AssistantContentBlock, Message};
use eukhe_types::session::AgentMessage;

use super::utils::format_file_operations;
use crate::durable::messages::{
    COMPACTION_SUMMARY_PREFIX, COMPACTION_SUMMARY_SUFFIX, HARNESS_DIGEST_PREFIX,
    HARNESS_DIGEST_SUFFIX,
};

/// The summary as transcripts show it: the summarizer's text, then the
/// file-list blocks.
#[must_use]
pub fn summary_body(summary: &CompactionSummary) -> String {
    format!(
        "{}{}",
        summary.summary,
        format_file_operations(&summary.read_files, &summary.modified_files)
    )
}

/// The model text of a summary: the harness-digest block when a digest
/// rendered, then the `[compaction-summary]`-wrapped [`summary_body`].
#[must_use]
pub fn rendered_summary(summary: &CompactionSummary) -> String {
    let wrapped = format!(
        "{COMPACTION_SUMMARY_PREFIX}{}{COMPACTION_SUMMARY_SUFFIX}",
        summary_body(summary)
    );
    match &summary.digest {
        Some(digest) => format!(
            "{HARNESS_DIGEST_PREFIX}{}{HARNESS_DIGEST_SUFFIX}\n\n{wrapped}",
            digest.digest
        ),
        None => wrapped,
    }
}

/// The summary text of a `pi.compaction` entry as transcripts show it: the
/// typed summary's [`summary_body`], or the model text of a summary the
/// built-in summarizer wrote.
///
/// # Errors
///
/// The entry's data does not decode.
pub fn compaction_summary_text(entry: &EntryRecord) -> Result<String, JsonError> {
    let Some(compaction) = COMPACTION_ENTRY.narrow(entry.clone())? else {
        return Ok(String::new());
    };
    Ok(match &compaction.data().summary {
        Some(summary) => summary_body(summary),
        None => user_text(entry.model.as_deref().unwrap_or_default())
            .unwrap_or_default()
            .to_owned(),
    })
}

/// What update mode continues from: the previous summary text (`None` when
/// nothing summarizable remains) and the file lists it carried.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct PreviousSummary {
    pub(crate) summary: Option<String>,
    pub(crate) read_files: Vec<String>,
    pub(crate) modified_files: Vec<String>,
}

/// The [`PreviousSummary`] of a compaction head: its typed summary, or the
/// model text of a summary the built-in summarizer wrote (no file lists).
///
/// # Errors
///
/// The entry's data does not decode.
pub(crate) fn previous_summary(head: &EntryRecord) -> Result<PreviousSummary, JsonError> {
    let Some(compaction) = COMPACTION_ENTRY.narrow(head.clone())? else {
        return Ok(PreviousSummary::default());
    };
    Ok(match &compaction.data().summary {
        Some(summary) => PreviousSummary {
            summary: (!summary.summary.trim().is_empty()).then(|| summary.summary.clone()),
            read_files: summary.read_files.clone(),
            modified_files: summary.modified_files.clone(),
        },
        None => PreviousSummary {
            summary: user_text(head.model.as_deref().unwrap_or_default()).map(str::to_owned),
            read_files: Vec::new(),
            modified_files: Vec::new(),
        },
    })
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
    use eukhe_durable::entries::HarnessDigest;

    use super::*;

    #[test]
    fn rendered_summary_leads_with_the_digest_and_carries_the_file_lists() {
        let summary = CompactionSummary {
            summary: "The story so far.".to_owned(),
            read_files: vec!["/a.rs".to_owned()],
            modified_files: Vec::new(),
            digest: Some(HarnessDigest {
                digest: "d".to_owned(),
                state_fingerprint: "f".to_owned(),
            }),
        };
        assert_eq!(
            rendered_summary(&summary),
            format!(
                "{HARNESS_DIGEST_PREFIX}d{HARNESS_DIGEST_SUFFIX}\n\n{COMPACTION_SUMMARY_PREFIX}The story so far.\n\n<read-files>\n/a.rs\n</read-files>{COMPACTION_SUMMARY_SUFFIX}"
            )
        );
    }
}
