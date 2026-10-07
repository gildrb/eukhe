//! Range selection and context size (spec §8.3, §8.7): pure functions of a
//! [`ContextView`] shared by the compaction task and generation's threshold
//! and overflow checks.

use std::collections::HashSet;

use eukhe_pi_ai::utils::estimate::{calculate_context_tokens, estimate_message_tokens};
use eukhe_types::pi_ai::{AssistantContentBlock, AssistantMessage, Message};

use crate::harness::context::order_tool_results;
use crate::harness::types::ContextView;

/// Index in `view.entries` of the first entry a summary keeps, or `None`
/// when there is nothing to compact (spec §8.7). Walks back from the tail
/// until `keep_recent_tokens` are kept, then cuts at the first candidate at or
/// after that entry: an entry whose contribution starts with a user or
/// assistant message, never a tool result, and never a user entry that a
/// result of the preceding assistant's calls still follows.
#[must_use]
pub fn select_cut(view: &ContextView, keep_recent_tokens: f64) -> Option<usize> {
    let contributions = &view.contributions;
    let start = usize::from(view.head.is_some());
    let candidates: Vec<usize> = (start..contributions.len())
        .filter(|&index| is_candidate(contributions, index))
        .collect();
    let mut kept: u64 = 0;
    let mut cut = None;
    for index in (start..contributions.len()).rev() {
        for message in &contributions[index] {
            kept += estimate_message_tokens(message);
        }
        if js_number(kept) < keep_recent_tokens {
            continue;
        }
        cut = candidates
            .iter()
            .copied()
            .find(|&candidate| candidate >= index)
            .or_else(|| candidates.last().copied());
        break;
    }
    let cut = cut?;
    (start..cut)
        .any(|index| !contributions[index].is_empty())
        .then_some(cut)
}

/// A token count as the JS number TS compares it as.
#[expect(
    clippy::cast_precision_loss,
    reason = "token sums are far below 2^53, where the conversion is exact"
)]
pub(super) fn js_number(tokens: u64) -> f64 {
    tokens as f64
}

fn is_candidate(contributions: &[Vec<Message>], index: usize) -> bool {
    match contributions[index].first() {
        Some(Message::Assistant(_)) => return true,
        Some(Message::User(_)) => {}
        Some(Message::System(_) | Message::ToolResult(_)) | None => return false,
    }
    // A result of the preceding assistant's calls that follows this entry,
    // before the next assistant, belongs before it.
    let mut calls: HashSet<&str> = HashSet::new();
    for before in (0..index).rev() {
        let Some(assistant) =
            contributions[before]
                .iter()
                .rev()
                .find_map(|message| match message {
                    Message::Assistant(assistant) => Some(assistant),
                    Message::System(_) | Message::User(_) | Message::ToolResult(_) => None,
                })
        else {
            continue;
        };
        calls = assistant
            .content
            .iter()
            .filter_map(|content| match content {
                AssistantContentBlock::ToolCall(call) => Some(call.id.as_str()),
                AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
            })
            .collect();
        break;
    }
    if calls.is_empty() {
        return true;
    }
    for (after, contribution) in contributions.iter().enumerate().skip(index) {
        for (position, message) in contribution.iter().enumerate() {
            match message {
                Message::Assistant(_) if after > index || position > 0 => return true,
                Message::ToolResult(result) if calls.contains(result.tool_call_id.as_str()) => {
                    return false;
                }
                Message::Assistant(_)
                | Message::ToolResult(_)
                | Message::System(_)
                | Message::User(_) => {}
            }
        }
    }
    true
}

/// Model messages of the entries before `cut`: the head marker first,
/// ordered like model context (spec §2.1).
#[must_use]
pub fn summarized_messages(view: &ContextView, cut: usize) -> Vec<Message> {
    let flat: Vec<Message> = view.contributions[..cut]
        .iter()
        .flatten()
        .cloned()
        .collect();
    order_tool_results(&flat)
}

/// Size of a request over `view` followed by `extra` (spec §8.3): the usage
/// of the newest assistant appended after the head marker, whose request
/// included the marker, plus estimates of the messages after it; without
/// one, estimates of every message.
///
/// TS locates the measured message in `view.messages` by object identity
/// (`lastIndexOf`); the Rust view holds copies, so the last equal message is
/// taken, which is the same message: an assistant carries its own usage and
/// timestamp.
#[must_use]
pub fn estimate_context(view: &ContextView, extra: &[Message]) -> u64 {
    let mut measured: Option<&AssistantMessage> = None;
    let after = view.head.as_ref().map(|head| head.id);
    for (entry, contribution) in view.entries.iter().zip(&view.contributions).rev() {
        if after.is_some_and(|after| entry.id <= after) {
            continue;
        }
        measured = contribution.iter().rev().find_map(|message| match message {
            Message::Assistant(assistant) if calculate_context_tokens(&assistant.usage) > 0 => {
                Some(assistant)
            }
            Message::Assistant(_)
            | Message::System(_)
            | Message::User(_)
            | Message::ToolResult(_) => None,
        });
        if measured.is_some() {
            break;
        }
    }
    let from = measured.map_or(0, |measured| {
        view.messages
            .iter()
            .rposition(
                |message| matches!(message, Message::Assistant(assistant) if assistant == measured),
            )
            .map_or(0, |index| index + 1)
    });
    let mut tokens = measured.map_or(0, |measured| calculate_context_tokens(&measured.usage));
    for message in &view.messages[from..] {
        tokens += estimate_message_tokens(message);
    }
    for message in extra {
        tokens += estimate_message_tokens(message);
    }
    tokens
}
