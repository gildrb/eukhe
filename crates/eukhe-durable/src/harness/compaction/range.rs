//! Range selection and context size (spec §8.3, §8.7): pure functions of a
//! [`ContextView`] shared by the compaction task and generation's threshold
//! and overflow checks. The compiled core decides where a compaction cuts
//! and which threshold a context compacts at
//! (`eukhe_bend::rules::infer_threshold`, laws `infer_threshold_plan_exact`,
//! `infer_threshold_cut_within_target`, `infer_threshold_target_under`);
//! this module counts the tokens and finds the places a cut may keep from.

use std::collections::HashSet;

use eukhe_ai::utils::context_tokens::{calculate_context_tokens, message_tokens};
use eukhe_bend::rules::infer_threshold::{whole, Compaction, Over, Range};
use eukhe_tokens::Tokenizer;
use eukhe_types::pi_ai::{AssistantContentBlock, AssistantMessage, Message};

use crate::harness::context::order_tool_results;
use crate::harness::types::{CompactionPolicy, ContextView};

/// What a compaction of a view does: the threshold its request compacts at
/// and the index in `view.entries` of the first entry a summary keeps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Plan {
    /// Blocking for a request past the window, else the threshold the
    /// context of the last turn is over; kept only when a cut exists, and
    /// the background one only when the cut brings the request down to
    /// the target (half the size at which compaction starts).
    pub(crate) over: Over,
    /// The first kept entry; `None` when there is nothing to compact.
    pub(crate) cut: Option<usize>,
}

/// Index in `view.entries` of the first entry a summary keeps, or `None`
/// when there is nothing to compact (spec §8.7): the cut of [`plan`] for
/// the view's own context size ([`context_tokens`]) under the reading
/// model's `tokenizer`.
#[must_use]
pub fn select_cut(
    view: &ContextView,
    policy: &CompactionPolicy,
    context_window: u64,
    tokenizer: &Tokenizer,
) -> Option<usize> {
    let tokens = context_tokens(view, &[], tokenizer);
    // The cut reads no threshold, so no turn's count.
    plan(view, policy, context_window, tokens, 0, tokenizer).cut
}

/// The plan for a request over `view` of `tokens` tokens after a turn that
/// reached `last` tokens ([`last_turn_tokens`]; 0: no turn to read) (spec
/// §8.3, §8.7). A compaction runs once the context actually crossed a
/// threshold: the thresholds read `last`; the request itself only has to
/// stay within the window (laws `infer_threshold_turn_under`,
/// `infer_threshold_past_window_blocks`).
/// The compiled core keeps the most of the newest entries whose tokens stay
/// within `keepRecentTokens` and, with a known window, leave the context at
/// most at the target; when no cut does, the newest cut. A cut starts at an
/// entry whose contribution starts with a user or assistant message, never
/// a tool result, and never a user entry that a result of the preceding
/// assistant's calls still follows; it leaves at least one entry with a
/// message before it. Entries count their messages' tokens under
/// `tokenizer`, their system messages none: a compaction writes the system
/// prompt again.
#[expect(
    clippy::cast_precision_loss,
    reason = "a percentage margin is a share of the window in f64 tokens"
)]
pub(crate) fn plan(
    view: &ContextView,
    policy: &CompactionPolicy,
    context_window: u64,
    tokens: u64,
    last: u64,
    tokenizer: &Tokenizer,
) -> Plan {
    let contributions = &view.contributions;
    let start = usize::from(view.head.is_some());
    let len = contributions.len();
    // Newest first: position k keeps the k newest entries.
    let sizes: Vec<u64> = contributions[start..]
        .iter()
        .rev()
        .map(|contribution| {
            contribution
                .iter()
                .filter(|message| !matches!(message, Message::System(_)))
                .map(|message| message_tokens(tokenizer, message))
                .sum()
        })
        .collect();
    let cuts: Vec<u64> = (start..len)
        .filter(|&index| is_candidate(contributions, index))
        .map(|index| (len - index) as u64)
        .collect();
    let full = (start..len)
        .find(|&index| !contributions[index].is_empty())
        .map_or(0, |index| (len - index) as u64);
    let compaction = Compaction {
        enabled: policy.enabled,
        window: context_window,
        reserve: whole(policy.reserve_tokens),
        margin: whole(policy.background.tokens(context_window as f64)),
        keep: u64::try_from(whole(policy.keep_recent_tokens)).unwrap_or(0),
    };
    let decided = compaction.plan(&Range {
        tokens,
        last,
        sizes: &sizes,
        cuts: &cuts,
        full,
    });
    Plan {
        over: decided.over,
        // The core keeps k of the newest entries, a cut it was given
        // (law `infer_threshold_plan_exact`): 1 <= k <= len - start.
        cut: decided
            .cut
            .and_then(|kept| usize::try_from(kept).ok())
            .and_then(|kept| len.checked_sub(kept)),
    }
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
/// included the marker, plus the counted tokens of the messages after it
/// under the reading model's `tokenizer`; without one, the counted tokens
/// of every message.
///
/// TS locates the measured message in `view.messages` by object identity
/// (`lastIndexOf`); the Rust view holds copies, so the last equal message is
/// taken, which is the same message: an assistant carries its own usage and
/// timestamp.
#[must_use]
pub fn context_tokens(view: &ContextView, extra: &[Message], tokenizer: &Tokenizer) -> u64 {
    let measured = last_turn(view);
    let from = measured.map_or(0, |measured| {
        view.messages
            .iter()
            .rposition(
                |message| matches!(message, Message::Assistant(assistant) if assistant == measured),
            )
            .map_or(0, |index| index + 1)
    });
    let counted = measured.map_or(0, |measured| calculate_context_tokens(&measured.usage));
    let trailing: u64 = view.messages[from..]
        .iter()
        .chain(extra)
        .map(|message| message_tokens(tokenizer, message))
        .sum();
    counted + trailing
}

/// The tokens the provider counted for the newest answer appended after the
/// head marker (its request and answer): the context the last turn
/// reached; 0 when no answer since the head was counted.
pub(crate) fn last_turn_tokens(view: &ContextView) -> u64 {
    last_turn(view).map_or(0, |turn| calculate_context_tokens(&turn.usage))
}

/// The newest assistant appended after the head marker that the provider
/// counted: its request included the marker.
fn last_turn(view: &ContextView) -> Option<&AssistantMessage> {
    let after = view.head.as_ref().map(|head| head.id);
    view.entries
        .iter()
        .zip(&view.contributions)
        .rev()
        .filter(|(entry, _)| after.is_none_or(|after| entry.id > after))
        .find_map(|(_, contribution)| {
            contribution.iter().rev().find_map(|message| match message {
                Message::Assistant(assistant) if calculate_context_tokens(&assistant.usage) > 0 => {
                    Some(assistant)
                }
                Message::Assistant(_)
                | Message::System(_)
                | Message::User(_)
                | Message::ToolResult(_) => None,
            })
        })
}
