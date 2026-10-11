//! The summarization request: the history and turn-prefix summarizer
//! request bodies (TS core/compaction/compaction.ts prompts), their chars/4
//! size estimates, and the completion budgets of the two summary calls.

use eukhe_types::ai::{TextContent, UserContent, UserContentBlock, UserMessage};
use eukhe_types::session::AgentMessage;
use std::fmt::Write as _;

use super::utils::{serialize_conversation, SUMMARIZATION_SYSTEM_PROMPT};
use crate::durable::messages::convert_to_llm;

/// Default compaction reserve (TS `DEFAULT_COMPACTION_SETTINGS`).
pub const DEFAULT_RESERVE_TOKENS: u64 = 16_384;

/// Chars/4 heuristic token estimate (conservative; overestimates).
#[must_use]
pub fn estimate_tokens(message: &AgentMessage) -> u64 {
    let chars = |text: &str| text.chars().count() as u64;
    match message {
        AgentMessage::User(user) => match &user.content {
            eukhe_types::ai::UserContent::Text(text) => div4(chars(text)),
            eukhe_types::ai::UserContent::Blocks(blocks) => div4(
                blocks
                    .iter()
                    .filter_map(|block| match block {
                        eukhe_types::ai::UserContentBlock::Text(text) => Some(chars(&text.text)),
                        _ => None,
                    })
                    .sum(),
            ),
        },
        AgentMessage::Assistant(assistant) => {
            let mut total = 0u64;
            for block in &assistant.content {
                match block {
                    eukhe_types::ai::AssistantContentBlock::Text(text) => {
                        total += chars(&text.text);
                    }
                    eukhe_types::ai::AssistantContentBlock::Thinking(thinking) => {
                        total += chars(&thinking.thinking);
                    }
                    eukhe_types::ai::AssistantContentBlock::ToolCall(call) => {
                        total += chars(&call.name)
                            + serde_json::to_string(&call.arguments)
                                .map_or(0, |json| json.chars().count() as u64);
                    }
                }
            }
            div4(total)
        }
        AgentMessage::Custom(custom) => match &custom.content {
            eukhe_types::ai::UserContent::Text(text) => div4(chars(text)),
            eukhe_types::ai::UserContent::Blocks(blocks) => div4(
                blocks
                    .iter()
                    .map(|block| match block {
                        eukhe_types::ai::UserContentBlock::Text(text) => chars(&text.text),
                        eukhe_types::ai::UserContentBlock::Image(_) => 4_800, // ~1200 tokens
                        // Un-modeled blocks have no modeled size; TS sizes
                        // only typed blocks, so estimate zero.
                        eukhe_types::ai::UserContentBlock::Raw(_) => 0,
                    })
                    .sum(),
            ),
        },
        AgentMessage::ToolResult(result) => div4(
            result
                .content
                .iter()
                .map(|block| match block {
                    eukhe_types::ai::UserContentBlock::Text(text) => chars(&text.text),
                    eukhe_types::ai::UserContentBlock::Image(_) => 4_800,
                    eukhe_types::ai::UserContentBlock::Raw(_) => 0,
                })
                .sum(),
        ),
        AgentMessage::BashExecution(bash) => div4(chars(&bash.command) + chars(&bash.output)),
        AgentMessage::BranchSummary(summary) => div4(chars(&summary.summary)),
        AgentMessage::CompactionSummary(summary) => div4(chars(&summary.summary)),
    }
    .saturating_add(0) // keep type u64
}

fn div4(chars: u64) -> u64 {
    chars.div_ceil(4)
}

const SUMMARIZATION_PROMPT: &str = "The messages above are a conversation to summarize. Create a structured context checkpoint summary that another LLM will use to continue the work.\n\nUse this EXACT format:\n\n## Goal\n[What is the user trying to accomplish? Can be multiple items if the session covers different tasks.]\n\n## Constraints & Preferences\n- [Any constraints, preferences, or requirements mentioned by user]\n- [Or \"(none)\" if none were mentioned]\n\n## Progress\n### Done\n- [x] [Completed tasks/changes]\n\n### In Progress\n- [ ] [Current work]\n\n### Blocked\n- [Issues preventing progress, if any]\n\n## Key Decisions\n- **[Decision]**: [Brief rationale]\n\n## Next Steps\n1. [Ordered list of what should happen next]\n\n## Critical Context\n- [Any data, examples, or references needed to continue]\n- [Or \"(none)\" if not applicable]\n\nKeep each section concise. Preserve exact file paths, function names, and error messages.";

const KERNEL_PERSIST_SUMMARY_NOTE: &str = "Note: the Python kernel keeps running after this summary — every Python variable, import, and helper you defined stays available. The cells that defined them won't appear above, so record in the summary any names worth remembering so you reuse them instead of redefining them.";

/// The turn-prefix summarizer instruction (TS `TURN_PREFIX_SUMMARIZATION_PROMPT`):
/// a split turn keeps its suffix, and this prompt summarizes the cut turn's
/// prefix for the retained recent work.
pub const TURN_PREFIX_SUMMARIZATION_PROMPT: &str = "This is the PREFIX of a turn that was too large to keep. The SUFFIX (recent work) is retained.\n\nSummarize the prefix to provide context for the retained suffix:\n\n## Original Request\n[What did the user ask for in this turn?]\n\n## Early Progress\n- [Key decisions and work done in the prefix]\n\n## Context for Suffix\n- [Information needed to understand the retained recent work]\n\nBe concise. Focus on what's needed to understand the kept suffix.";

const UPDATE_SUMMARIZATION_PROMPT: &str = "The messages above are NEW conversation messages to incorporate into the existing summary provided in <previous-summary> tags.\n\nUpdate the existing structured summary with new information. RULES:\n- PRESERVE all existing information from the previous summary\n- ADD new progress, decisions, and context from the new messages\n- UPDATE the Progress section: move items from \"In Progress\" to \"Done\" when completed\n- UPDATE \"Next Steps\" based on what was accomplished\n- PRESERVE exact file paths, function names, and error messages\n- If something is no longer relevant, you may remove it\n\nUse this EXACT format:\n\n## Goal\n[Preserve existing goals, add new ones if the task expanded]\n\n## Constraints & Preferences\n- [Preserve existing, add new ones discovered]\n\n## Progress\n### Done\n- [x] [Include previously done items AND newly completed items]\n\n### In Progress\n- [ ] [Current work - update based on progress]\n\n### Blocked\n- [Current blockers - remove if resolved]\n\n## Key Decisions\n- **[Decision]**: [Brief rationale] (preserve all previous, add new)\n\n## Next Steps\n1. [Update based on current state]\n\n## Critical Context\n- [Preserve important context, add new if needed]\n\nKeep each section concise. Preserve exact file paths, function names, and error messages.";

/// The instruction part of the summarization prompt (initial or update
/// template, user instructions, kernel persistence note).
#[must_use]
pub fn build_summarization_prompt(
    custom_instructions: Option<&str>,
    previous_summary: Option<&str>,
) -> String {
    let mut base = if previous_summary.is_some() {
        UPDATE_SUMMARIZATION_PROMPT
    } else {
        SUMMARIZATION_PROMPT
    }
    .to_string();
    if let Some(custom_instructions) = custom_instructions {
        let _ = write!(base,
            "\n\n<user-instructions>\nThe user provided these instructions for this summary. Follow them with high priority while keeping the section format above: emphasize what they ask to focus on, and preserve verbatim anything they ask to remember.\n{custom_instructions}\n</user-instructions>"
        );
    }
    format!("{base}\n\n{KERNEL_PERSIST_SUMMARY_NOTE}")
}

/// Assemble the summarization messages for the conversation slice.
/// `recent_state_anchor` (TS #2385) is the newest retained assistant text:
/// it rides the request as a `<recent-state-anchor>` block after the
/// previous summary, marking the retained tail — not the summarized
/// conversation above — as the current state, so the update summary cannot
/// lag behind the kept tail. The turn-prefix request never carries one
/// (its slice is summarized away).
#[must_use]
pub fn build_summarization_request(
    messages: &[AgentMessage],
    custom_instructions: Option<&str>,
    previous_summary: Option<&str>,
    recent_state_anchor: Option<&str>,
    #[allow(unused_variables)] reserve_tokens: u64,
) -> Vec<AgentMessage> {
    let llm_messages = convert_to_llm(messages);
    let conversation_text = serialize_conversation(&llm_messages);
    let mut prompt_text = format!("<conversation>\n{conversation_text}\n</conversation>\n\n");
    if let Some(previous_summary) = previous_summary {
        let _ = write!(
            prompt_text,
            "<previous-summary>\n{previous_summary}\n</previous-summary>\n\n"
        );
    }
    if let Some(recent_state_anchor) = recent_state_anchor {
        let _ = write!(
            prompt_text,
            "<recent-state-anchor>\nNewest assistant message that stays retained below the summary. The conversation to summarize is older than this anchor; the retained messages below are authoritative, so treat this anchor, not the conversation above, as the current state.\n\n{recent_state_anchor}\n</recent-state-anchor>\n\n"
        );
    }
    prompt_text.push_str(&build_summarization_prompt(
        custom_instructions,
        previous_summary,
    ));
    vec![AgentMessage::User(UserMessage {
        content: UserContent::Blocks(vec![UserContentBlock::Text(TextContent {
            text: prompt_text,
            text_signature: None,
            rest: serde_json::Map::default(),
            cache_breakpoint: None,
        })]),
        timestamp: 0,
        rest: serde_json::Map::default(),
    })]
}

/// The turn-prefix summarization request (TS `generateTurnPrefixSummary`):
/// the serialized prefix conversation under the turn-prefix instruction —
/// no custom instructions, no previous summary, no kernel note.
#[must_use]
pub fn build_turn_prefix_request(messages: &[AgentMessage]) -> Vec<AgentMessage> {
    let llm_messages = convert_to_llm(messages);
    let conversation_text = serialize_conversation(&llm_messages);
    let prompt_text = format!(
        "<conversation>\n{conversation_text}\n</conversation>\n\n{TURN_PREFIX_SUMMARIZATION_PROMPT}"
    );
    vec![AgentMessage::User(UserMessage {
        content: UserContent::Blocks(vec![UserContentBlock::Text(TextContent {
            text: prompt_text,
            text_signature: None,
            rest: serde_json::Map::default(),
            cache_breakpoint: None,
        })]),
        timestamp: 0,
        rest: serde_json::Map::default(),
    })]
}

/// The history summary's completion budget (TS `generateSummary`:
/// `Math.floor(0.8 * reserveTokens)`): multiply before dividing so
/// sub-5 budgets round toward the true floor instead of collapsing to
/// zero (`/ 5 * 4` truncates first and yields 0 for reserves 1–4, and
/// 4 for 9 where the TS floor is 7).
pub(crate) fn history_summary_completion_budget(reserve_tokens: u64) -> u64 {
    reserve_tokens.saturating_mul(4) / 5
}

/// The split-turn prefix summary's completion budget (TS
/// `generateTurnPrefixSummary`: `Math.floor(0.5 * reserveTokens)`).
pub(crate) fn turn_prefix_summary_completion_budget(reserve_tokens: u64) -> u64 {
    reserve_tokens / 2
}

/// The chars the summarizer request text occupies at the compaction
/// module's chars/4 heuristic (TS #2411's estimator math).
pub(crate) fn summarizer_request_tokens(request: &[AgentMessage]) -> u64 {
    let chars: usize = request
        .iter()
        .map(|message| match message {
            AgentMessage::User(user) => user.content.text().chars().count(),
            _ => 0,
        })
        .sum();
    (chars as u64).div_ceil(4)
}

/// Estimate the context window the compaction's summary calls need (TS
/// #2411's `estimateSummaryRequestTokens`): the exact request bodies
/// through the same builders as the wire calls
/// ([`build_summarization_request`], [`build_turn_prefix_request`]), the
/// chars/4 heuristic, the shared system prompt, and each call's
/// completion budget — the largest slice wins, because routing must fit
/// every request the compaction will issue. `history` and `turn_prefix`
/// are the messages the run will summarize (the compaction run's slices).
/// `recent_state_anchor` mirrors the anchor block the history wire request
/// always carries when the kept tail has assistant text (TS follow-up
/// 771611b14): an estimate without it would accept an auxiliary model
/// whose window fits the underestimate while the real request goes
/// over-limit.
pub fn estimate_summary_request_tokens(
    history: &[AgentMessage],
    turn_prefix: &[AgentMessage],
    is_split_turn: bool,
    previous_summary: Option<&str>,
    recent_state_anchor: Option<&str>,
    custom_instructions: Option<&str>,
    reserve_tokens: u64,
) -> u64 {
    let system_prompt_tokens = (SUMMARIZATION_SYSTEM_PROMPT.chars().count() as u64).div_ceil(4);
    let mut required = 0u64;
    // The history slice runs for every compaction except a split turn
    // whose kept cut leaves no history ("No prior history." is a literal
    // stand-in, no wire call).
    let issues_history_call = !history.is_empty() || !is_split_turn || turn_prefix.is_empty();
    if issues_history_call {
        let request = build_summarization_request(
            history,
            custom_instructions,
            previous_summary,
            recent_state_anchor,
            reserve_tokens,
        );
        required = required.max(
            system_prompt_tokens
                + summarizer_request_tokens(&request)
                + history_summary_completion_budget(reserve_tokens),
        );
    }
    // A split turn's prefix summary is a separate request with its own
    // body and a smaller completion budget, so it can exceed the history
    // slice.
    if !turn_prefix.is_empty() {
        let request = build_turn_prefix_request(turn_prefix);
        required = required.max(
            system_prompt_tokens
                + summarizer_request_tokens(&request)
                + turn_prefix_summary_completion_budget(reserve_tokens),
        );
    }
    required
}

#[cfg(test)]
mod tests {
    use super::*;

    fn user(text: &str) -> AgentMessage {
        AgentMessage::User(UserMessage {
            content: UserContent::Text(text.to_string()),
            timestamp: 0,
            rest: serde_json::Map::default(),
        })
    }

    #[test]
    fn token_estimation() {
        let user = AgentMessage::User(eukhe_types::ai::UserMessage {
            content: eukhe_types::ai::UserContent::Text("12345678".to_string()), // 8 chars -> 2 tokens
            timestamp: 0,
            rest: serde_json::Map::default(),
        });
        assert_eq!(estimate_tokens(&user), 2);
    }

    #[test]
    fn summarization_prompt_shapes() {
        let initial = build_summarization_prompt(None, None);
        assert!(initial.contains("Create a structured context checkpoint summary"));
        assert!(initial.contains("the Python kernel keeps running"));
        let update = build_summarization_prompt(None, Some("old summary"));
        assert!(update.contains("NEW conversation messages to incorporate"));
        let custom = build_summarization_prompt(Some("focus on tests"), None);
        assert!(custom.contains("<user-instructions>\nThe user provided these instructions"));
        assert!(custom.contains("focus on tests"));
    }

    /// The history request carries the recency anchor after the previous
    /// summary (TS #2385), marking the retained tail — not the summarized
    /// conversation above — as the current state; a missing anchor adds no
    /// block, and the turn-prefix request has no anchor parameter at all.
    #[test]
    fn summarization_request_carries_the_recent_state_anchor() {
        let request = build_summarization_request(
            std::slice::from_ref(&user("the conversation")),
            None,
            Some("the previous summary"),
            Some("the newest kept-tail text"),
            1_000,
        );
        let AgentMessage::User(prompt) = &request[0] else {
            panic!("the summarization request is a single user message");
        };
        let text = prompt.content.text();
        let previous_end = text.find("</previous-summary>").expect("previous summary");
        let anchor_start = text.find("<recent-state-anchor>").expect("anchor block");
        let anchor_end = text.find("</recent-state-anchor>").expect("anchor close");
        assert!(previous_end < anchor_start && anchor_start < anchor_end);
        assert!(text.contains(
            "<recent-state-anchor>\nNewest assistant message that stays retained below the summary. The conversation to summarize is older than this anchor; the retained messages below are authoritative, so treat this anchor, not the conversation above, as the current state.\n\nthe newest kept-tail text\n</recent-state-anchor>\n\n"
        ));
        // Without an anchor the request carries no anchor block.
        let request = build_summarization_request(
            std::slice::from_ref(&user("the conversation")),
            None,
            Some("the previous summary"),
            None,
            1_000,
        );
        let AgentMessage::User(prompt) = &request[0] else {
            panic!("the summarization request is a single user message");
        };
        assert!(!prompt.content.text().contains("<recent-state-anchor>"));
    }

    /// The turn-prefix request (TS `generateTurnPrefixSummary`): the
    /// serialized prefix under the turn-prefix instruction — never the
    /// checkpoint prompt, a previous summary, or the kernel note.
    #[test]
    fn turn_prefix_request_shape() {
        let messages = vec![user("big turn"), user("more of the turn")];
        let request = build_turn_prefix_request(&messages);
        let AgentMessage::User(user) = &request[0] else {
            panic!("expected user request");
        };
        let text = user.content.text();
        assert!(text.starts_with(
            "<conversation>\n[User]: big turn\n\n[User]: more of the turn\n</conversation>\n\n"
        ));
        assert!(text.contains("This is the PREFIX of a turn that was too large to keep."));
        assert!(text.ends_with("Be concise. Focus on what's needed to understand the kept suffix."));
        assert!(!text.contains("Create a structured context checkpoint summary"));
        assert!(!text.contains("<previous-summary>"));
        assert!(!text.contains("the Python kernel keeps running"));
    }

    #[test]
    fn summarization_request_shape() {
        let messages = vec![user("hello"), user("world")];
        let request = build_summarization_request(
            &messages,
            Some("be brief"),
            None,
            /*recent_state_anchor*/ None,
            1_000,
        );
        match &request[0] {
            AgentMessage::User(user) => {
                let text = user.content.text();
                assert!(text.starts_with(
                    "<conversation>\n[User]: hello\n\n[User]: world\n</conversation>"
                ));
                assert!(text.contains("<user-instructions>\nThe user provided these instructions"));
                assert!(text.ends_with("redefining them."));
            }
            _ => panic!("expected user message"),
        }
    }

    /// The window estimate covers the exact wire bodies the compaction
    /// will issue (TS #2411's `estimateSummaryRequestTokens`): a split
    /// turn estimates BOTH the history request and the turn-prefix
    /// request (each with the shared system prompt and its own
    /// completion budget), and the no-history split arm estimates only the
    /// prefix call.
    #[test]
    fn summary_window_estimate_covers_both_split_requests() {
        let history = vec![user("some history to summarize")];
        let turn_prefix = vec![user(&"a very long turn prefix ".repeat(2_000))];
        let full =
            estimate_summary_request_tokens(&history, &turn_prefix, true, None, None, None, 10_000);
        let history_only =
            estimate_summary_request_tokens(&history, &[], false, None, None, None, 10_000);
        let prefix_only =
            estimate_summary_request_tokens(&[], &turn_prefix, true, None, None, None, 10_000);
        // A split turn must fit every request it will issue: the estimate
        // is the larger of the two arms' estimates (each with the shared
        // system prompt and its own completion budget).
        assert_eq!(full, history_only.max(prefix_only));
        assert!(full > history_only);
        // The previous summary, the recency anchor, and the custom
        // instructions grow the history request, so they grow the
        // estimate.
        let with_anchors = estimate_summary_request_tokens(
            &history,
            &[],
            false,
            Some("the previous summary text"),
            Some("the newest kept-tail assistant text"),
            Some("focus on the goal"),
            10_000,
        );
        assert!(with_anchors > history_only);
        // The recency anchor alone grows the estimate (TS follow-up
        // 771611b14: the estimator mirrors the anchor block the wire
        // request carries).
        let with_anchor = estimate_summary_request_tokens(
            &history,
            &[],
            false,
            None,
            Some("the newest kept-tail assistant text"),
            None,
            10_000,
        );
        assert!(with_anchor > history_only);
        // The completion budgets draw on the reserve: a larger reserve
        // grows the estimate.
        let bigger_reserve =
            estimate_summary_request_tokens(&history, &[], false, None, None, None, 100_000);
        assert!(bigger_reserve > history_only);
    }
}
