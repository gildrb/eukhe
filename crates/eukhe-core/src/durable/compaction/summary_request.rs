//! The summarization request: the history and turn-prefix summarizer
//! request bodies (TS core/compaction/compaction.ts prompts), their sizes
//! counted with the summarizer model's tokenizer, and the completion
//! budgets of the two summary calls.

use eukhe_tokens::Tokenizer;
use eukhe_types::ai::{TextContent, UserContent, UserContentBlock, UserMessage};
use eukhe_types::session::AgentMessage;
use std::fmt::Write as _;

use super::utils::{serialize_conversation, SUMMARIZATION_SYSTEM_PROMPT};
use crate::durable::messages::convert_to_llm;

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
    build_summarization_request_for_text(
        &conversation_text,
        custom_instructions,
        previous_summary,
        recent_state_anchor,
    )
}

/// [`build_summarization_request`] over an already serialized
/// conversation (one summary window).
#[must_use]
pub(crate) fn build_summarization_request_for_text(
    conversation_text: &str,
    custom_instructions: Option<&str>,
    previous_summary: Option<&str>,
    recent_state_anchor: Option<&str>,
) -> Vec<AgentMessage> {
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

/// The summarizer window of a model whose catalog entry carries no usable
/// context window.
const DEFAULT_SUMMARY_INPUT_WINDOW: u64 = 200_000;

/// The floor of one summarization window, so a tiny model still makes
/// progress.
const MIN_SUMMARY_INPUT_TOKENS: u64 = 16_384;

/// The most a summary may emit (the default summary reserve).
const MAX_SUMMARY_TOKENS: u64 = 16_384;

fn summary_input_window(context_window: u64) -> u64 {
    if context_window > 0 {
        context_window
    } else {
        DEFAULT_SUMMARY_INPUT_WINDOW
    }
}

/// The smallest summarization window worth planning for a model of
/// `context_window` tokens; below it, overflow recovery gives up.
pub(crate) fn min_summary_input_tokens(context_window: u64) -> u64 {
    MIN_SUMMARY_INPUT_TOKENS.min((summary_input_window(context_window) / 8).max(1_024))
}

/// The conversation input of ONE summarization call: the summarizer's
/// window, discounted to 0.8 because the provider's tokenizer disagrees
/// with the local count by a few percent, minus the summary it emits
/// (`max_tokens`) and the previous summary and prompt it carries.
pub(crate) fn summary_input_budget_tokens(context_window: u64, max_tokens: u64) -> u64 {
    let window = summary_input_window(context_window);
    (window.saturating_mul(4) / 5)
        .saturating_sub(max_tokens)
        .saturating_sub(MAX_SUMMARY_TOKENS)
        .max(min_summary_input_tokens(context_window))
}

/// Clamp one serialized window of `tokens` counted tokens to
/// `budget_tokens`: only a single message
/// above the budget (an oversized paste) gets here, and the alternative is
/// a summarizer rejection no retry can clear, which strands the session
/// with a full window. Lengths count UTF-16 code units like the TS slice;
/// the cut never splits a character.
pub(crate) fn clamp_conversation_to_budget(
    mut text: String,
    budget_tokens: u64,
    tokens: u64,
) -> String {
    if tokens <= budget_tokens {
        return text;
    }
    let length = text.encode_utf16().count() as u64;
    let keep = u64::try_from(
        u128::from(length) * u128::from(budget_tokens) * 95 / (u128::from(tokens) * 100),
    )
    .unwrap_or(u64::MAX)
    .max(1_024);
    if keep >= length {
        return text;
    }
    let mut units = 0u64;
    let cut = text
        .char_indices()
        .find(|(_, character)| {
            units += character.len_utf16() as u64;
            units > keep
        })
        .map_or(text.len(), |(index, _)| index);
    text.truncate(cut);
    let _ = write!(
        text,
        "\n\n[... {} more characters truncated]",
        length - keep
    );
    text
}

/// Partition `messages` (already converted for the model) into windows
/// whose serializations each fit `budget_tokens` under the summarizer
/// model's `tokenizer`, splitting on message boundaries; a single message
/// above the budget is a window of its own.
pub(crate) fn plan_summary_windows(
    messages: Vec<AgentMessage>,
    tokenizer: &Tokenizer,
    budget_tokens: u64,
) -> Vec<Vec<AgentMessage>> {
    let mut windows = Vec::new();
    let mut current: Vec<AgentMessage> = Vec::new();
    let mut current_tokens = 0u64;
    for message in messages {
        let tokens = tokenizer.count_text(&serialize_conversation(std::slice::from_ref(&message)));
        if current_tokens > 0 && current_tokens + tokens > budget_tokens {
            windows.push(std::mem::take(&mut current));
            current_tokens = 0;
        }
        current.push(message);
        current_tokens += tokens;
    }
    if !current.is_empty() {
        windows.push(current);
    }
    windows
}

/// The tokens the summarizer request text occupies under the summarizer
/// model's `tokenizer`: the request is user text only.
pub(crate) fn summarizer_request_tokens(tokenizer: &Tokenizer, request: &[AgentMessage]) -> u64 {
    request
        .iter()
        .map(|message| match message {
            AgentMessage::User(user) => tokenizer.count_text(&user.content.text()),
            AgentMessage::Assistant(_)
            | AgentMessage::Custom(_)
            | AgentMessage::ToolResult(_)
            | AgentMessage::BashExecution(_)
            | AgentMessage::BranchSummary(_)
            | AgentMessage::CompactionSummary(_) => 0,
        })
        .sum()
}

/// The context window the compaction's summary calls need (TS #2411's
/// `estimateSummaryRequestTokens`), counted with the summarizer model's
/// `tokenizer`: the exact request bodies through the same builders as the
/// wire calls ([`build_summarization_request`],
/// [`build_turn_prefix_request`]), the shared system prompt, and each
/// call's completion budget — the largest slice wins, because routing must
/// fit every request the compaction will issue. `history` and
/// `turn_prefix` are the messages the run will summarize (the compaction
/// run's slices). `recent_state_anchor` mirrors the anchor block the
/// history wire request always carries when the kept tail has assistant
/// text (TS follow-up 771611b14): a count without it would accept an
/// auxiliary model whose window fits the smaller size while the real
/// request goes over-limit.
#[expect(
    clippy::too_many_arguments,
    reason = "the summary request's inputs, as the wire builders take them, and the counting model"
)]
pub fn summary_request_tokens(
    tokenizer: &Tokenizer,
    history: &[AgentMessage],
    turn_prefix: &[AgentMessage],
    is_split_turn: bool,
    previous_summary: Option<&str>,
    recent_state_anchor: Option<&str>,
    custom_instructions: Option<&str>,
    reserve_tokens: u64,
) -> u64 {
    let system_prompt_tokens = tokenizer.count_text(SUMMARIZATION_SYSTEM_PROMPT);
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
                + summarizer_request_tokens(tokenizer, &request)
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
                + summarizer_request_tokens(tokenizer, &request)
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

    /// A window above its budget keeps the share of its characters the
    /// budget allows (95% of the
    /// proportional length, at least 1024), never splitting a character,
    /// and says how many it dropped; one within its budget is unchanged.
    #[test]
    fn an_oversized_window_is_clamped_to_its_budget() {
        let text = "字".repeat(10_000);
        assert_eq!(
            clamp_conversation_to_budget(text.clone(), 10_000, 10_000),
            text
        );
        assert_eq!(
            clamp_conversation_to_budget(text.clone(), 5_000, 10_000),
            format!(
                "{}\n\n[... 5250 more characters truncated]",
                "字".repeat(4_750)
            )
        );
        assert_eq!(
            clamp_conversation_to_budget(text, 1, 10_000),
            format!(
                "{}\n\n[... 8976 more characters truncated]",
                "字".repeat(1_024)
            )
        );
        let pairs = "😀".repeat(1_000);
        assert_eq!(
            clamp_conversation_to_budget(pairs, 1, 1_000),
            format!(
                "{}\n\n[... 976 more characters truncated]",
                "😀".repeat(512)
            )
        );
    }

    /// Windows split on message boundaries under the budget, counted with
    /// the summarizer's tokenizer; a message above it is a window of its
    /// own. The input budget is 0.8 of the window less the summary's and
    /// the carried summary's reserves, never below the floor.
    #[test]
    fn summary_windows_fit_their_budget() {
        let tokenizer = Tokenizer::unknown_model();
        let serialized_tokens = |message: &AgentMessage| {
            tokenizer.count_text(&serialize_conversation(std::slice::from_ref(message)))
        };
        let small = || user(&" x".repeat(10));
        let large = user(&" y".repeat(1_000));
        // Two small messages fill the budget exactly; the large one alone
        // is past it.
        let budget = 2 * serialized_tokens(&small());
        assert!(serialized_tokens(&large) > budget);
        let windows = plan_summary_windows(
            vec![small(), small(), large.clone(), small()],
            &tokenizer,
            budget,
        );
        assert_eq!(
            windows,
            vec![vec![small(), small()], vec![large], vec![small()]]
        );
        assert_eq!(summary_input_budget_tokens(1_000_000, 13_107), 770_509);
        assert_eq!(summary_input_budget_tokens(0, 13_107), 130_509);
        assert_eq!(summary_input_budget_tokens(32_000, 13_107), 4_000);
        assert_eq!(min_summary_input_tokens(1_000_000), 16_384);
        assert_eq!(min_summary_input_tokens(4_000), 1_024);
    }

    /// Summary routing sizes the request with the summarizer model's
    /// tokenizer: the system prompt, the request body, and the completion
    /// budget.
    #[test]
    fn summary_routing_counts_with_the_summarizer_tokenizer() {
        let tokenizer = Tokenizer::unknown_model();
        let history = vec![user(&"0123456".repeat(100))];
        let request = build_summarization_request(&history, None, None, None, 1_000);
        let AgentMessage::User(prompt) = &request[0] else {
            panic!("the summarization request is a single user message");
        };
        assert_eq!(
            summary_request_tokens(&tokenizer, &history, &[], false, None, None, None, 1_000),
            tokenizer.count_text(SUMMARIZATION_SYSTEM_PROMPT)
                + tokenizer.count_text(&prompt.content.text())
                + 800
        );
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

    /// The window count covers the exact wire bodies the compaction will
    /// issue (TS #2411's `estimateSummaryRequestTokens`): a split turn
    /// counts BOTH the history request and the turn-prefix request (each
    /// with the shared system prompt and its own completion budget), and
    /// the no-history split arm counts only the prefix call.
    #[test]
    fn summary_window_count_covers_both_split_requests() {
        let tokenizer = Tokenizer::unknown_model();
        let count = |history: &[AgentMessage],
                     turn_prefix: &[AgentMessage],
                     is_split_turn: bool,
                     anchors: [Option<&str>; 3],
                     reserve: u64| {
            let [previous, anchor, custom] = anchors;
            summary_request_tokens(
                &tokenizer,
                history,
                turn_prefix,
                is_split_turn,
                previous,
                anchor,
                custom,
                reserve,
            )
        };
        let history = vec![user("some history to summarize")];
        let turn_prefix = vec![user(&"a very long turn prefix ".repeat(2_000))];
        let full = count(&history, &turn_prefix, true, [None; 3], 10_000);
        let history_only = count(&history, &[], false, [None; 3], 10_000);
        let prefix_only = count(&[], &turn_prefix, true, [None; 3], 10_000);
        // A split turn must fit every request it will issue: the count is
        // the larger of the two arms' (each with the shared system prompt
        // and its own completion budget).
        assert_eq!(full, history_only.max(prefix_only));
        assert!(full > history_only);
        // The previous summary, the recency anchor, and the custom
        // instructions grow the history request, so they grow the count.
        let with_anchors = count(
            &history,
            &[],
            false,
            [
                Some("the previous summary text"),
                Some("the newest kept-tail assistant text"),
                Some("focus on the goal"),
            ],
            10_000,
        );
        assert!(with_anchors > history_only);
        // The recency anchor alone grows the count (TS follow-up
        // 771611b14: the count mirrors the anchor block the wire request
        // carries).
        let with_anchor = count(
            &history,
            &[],
            false,
            [None, Some("the newest kept-tail assistant text"), None],
            10_000,
        );
        assert!(with_anchor > history_only);
        // The completion budgets draw on the reserve: a larger reserve
        // grows the count.
        let bigger_reserve = count(&history, &[], false, [None; 3], 100_000);
        assert!(bigger_reserve > history_only);
    }

    /// CJK text is counted, not guessed at 3.5 characters per token: a
    /// history of 200,000 CJK characters, which that guess put at 57,143
    /// tokens, is counted past a 128,000-token window.
    #[test]
    fn a_cjk_history_is_counted_past_the_window_its_estimate_fit() {
        let cjk: String = (0..200_000u32)
            .filter_map(|i| char::from_u32(0x4E00 + (i * 7919 % 0x5200)))
            .collect();
        let required = summary_request_tokens(
            &Tokenizer::unknown_model(),
            &[user(&cjk)],
            &[],
            false,
            None,
            None,
            None,
            1_000,
        );
        assert!(required > 128_000, "{required}");
    }
}
