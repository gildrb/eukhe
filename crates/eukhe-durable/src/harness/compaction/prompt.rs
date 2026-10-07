//! The summarizer's request text (the coding agent's structured checkpoint
//! format) and the classification of its answer (spec §8.7).

use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Message, StopReason, UserContent, UserContentBlock,
};

/// Longest tool result text, in UTF-16 code units, a serialized summary
/// source keeps.
const TOOL_RESULT_MAX_CHARS: usize = 2000;

pub(super) const SUMMARY_PREFIX: &str =
    "The conversation history before this point was compacted into the following summary:\n\n<summary>\n";
pub(super) const SUMMARY_SUFFIX: &str = "\n</summary>";

pub(super) const SUMMARIZATION_SYSTEM_PROMPT: &str = "You are a context summarization assistant. Your task is to read a conversation between a user and an AI assistant, then produce a structured summary following the exact format specified.

Do NOT continue the conversation. Do NOT respond to any questions in the conversation. ONLY output the structured summary.";

const SUMMARIZATION_PROMPT: &str = "The messages above are a conversation to summarize. Create a structured context checkpoint summary that another LLM will use to continue the work. If the conversation starts with an earlier summary, preserve its information and fold the newer messages into it.

Use this EXACT format:

## Goal
[What is the user trying to accomplish? Can be multiple items if the session covers different tasks.]

## Constraints & Preferences
- [Any constraints, preferences, or requirements mentioned by user]
- [Or \"(none)\" if none were mentioned]

## Progress
### Done
- [x] [Completed tasks/changes]

### In Progress
- [ ] [Current work]

### Blocked
- [Issues preventing progress, if any]

## Key Decisions
- **[Decision]**: [Brief rationale]

## Next Steps
1. [Ordered list of what should happen next]

## Critical Context
- [Any data, examples, or references needed to continue]
- [Or \"(none)\" if not applicable]

Keep each section concise. Preserve exact file paths, function names, and error messages.";

/// The summary of a clean `stop` with text and no tool call; anything else
/// is not a summary.
pub(super) fn summary_text(message: &AssistantMessage) -> Option<String> {
    if message.stop_reason != StopReason::Stop || has_tool_call(message) {
        return None;
    }
    let text = message
        .content
        .iter()
        .filter_map(|content| match content {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n");
    let text = text.trim_matches(is_js_whitespace);
    (!text.is_empty()).then(|| text.to_owned())
}

/// The failure message of a response that is not a summary.
pub(super) fn summary_failure(message: &AssistantMessage) -> String {
    if matches!(message.stop_reason, StopReason::Error | StopReason::Aborted) {
        let reason = message
            .error_message
            .as_deref()
            .unwrap_or_else(|| message.stop_reason.as_str());
        return format!("Summarization failed: {reason}");
    }
    if message.stop_reason == StopReason::Length {
        return "Summarization hit the token limit; the summary is incomplete".to_owned();
    }
    if has_tool_call(message) {
        return "Summarization attempted to call a tool".to_owned();
    }
    "Summarization produced no text".to_owned()
}

fn has_tool_call(message: &AssistantMessage) -> bool {
    message
        .content
        .iter()
        .any(|content| matches!(content, AssistantContentBlock::ToolCall(_)))
}

/// The summarizer's user message: the serialized conversation, the prompt,
/// and any instructions.
pub(super) fn summary_prompt(messages: &[Message], instructions: Option<&str>) -> String {
    let focus = instructions.map_or_else(String::new, |instructions| {
        format!("\n\nAdditional focus: {instructions}")
    });
    format!(
        "<conversation>\n{}\n</conversation>\n\n{SUMMARIZATION_PROMPT}{focus}",
        serialize_conversation(messages)
    )
}

/// Messages as plain text, so the summarizer reads a transcript instead of
/// continuing it. System messages are omitted.
#[must_use]
pub fn serialize_conversation(messages: &[Message]) -> String {
    let mut parts: Vec<String> = Vec::new();
    for message in messages {
        match message {
            Message::User(user) => {
                let text = user_text(&user.content);
                if !text.is_empty() {
                    parts.push(format!("[User]: {text}"));
                }
            }
            Message::Assistant(assistant) => {
                let mut thinking = Vec::new();
                let mut text = Vec::new();
                let mut calls = Vec::new();
                for content in &assistant.content {
                    match content {
                        AssistantContentBlock::Thinking(block) => {
                            thinking.push(block.thinking.as_str());
                        }
                        AssistantContentBlock::Text(block) => text.push(block.text.as_str()),
                        AssistantContentBlock::ToolCall(call) => {
                            // `Object.entries()` enumerates in JS own-key order.
                            let arguments = JsonObject::from_iter(
                                call.arguments
                                    .iter()
                                    .map(|(key, value)| (key.as_str(), JsonValue::from(value))),
                            );
                            let arguments = arguments
                                .iter()
                                .map(|(key, value)| format!("{key}={value}"))
                                .collect::<Vec<_>>()
                                .join(", ");
                            calls.push(format!("{}({arguments})", call.name));
                        }
                    }
                }
                if !thinking.is_empty() {
                    parts.push(format!("[Assistant thinking]: {}", thinking.join("\n")));
                }
                if !text.is_empty() {
                    parts.push(format!("[Assistant]: {}", text.join("\n")));
                }
                if !calls.is_empty() {
                    parts.push(format!("[Assistant tool calls]: {}", calls.join("; ")));
                }
            }
            Message::ToolResult(result) => {
                let text = block_text(&result.content);
                if !text.is_empty() {
                    parts.push(format!(
                        "[Tool result]: {}",
                        truncate(&text, TOOL_RESULT_MAX_CHARS)
                    ));
                }
            }
            Message::System(_) => {}
        }
    }
    parts.join("\n\n")
}

fn user_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => block_text(blocks),
    }
}

fn block_text(blocks: &[UserContentBlock]) -> String {
    blocks
        .iter()
        .filter_map(|block| match block {
            UserContentBlock::Text(text) => Some(text.text.as_str()),
            UserContentBlock::Image(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// TS `text.slice(0, maxChars)` plus a note, counting UTF-16 code units; the
/// cut never splits a character, so a surrogate pair straddling the limit
/// is dropped whole.
fn truncate(text: &str, max_chars: usize) -> String {
    let length: usize = text.chars().map(char::len_utf16).sum();
    if length <= max_chars {
        return text.to_owned();
    }
    let mut units = 0;
    let mut end = 0;
    for (index, character) in text.char_indices() {
        units += character.len_utf16();
        if units > max_chars {
            break;
        }
        end = index + character.len_utf8();
    }
    format!(
        "{}\n\n[... {} more characters truncated]",
        &text[..end],
        length - max_chars
    )
}

/// JS `String.prototype.trim` whitespace: `WhiteSpace` and `LineTerminator`.
/// Rust's `White_Space` adds U+0085 and lacks U+FEFF.
fn is_js_whitespace(character: char) -> bool {
    (character.is_whitespace() && character != '\u{85}') || character == '\u{feff}'
}
