//! Message and transcript token counts over `pi_ai` messages, with the
//! reading model's real tokenizer ([`eukhe_tokens::Tokenizer`]).

use std::sync::Arc;

use eukhe_tokens::{MessageParts, ModelRef, Tokenizer};
use eukhe_types::pi_ai::{Message, Model, StopReason, Usage};

use super::js::json_stringify;
use super::text::get_system_message_text;

/// The context size of a transcript.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ContextTokens {
    /// Total context tokens.
    pub tokens: u64,
    /// Tokens reported by the most recent applicable assistant usage block.
    pub usage_tokens: u64,
    /// Counted tokens of the messages after that usage block.
    pub trailing_tokens: u64,
    /// Index of the applicable message that provided usage, if any.
    pub last_usage_index: Option<usize>,
}

/// The shared tokenizer of the model a request goes to.
#[must_use]
pub fn model_tokenizer(model: &Model) -> Arc<Tokenizer> {
    Tokenizer::for_model(ModelRef {
        id: &model.id,
        provider: &model.provider,
        api: &model.api,
    })
}

/// Context tokens a usage block describes: `total_tokens`, or the sum of its parts when zero.
#[must_use]
pub fn calculate_context_tokens(usage: &Usage) -> u64 {
    if usage.total_tokens != 0 {
        return usage.total_tokens;
    }
    usage.input + usage.output + usage.cache_read + usage.cache_write
}

/// `JSON.stringify(value)` of a serializable value.
fn stringify<T: serde::Serialize>(value: &T) -> String {
    // Transcript types always serialize (string keys, finite numbers); the
    // TS fallback for unserializable values is `[unserializable]`.
    serde_json::to_value(value).map_or_else(
        |_| "[unserializable]".to_owned(),
        |value| json_stringify(&value),
    )
}

/// Tokens one message adds to a request under `tokenizer`: a system
/// message its prompt text and the tool declarations it adds or removes.
#[must_use]
pub fn message_tokens(tokenizer: &Tokenizer, message: &Message) -> u64 {
    let Message::System(system) = message else {
        return MessageParts::from_pi_ai(message)
            .map_or(0, |parts| tokenizer.count_message(&parts));
    };
    let mut fragments = vec![get_system_message_text(system)];
    for tools in [
        system.tools_added.as_ref().map(stringify),
        system.tools_removed.as_ref().map(stringify),
    ]
    .into_iter()
    .flatten()
    {
        fragments.push(tools);
    }
    tokenizer.count_fragments(&fragments)
}

/// The last assistant usage that still describes the transcript prefix.
fn get_last_assistant_usage_info(messages: &[Message]) -> Option<(&Usage, usize)> {
    let mut latest_prefix_timestamp: Option<u64> = None;
    let mut usage_info = None;
    for (index, message) in messages.iter().enumerate() {
        if let Message::Assistant(assistant) = message {
            // A newer prefix message was inserted after this response (for
            // example a compaction summary), so its usage cannot describe the
            // current prefix.
            let usage_applies_to_prefix =
                latest_prefix_timestamp.is_none_or(|latest| assistant.timestamp >= latest);
            if usage_applies_to_prefix
                && assistant.stop_reason != StopReason::Aborted
                && assistant.stop_reason != StopReason::Error
                && calculate_context_tokens(&assistant.usage) > 0
            {
                usage_info = Some((&assistant.usage, index));
            }
        }
        let timestamp = message.timestamp();
        latest_prefix_timestamp =
            Some(latest_prefix_timestamp.map_or(timestamp, |latest| latest.max(timestamp)));
    }
    usage_info
}

/// The context size of a transcript (pass `TranscriptContext::messages()`
/// for a normalized context): the last applicable assistant usage plus the
/// counted tokens of the messages after it, or of every message.
#[must_use]
pub fn context_tokens(tokenizer: &Tokenizer, messages: &[Message]) -> ContextTokens {
    let count = |messages: &[Message]| -> u64 {
        messages
            .iter()
            .map(|message| message_tokens(tokenizer, message))
            .sum()
    };
    if let Some((usage, index)) = get_last_assistant_usage_info(messages) {
        let usage_tokens = calculate_context_tokens(usage);
        let trailing_tokens = count(&messages[index + 1..]);
        return ContextTokens {
            tokens: usage_tokens + trailing_tokens,
            usage_tokens,
            trailing_tokens,
            last_usage_index: Some(index),
        };
    }
    let tokens = count(messages);
    ContextTokens {
        tokens,
        usage_tokens: 0,
        trailing_tokens: tokens,
        last_usage_index: None,
    }
}

/// Locally counted prompt tokens are padded by 1/this before the output
/// cap is sized: the provider's tokenizer can disagree with the local one
/// by a few percent.
const LOCAL_COUNT_MARGIN_DIVISOR: u64 = 10;

/// Chat-template framing charged per locally counted message: a count is
/// message content, and every template wraps a message in role markers and
/// separators.
const MESSAGE_FRAMING_TOKENS: u64 = 16;

/// The prompt of a request as the output cap sizes it: the provider's
/// count at the last applicable assistant usage, exact, plus the local
/// count of the messages after it (of every message without one), padded
/// by a tenth and [`MESSAGE_FRAMING_TOKENS`] per message.
#[must_use]
pub fn output_cap_prompt_tokens(tokenizer: &Tokenizer, messages: &[Message]) -> u64 {
    let counted = context_tokens(tokenizer, messages);
    let local_messages = messages.len() - counted.last_usage_index.map_or(0, |index| index + 1);
    counted.tokens
        + counted.trailing_tokens.div_ceil(LOCAL_COUNT_MARGIN_DIVISOR)
        + local_messages as u64 * MESSAGE_FRAMING_TOKENS
}

#[cfg(test)]
mod tests {
    use eukhe_tokens::Encoding;
    use eukhe_types::pi_ai::{
        AssistantContentBlock, AssistantMessage, Context, TextContent, UserContent, UserMessage,
    };

    use super::*;
    use crate::utils::transcript::normalize_context;

    const MODEL: ModelRef<'static> = ModelRef {
        id: "test-model",
        provider: "openai",
        api: "openai-responses",
    };

    fn create_usage(total_tokens: u64) -> Usage {
        Usage {
            input: total_tokens,
            total_tokens,
            ..Usage::default()
        }
    }

    fn create_assistant(timestamp: u64, total_tokens: u64) -> Message {
        Message::Assistant(AssistantMessage {
            content: vec![AssistantContentBlock::Text(TextContent::new("kept"))],
            api: MODEL.api.into(),
            provider: MODEL.provider.into(),
            model: MODEL.id.into(),
            response_model: None,
            response_id: None,
            provider_thinking_level: None,
            thinking_level: None,
            diagnostics: None,
            usage: create_usage(total_tokens),
            stop_reason: StopReason::Stop,
            deferred: None,
            error_message: None,
            raw_stop_reason: None,
            end_turn: None,
            timestamp,
            duration_ms: None,
            timing: None,
        })
    }

    fn user(text: &str, timestamp: u64) -> Message {
        Message::User(UserMessage {
            content: UserContent::Text(text.into()),
            timestamp,
        })
    }

    fn o200k(text: &str) -> u64 {
        u64::from(Encoding::O200kBase.count(text))
    }

    /// New text after the last usage counts with the model's tokenizer
    /// (`o200k_base` for a model the catalog names no tokenizer for).
    #[test]
    fn counts_new_text_after_the_last_usage() {
        let tail = "The quick brown fox jumps over the lazy dog. ".repeat(80);
        let context = normalize_context(Context {
            system_prompt: None,
            messages: vec![create_assistant(100, 2_000), user(&tail, 200)],
            tools: None,
        });
        assert_eq!(
            context_tokens(&Tokenizer::for_model(MODEL), context.messages()),
            ContextTokens {
                tokens: 2_000 + o200k(&tail),
                usage_tokens: 2_000,
                trailing_tokens: o200k(&tail),
                last_usage_index: Some(0),
            }
        );
    }

    #[test]
    fn ignores_stale_assistant_usage_after_a_newer_message_is_inserted_before_it() {
        let tail = "x".repeat(4_000);
        let context = normalize_context(Context {
            system_prompt: Some("system".into()),
            messages: vec![
                user("summary", 200),
                create_assistant(100, 9_500),
                user(&tail, 300),
            ],
            tools: None,
        });
        let counted = o200k("system") + o200k("summary") + o200k("kept") + o200k(&tail);
        assert_eq!(
            context_tokens(&Tokenizer::for_model(MODEL), context.messages()),
            ContextTokens {
                tokens: counted,
                usage_tokens: 0,
                trailing_tokens: counted,
                last_usage_index: None,
            }
        );
    }

    #[test]
    fn uses_assistant_usage_again_after_a_response_to_the_inserted_context() {
        let context = normalize_context(Context {
            system_prompt: None,
            messages: vec![
                user("summary", 200),
                create_assistant(100, 9_500),
                user("new prompt", 300),
                create_assistant(400, 2_000),
                user("tail", 500),
            ],
            tools: None,
        });
        assert_eq!(
            context_tokens(&Tokenizer::for_model(MODEL), context.messages()),
            ContextTokens {
                tokens: 2_000 + o200k("tail"),
                usage_tokens: 2_000,
                trailing_tokens: o200k("tail"),
                last_usage_index: Some(3),
            }
        );
    }

    /// The output cap's prompt keeps the provider's count exact and pads
    /// only the locally counted tail: a tenth of its tokens, rounded up,
    /// and 16 framing tokens per message.
    #[test]
    fn the_output_cap_prompt_pads_only_the_locally_counted_messages() {
        let tail = " x".repeat(1_005);
        assert_eq!(o200k(&tail), 1_005);
        let tokenizer = Tokenizer::for_model(MODEL);
        let anchored = normalize_context(Context {
            system_prompt: None,
            messages: vec![
                user("first", 100),
                create_assistant(200, 2_000),
                user(&tail, 300),
                user(&tail, 400),
            ],
            tools: None,
        });
        assert_eq!(
            output_cap_prompt_tokens(&tokenizer, anchored.messages()),
            2_000 + 2_010 + 201 + 2 * 16
        );
        let unanchored = normalize_context(Context {
            system_prompt: None,
            messages: vec![user(&tail, 100)],
            tools: None,
        });
        assert_eq!(
            output_cap_prompt_tokens(&tokenizer, unanchored.messages()),
            1_005 + 101 + 16
        );
    }
}
