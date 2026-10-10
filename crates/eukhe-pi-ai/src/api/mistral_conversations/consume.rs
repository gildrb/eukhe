//! Streaming core of the Mistral chat API: turns parsed SSE chunks into
//! assistant message events. Section of the port of
//! `api/mistral-conversations.ts` (`consumeChatStream`).

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, IndexMap, JsonObject,
    JsonValue, Model, StopReason, TextContent, ThinkingContent, ToolCall,
};

use super::transport::MistralEventReader;
use super::{derive_mistral_tool_call_id, is_truthy, type_error};
use crate::models::calculate_cost;
use crate::types::OnProviderStreamEvent;
use crate::utils::diagnostics::Thrown;
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::js::{js_to_string, json_stringify};
use crate::utils::json_parse::parse_streaming_json_object;
use crate::utils::sanitize_unicode::sanitize_surrogates;

/// The open text or thinking block (always the last content block).
#[derive(Clone, Copy, PartialEq, Eq)]
enum CurrentBlock {
    Text,
    Thinking,
}

/// TS `toolBlocksByKey` key: `toolCall.index ?? callId`.
#[derive(Clone, PartialEq, Eq, Hash)]
enum ToolKey {
    /// A numeric index, by its JS string form.
    Index(String),
    Id(String),
}

/// A streamed tool call block and its argument scratch buffer (TS
/// `partialArgs`, never persisted).
struct ToolBlock {
    content_index: usize,
    partial_args: String,
}

struct ChatStreamState<'a> {
    output: &'a mut AssistantMessage,
    stream: &'a AssistantMessageEventStream,
    current: Option<CurrentBlock>,
    tool_blocks: IndexMap<ToolKey, ToolBlock>,
}

/// `value || 0` for a JS number field.
fn number_or_zero(value: Option<&JsonValue>) -> f64 {
    value
        .and_then(JsonValue::as_f64)
        .filter(|number| *number != 0.0 && !number.is_nan())
        .unwrap_or(0.0)
}

/// A token count as stored in [`eukhe_types::pi_ai::Usage`].
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // Non-negative token counts far below 2^53.
fn tokens(value: f64) -> u64 {
    value.max(0.0) as u64
}

/// TS `getMistralCachedPromptTokens`.
fn get_mistral_cached_prompt_tokens(usage: &JsonObject, prompt_tokens: f64) -> f64 {
    let nested = |outer: &str, inner: &str| {
        usage
            .get(outer)
            .and_then(|details| details.get(inner))
            .filter(|value| !value.is_null())
    };
    let raw_cached_tokens = nested("promptTokensDetails", "cachedTokens")
        .or_else(|| nested("prompt_tokens_details", "cached_tokens"))
        .or_else(|| nested("promptTokenDetails", "cachedTokens"))
        .or_else(|| nested("prompt_token_details", "cached_tokens"))
        .or_else(|| {
            usage
                .get("numCachedTokens")
                .filter(|value| !value.is_null())
        })
        .or_else(|| {
            usage
                .get("num_cached_tokens")
                .filter(|value| !value.is_null())
        });
    let cached_tokens = raw_cached_tokens
        .and_then(JsonValue::as_f64)
        .filter(|number| number.is_finite())
        .unwrap_or(0.0);
    prompt_tokens.min(cached_tokens.max(0.0))
}

/// TS `mapChatStopReason`.
fn map_chat_stop_reason(reason: &str) -> (StopReason, Option<String>) {
    match reason {
        "stop" => (StopReason::Stop, None),
        "length" | "model_length" => (StopReason::Length, None),
        "tool_calls" => (StopReason::ToolUse, None),
        "error" => (
            StopReason::Error,
            // Mistral reports transient server failures this way; "server error" makes the message retryable.
            Some("Provider stopped with: error (server error)".to_owned()),
        ),
        other => (
            StopReason::Error,
            Some(format!("Provider stopped with: {other}")),
        ),
    }
}

/// A JS string's text, or the `?? ""` default for a missing/null value.
fn text_or_empty(value: Option<&JsonValue>) -> String {
    match value {
        None | Some(JsonValue::Null) => String::new(),
        Some(JsonValue::String(text)) => text.clone(),
        Some(other) => js_to_string(other),
    }
}

impl ChatStreamState<'_> {
    fn push(&self, event: AssistantMessageEvent) {
        self.stream.push(event);
    }

    fn block_index(&self) -> usize {
        self.output.content.len() - 1
    }

    /// TS `finishCurrentBlock`.
    fn finish_current_block(&mut self) {
        let Some(current) = self.current.take() else {
            return;
        };
        let content_index = self.block_index();
        let event = match (current, &self.output.content[content_index]) {
            (CurrentBlock::Text, AssistantContentBlock::Text(block)) => {
                AssistantMessageEvent::TextEnd {
                    content_index,
                    content: block.text.clone(),
                    partial: self.output.clone(),
                }
            }
            (CurrentBlock::Thinking, AssistantContentBlock::Thinking(block)) => {
                AssistantMessageEvent::ThinkingEnd {
                    content_index,
                    content: block.thinking.clone(),
                    partial: self.output.clone(),
                }
            }
            _ => return,
        };
        self.push(event);
    }

    fn append_text(&mut self, delta: String) {
        if self.current != Some(CurrentBlock::Text) {
            self.finish_current_block();
            self.current = Some(CurrentBlock::Text);
            self.output
                .content
                .push(AssistantContentBlock::Text(TextContent::new("")));
            self.push(AssistantMessageEvent::TextStart {
                content_index: self.block_index(),
                partial: self.output.clone(),
            });
        }
        let content_index = self.block_index();
        if let Some(AssistantContentBlock::Text(block)) = self.output.content.last_mut() {
            block.text.push_str(&delta);
        }
        self.push(AssistantMessageEvent::TextDelta {
            content_index,
            delta,
            partial: self.output.clone(),
        });
    }

    fn append_thinking(&mut self, delta: String) {
        if self.current != Some(CurrentBlock::Thinking) {
            self.finish_current_block();
            self.current = Some(CurrentBlock::Thinking);
            self.output
                .content
                .push(AssistantContentBlock::Thinking(ThinkingContent::default()));
            self.push(AssistantMessageEvent::ThinkingStart {
                content_index: self.block_index(),
                partial: self.output.clone(),
            });
        }
        let content_index = self.block_index();
        if let Some(AssistantContentBlock::Thinking(block)) = self.output.content.last_mut() {
            block.thinking.push_str(&delta);
        }
        self.push(AssistantMessageEvent::ThinkingDelta {
            content_index,
            delta,
            partial: self.output.clone(),
        });
    }

    fn apply_usage(&mut self, model: &Model, usage: &JsonObject) {
        let prompt_tokens = number_or_zero(usage.get("prompt_tokens"));
        let cached_prompt_tokens = get_mistral_cached_prompt_tokens(usage, prompt_tokens);
        let output_usage = &mut self.output.usage;
        output_usage.input = tokens(prompt_tokens - cached_prompt_tokens);
        output_usage.output = tokens(number_or_zero(usage.get("completion_tokens")));
        output_usage.cache_read = tokens(cached_prompt_tokens);
        output_usage.cache_write = 0;
        let total = number_or_zero(usage.get("total_tokens"));
        output_usage.total_tokens = if total == 0.0 {
            output_usage.input
                + output_usage.output
                + output_usage.cache_read
                + output_usage.cache_write
        } else {
            tokens(total)
        };
        calculate_cost(model, output_usage);
    }

    fn apply_content(&mut self, content: &JsonValue) -> Result<(), Thrown> {
        let items: Vec<&JsonValue> = match content {
            JsonValue::String(_) => vec![content],
            JsonValue::Array(items) => items.iter().collect(),
            JsonValue::Null => return Ok(()),
            JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::Object(_) => {
                return Err(type_error("delta.content is not iterable"))
            }
        };
        for item in items {
            match item {
                JsonValue::String(text) => {
                    // GLM models on Mistral send empty content deltas around
                    // thinking and tool calls. Opening a block for them splits
                    // thinking into multiple blocks, which Mistral rejects on replay.
                    let delta = sanitize_surrogates(text).into_owned();
                    if !delta.is_empty() {
                        self.append_text(delta);
                    }
                }
                JsonValue::Null => {
                    return Err(type_error(
                        "Cannot read properties of null (reading 'type')",
                    ))
                }
                JsonValue::Object(chunk) => match chunk.get("type").and_then(JsonValue::as_str) {
                    Some("thinking") => {
                        let parts = match chunk.get("thinking") {
                            Some(JsonValue::Array(parts)) => parts.as_slice(),
                            _ => &[],
                        };
                        let delta_text: String = parts
                            .iter()
                            .filter_map(|part| part.get("text").and_then(JsonValue::as_str))
                            .collect();
                        let delta = sanitize_surrogates(&delta_text).into_owned();
                        if !delta.is_empty() {
                            self.append_thinking(delta);
                        }
                    }
                    Some("text") => {
                        let text = text_or_empty(chunk.get("text"));
                        let delta = sanitize_surrogates(&text).into_owned();
                        if !delta.is_empty() {
                            self.append_text(delta);
                        }
                    }
                    _ => {}
                },
                JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::Array(_) => {}
            }
        }
        Ok(())
    }

    fn apply_tool_call(&mut self, tool_call: &JsonValue) -> Result<(), Thrown> {
        if self.current.is_some() {
            self.finish_current_block();
        }
        let index = tool_call.get("index").filter(|value| !value.is_null());
        let call_id = match tool_call.get("id").and_then(JsonValue::as_str) {
            Some(id) if !id.is_empty() && id != "null" => id.to_owned(),
            _ => derive_mistral_tool_call_id(
                &format!(
                    "toolcall:{}",
                    index.map_or_else(|| "0".to_owned(), js_to_string)
                ),
                0,
            ),
        };
        let key = match index {
            Some(index) => ToolKey::Index(js_to_string(index)),
            None => ToolKey::Id(call_id.clone()),
        };
        let function = match tool_call.get("function") {
            Some(JsonValue::Object(function)) => function,
            Some(JsonValue::Null) => {
                return Err(type_error(
                    "Cannot read properties of null (reading 'name')",
                ))
            }
            _ => {
                return Err(type_error(
                    "Cannot read properties of undefined (reading 'name')",
                ))
            }
        };

        if !self.tool_blocks.contains_key(&key) {
            self.output
                .content
                .push(AssistantContentBlock::ToolCall(ToolCall {
                    id: call_id,
                    name: text_or_empty(function.get("name")),
                    arguments: JsonObject::new(),
                    thought_signature: None,
                    namespace: None,
                }));
            let content_index = self.output.content.len() - 1;
            self.tool_blocks.insert(
                key.clone(),
                ToolBlock {
                    content_index,
                    partial_args: String::new(),
                },
            );
            self.push(AssistantMessageEvent::ToolCallStart {
                content_index,
                partial: self.output.clone(),
            });
        }

        let args_delta = match function.get("arguments") {
            Some(JsonValue::String(arguments)) => arguments.clone(),
            Some(arguments) if is_truthy(arguments) => json_stringify(arguments),
            _ => "{}".to_owned(),
        };
        let block = self
            .tool_blocks
            .get_mut(&key)
            .expect("tool block registered above");
        block.partial_args.push_str(&args_delta);
        let content_index = block.content_index;
        let arguments = parse_streaming_json_object(Some(&block.partial_args));
        if let AssistantContentBlock::ToolCall(call) = &mut self.output.content[content_index] {
            call.arguments = arguments;
        }
        self.push(AssistantMessageEvent::ToolCallDelta {
            content_index,
            delta: args_delta,
            partial: self.output.clone(),
        });
        Ok(())
    }

    fn apply_chunk(&mut self, model: &Model, chunk: &JsonValue) -> Result<(), Thrown> {
        // Mistral's streamed CompletionChunk carries an id field. Keep the
        // first non-empty one (`output.responseId ||= chunk.id`).
        if self.output.response_id.as_deref().is_none_or(str::is_empty) {
            self.output.response_id = chunk
                .get("id")
                .and_then(JsonValue::as_str)
                .map(str::to_owned);
        }
        if let Some(JsonValue::Object(usage)) = chunk.get("usage") {
            self.apply_usage(model, usage);
        }

        let Some(choice) = chunk
            .get("choices")
            .and_then(JsonValue::as_array)
            .and_then(|choices| choices.first())
        else {
            return Ok(());
        };
        if choice.is_null() {
            return Err(type_error(
                "Cannot read properties of null (reading 'finish_reason')",
            ));
        }

        if let Some(reason) = choice
            .get("finish_reason")
            .filter(|reason| is_truthy(reason))
        {
            let reason = match reason {
                JsonValue::String(reason) => reason.clone(),
                other => js_to_string(other),
            };
            let (stop_reason, error_message) = map_chat_stop_reason(&reason);
            self.output.raw_stop_reason = Some(reason);
            self.output.stop_reason = stop_reason;
            if error_message.is_some() {
                self.output.error_message = error_message;
            }
        }

        let delta = match choice.get("delta") {
            Some(JsonValue::Null) => {
                return Err(type_error(
                    "Cannot read properties of null (reading 'content')",
                ))
            }
            Some(delta) => delta,
            None => {
                return Err(type_error(
                    "Cannot read properties of undefined (reading 'content')",
                ))
            }
        };
        if let Some(content) = delta.get("content") {
            self.apply_content(content)?;
        }

        if let Some(tool_calls) = delta.get("tool_calls").filter(|calls| is_truthy(calls)) {
            let JsonValue::Array(tool_calls) = tool_calls else {
                return Err(type_error("toolCalls is not iterable"));
            };
            for tool_call in tool_calls {
                self.apply_tool_call(tool_call)?;
            }
        }
        Ok(())
    }

    /// The end of the TS `consumeChatStream`.
    fn finish(&mut self) {
        self.finish_current_block();
        let blocks: Vec<(usize, String)> = self
            .tool_blocks
            .values()
            .map(|block| (block.content_index, block.partial_args.clone()))
            .collect();
        for (content_index, partial_args) in blocks {
            let AssistantContentBlock::ToolCall(call) = &mut self.output.content[content_index]
            else {
                continue;
            };
            call.arguments = parse_streaming_json_object(Some(&partial_args));
            let tool_call = call.clone();
            self.push(AssistantMessageEvent::ToolCallEnd {
                content_index,
                tool_call,
                partial: self.output.clone(),
            });
        }
    }
}

/// TS `consumeChatStream`.
pub(super) async fn consume_chat_stream(
    model: &Model,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
    events: &mut MistralEventReader,
    on_provider_stream_event: Option<&OnProviderStreamEvent>,
) -> Result<(), Thrown> {
    let mut state = ChatStreamState {
        output,
        stream,
        current: None,
        tool_blocks: IndexMap::new(),
    };
    while let Some(event) = events.next_event().await? {
        if let Some(callback) = on_provider_stream_event {
            callback(&event, model).await?;
        }
        state.apply_chunk(model, &event)?;
    }
    state.finish();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn cached_tokens_follow_the_alias_chain() {
        let JsonValue::Object(usage) = json!({
            "prompt_tokens_details": { "cached_tokens": null },
            "num_cached_tokens": 5,
        }) else {
            unreachable!()
        };
        assert!((get_mistral_cached_prompt_tokens(&usage, 4.0) - 4.0).abs() < f64::EPSILON);
    }

    #[test]
    fn stop_reasons() {
        assert!(matches!(
            map_chat_stop_reason("model_length"),
            (StopReason::Length, None)
        ));
        assert_eq!(
            map_chat_stop_reason("x").1.as_deref(),
            Some("Provider stopped with: x")
        );
    }
}
