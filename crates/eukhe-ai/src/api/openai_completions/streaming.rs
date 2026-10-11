//! Chunk-to-event translation of the streaming loop in TS `stream`: block
//! bookkeeping, usage parsing, and stop-reason mapping.

use std::collections::HashMap;

use crate::types::IndexMap;

use super::convert::{append_openai_reasoning_detail, is_openai_reasoning_detail, js_truthy};
use crate::api::constrained_sampling::{
    append_grammar_tool_input_json_delta, GrammarInputClose, GrammarToolInputJsonBuffer,
};
use crate::models::calculate_cost;
use crate::types::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, JsonObject, JsonValue, Model,
    StopReason, TextContent, ThinkingContent, ToolCall, Usage, UsageCost,
};
use crate::utils::diagnostics::{thrown, Thrown};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::js::json_stringify;
use crate::utils::json_parse::parse_streaming_json_object;

/// `customInput` of a streaming custom (grammar) tool call.
#[derive(Debug, Clone)]
struct CustomInput {
    property: String,
    json_buffer: GrammarToolInputJsonBuffer,
}

/// The streaming scratch fields TS keeps on a tool-call block
/// (`partialArgs`, `customInput`, `streamIndex`); they never reach events
/// or the final message.
#[derive(Debug, Clone, Default)]
struct ToolScratch {
    partial_args: Option<String>,
    custom_input: Option<CustomInput>,
    stream_index: Option<u64>,
}

/// `typeof index === "number"` as a map key (bit pattern of the double).
fn stream_index_key(value: Option<&JsonValue>) -> Option<u64> {
    value.and_then(JsonValue::as_f64).map(f64::to_bits)
}

/// TS `mapStopReason`.
pub(crate) fn map_stop_reason(reason: &str) -> (StopReason, Option<String>) {
    match reason {
        "stop" | "end" => (StopReason::Stop, None),
        "length" => (StopReason::Length, None),
        "function_call" | "tool_calls" => (StopReason::ToolUse, None),
        other => (
            StopReason::Error,
            Some(format!("Provider finish_reason: {other}")),
        ),
    }
}

/// `value || 0` for a token count.
fn count_or_zero(value: Option<&JsonValue>) -> f64 {
    value
        .and_then(JsonValue::as_f64)
        .filter(|count| !count.is_nan())
        .unwrap_or(0.0)
}

/// `a ?? b ?? ...` over numeric properties.
fn first_count(values: &[Option<&JsonValue>]) -> f64 {
    values
        .iter()
        .find_map(|value| value.filter(|value| !value.is_null()))
        .and_then(JsonValue::as_f64)
        .unwrap_or(0.0)
}

// Token counts are whole JS numbers far below 2^53.
#[allow(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]
fn tokens(value: f64) -> u64 {
    value.max(0.0) as u64
}

/// TS `parseChunkUsage`: cached tokens are cache reads; providers place them
/// in `prompt_tokens_details.cached_tokens` (`OpenAI`/`OpenRouter`),
/// `prompt_cache_hit_tokens` (`DeepSeek`), or top-level `cached_tokens` (Kimi).
/// Cache writes are counted separately and never subtracted from reads.
pub(crate) fn parse_chunk_usage(raw_usage: &JsonValue, model: &Model) -> Usage {
    let details = raw_usage.get("prompt_tokens_details");
    let prompt_tokens = count_or_zero(raw_usage.get("prompt_tokens"));
    let cache_read_tokens = first_count(&[
        details.and_then(|details| details.get("cached_tokens")),
        raw_usage.get("prompt_cache_hit_tokens"),
        raw_usage.get("cached_tokens"),
    ]);
    let cache_write_tokens =
        count_or_zero(details.and_then(|details| details.get("cache_write_tokens")));
    let input = (prompt_tokens - cache_read_tokens - cache_write_tokens).max(0.0);
    // OpenAI completion_tokens already includes reasoning_tokens.
    let output_tokens = count_or_zero(raw_usage.get("completion_tokens"));
    let reasoning = count_or_zero(
        raw_usage
            .get("completion_tokens_details")
            .and_then(|details| details.get("reasoning_tokens")),
    );
    let mut usage = Usage {
        input: tokens(input),
        output: tokens(output_tokens),
        cache_read: tokens(cache_read_tokens),
        cache_write: tokens(cache_write_tokens),
        cache_write_1h: None,
        reasoning: Some(tokens(reasoning)),
        total_tokens: tokens(input + output_tokens + cache_read_tokens + cache_write_tokens),
        cost: UsageCost::default(),
    };
    calculate_cost(model, &mut usage);
    usage
}

/// Streaming state of one response.
pub(crate) struct StreamState<'a> {
    pub(crate) output: AssistantMessage,
    stream: &'a AssistantMessageEventStream,
    model: &'a Model,
    grammar_tool_input_properties: &'a IndexMap<String, String>,
    text_block: Option<usize>,
    thinking_block: Option<usize>,
    pub(crate) has_finish_reason: bool,
    tool_blocks_by_index: HashMap<u64, usize>,
    tool_blocks_by_id: HashMap<String, usize>,
    scratch: HashMap<usize, ToolScratch>,
    /// `reasoning_details` are replay metadata, not user-visible deltas: kept
    /// in memory and serialized once when the thinking block is finalized.
    streamed_reasoning_details: Option<Vec<JsonValue>>,
    /// eukhe addition: the `service_tier` the provider reports on its chunks.
    pub(crate) response_service_tier: Option<String>,
}

impl<'a> StreamState<'a> {
    pub(crate) fn new(
        output: AssistantMessage,
        stream: &'a AssistantMessageEventStream,
        model: &'a Model,
        grammar_tool_input_properties: &'a IndexMap<String, String>,
    ) -> Self {
        Self {
            output,
            stream,
            model,
            grammar_tool_input_properties,
            text_block: None,
            thinking_block: None,
            has_finish_reason: false,
            tool_blocks_by_index: HashMap::new(),
            tool_blocks_by_id: HashMap::new(),
            scratch: HashMap::new(),
            streamed_reasoning_details: None,
            response_service_tier: None,
        }
    }

    fn partial(&self) -> AssistantMessage {
        self.output.clone()
    }

    fn push(&self, event: AssistantMessageEvent) {
        self.stream.push(event);
    }

    /// TS `applyStreamedReasoningDetails` on every thinking block.
    pub(crate) fn apply_streamed_reasoning_details(&mut self) {
        let Some(details) = &self.streamed_reasoning_details else {
            return;
        };
        let signature = json_stringify(&JsonValue::Array(details.clone()));
        for block in &mut self.output.content {
            if let AssistantContentBlock::Thinking(thinking) = block {
                thinking.thinking_signature = Some(signature.clone());
            }
        }
    }
    /// The `start` event.
    pub(crate) fn push_start(&self) {
        self.push(AssistantMessageEvent::Start {
            partial: self.partial(),
        });
    }

    fn tool_call(&mut self, index: usize) -> &mut ToolCall {
        match &mut self.output.content[index] {
            AssistantContentBlock::ToolCall(tool_call) => tool_call,
            AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => {
                unreachable!("tool-call bookkeeping only indexes tool-call blocks")
            }
        }
    }

    fn custom_tool_call_input(&self, index: usize) -> String {
        let Some(custom) = self
            .scratch
            .get(&index)
            .and_then(|s| s.custom_input.as_ref())
        else {
            return String::new();
        };
        match &self.output.content[index] {
            AssistantContentBlock::ToolCall(tool_call) => tool_call
                .arguments
                .get(&custom.property)
                .and_then(JsonValue::as_str)
                .unwrap_or_default()
                .to_owned(),
            AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => String::new(),
        }
    }

    fn append_custom_tool_call_input(
        &mut self,
        index: usize,
        next_input: &str,
        close: GrammarInputClose,
    ) -> Result<Option<String>, Thrown> {
        let Some(custom) = self
            .scratch
            .get_mut(&index)
            .and_then(|scratch| scratch.custom_input.as_mut())
        else {
            return Ok(None);
        };
        let delta = append_grammar_tool_input_json_delta(
            &mut custom.json_buffer,
            &custom.property,
            next_input,
            close,
        )
        .map_err(thrown)?;
        let property = custom.property.clone();
        let mut arguments = JsonObject::new();
        arguments.insert(property, JsonValue::String(next_input.to_owned()));
        self.tool_call(index).arguments = arguments;
        Ok(delta)
    }

    fn ensure_text_block(&mut self) -> usize {
        if let Some(index) = self.text_block {
            return index;
        }
        self.output
            .content
            .push(AssistantContentBlock::Text(TextContent::new("")));
        let index = self.output.content.len() - 1;
        self.text_block = Some(index);
        self.push(AssistantMessageEvent::TextStart {
            content_index: index,
            partial: self.partial(),
        });
        index
    }

    fn ensure_thinking_block(&mut self, thinking_signature: &str) -> usize {
        if let Some(index) = self.thinking_block {
            return index;
        }
        self.output
            .content
            .push(AssistantContentBlock::Thinking(ThinkingContent {
                thinking: String::new(),
                thinking_signature: Some(thinking_signature.to_owned()),
                redacted: None,
            }));
        let index = self.output.content.len() - 1;
        self.thinking_block = Some(index);
        self.push(AssistantMessageEvent::ThinkingStart {
            content_index: index,
            partial: self.partial(),
        });
        index
    }

    fn new_custom_input(&self, name: &str) -> CustomInput {
        // The "input" fallback should not be taken; it only stashes input
        // for a tool the model made up.
        CustomInput {
            property: self
                .grammar_tool_input_properties
                .get(name)
                .cloned()
                .unwrap_or_else(|| "input".to_owned()),
            json_buffer: GrammarToolInputJsonBuffer::default(),
        }
    }

    fn ensure_tool_call_block(&mut self, tool_call: &JsonValue) -> usize {
        let stream_index = stream_index_key(tool_call.get("index"));
        let function = tool_call.get("function").filter(|f| js_truthy(Some(f)));
        let custom = tool_call.get("custom").filter(|c| js_truthy(Some(c)));
        let id = tool_call
            .get("id")
            .and_then(JsonValue::as_str)
            .filter(|id| !id.is_empty());
        let name = function
            .and_then(|function| function.get("name"))
            .filter(|name| !name.is_null())
            .or_else(|| custom.and_then(|custom| custom.get("name")))
            .and_then(JsonValue::as_str)
            .unwrap_or_default()
            .to_owned();
        let is_custom = custom.is_some() && function.is_none();

        let mut block = stream_index.and_then(|key| self.tool_blocks_by_index.get(&key).copied());
        if block.is_none() {
            block = id.and_then(|id| self.tool_blocks_by_id.get(id).copied());
        }
        let index = if let Some(index) = block {
            index
        } else {
            let custom_input = is_custom.then(|| self.new_custom_input(&name));
            let mut arguments = JsonObject::new();
            if let Some(custom_input) = &custom_input {
                arguments.insert(
                    custom_input.property.clone(),
                    JsonValue::String(String::new()),
                );
            }
            self.output
                .content
                .push(AssistantContentBlock::ToolCall(ToolCall {
                    id: id.unwrap_or_default().to_owned(),
                    name: name.clone(),
                    arguments,
                    thought_signature: None,
                    namespace: None,
                }));
            let index = self.output.content.len() - 1;
            self.scratch.insert(
                index,
                ToolScratch {
                    partial_args: custom_input.is_none().then(String::new),
                    custom_input,
                    stream_index,
                },
            );
            if let Some(key) = stream_index {
                self.tool_blocks_by_index.insert(key, index);
            }
            if let Some(id) = id {
                self.tool_blocks_by_id.insert(id.to_owned(), index);
            }
            self.push(AssistantMessageEvent::ToolCallStart {
                content_index: index,
                partial: self.partial(),
            });
            index
        };

        if let Some(key) = stream_index {
            let scratch = self.scratch.entry(index).or_default();
            if scratch.stream_index.is_none() {
                scratch.stream_index = Some(key);
                self.tool_blocks_by_index.insert(key, index);
            }
        }
        if let Some(id) = id {
            self.tool_blocks_by_id.insert(id.to_owned(), index);
        }
        if self.tool_call(index).name.is_empty() && !name.is_empty() {
            self.tool_call(index).name.clone_from(&name);
        }
        let has_custom_input = self
            .scratch
            .get(&index)
            .is_some_and(|scratch| scratch.custom_input.is_some());
        if is_custom && !has_custom_input {
            let block_name = self.tool_call(index).name.clone();
            let custom_input = self.new_custom_input(&block_name);
            let mut arguments = JsonObject::new();
            arguments.insert(
                custom_input.property.clone(),
                JsonValue::String(String::new()),
            );
            self.tool_call(index).arguments = arguments;
            let scratch = self.scratch.entry(index).or_default();
            scratch.custom_input = Some(custom_input);
            scratch.partial_args = None;
        }
        index
    }

    /// One parsed chunk of the provider stream.
    ///
    /// # Errors
    ///
    /// Grammar tool input that changed non-monotonically.
    // One linear body mirroring the TS chunk loop.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn handle_chunk(&mut self, chunk: &JsonValue) -> Result<(), Thrown> {
        let Some(chunk) = chunk.as_object() else {
            return Ok(());
        };

        // Each chunk of a streamed completion carries the same id.
        if self.output.response_id.as_deref().is_none_or(str::is_empty) {
            if let Some(id) = chunk.get("id").and_then(JsonValue::as_str) {
                self.output.response_id = Some(id.to_owned());
            }
        }
        if let Some(chunk_model) = chunk.get("model").and_then(JsonValue::as_str) {
            if !chunk_model.is_empty()
                && chunk_model != self.model.id
                && self
                    .output
                    .response_model
                    .as_deref()
                    .is_none_or(str::is_empty)
            {
                self.output.response_model = Some(chunk_model.to_owned());
            }
        }
        // eukhe addition: remember the tier that served the request.
        if let Some(service_tier) = chunk.get("service_tier").and_then(JsonValue::as_str) {
            self.response_service_tier = Some(service_tier.to_owned());
        }
        let chunk_usage = chunk.get("usage").filter(|usage| js_truthy(Some(usage)));
        if let Some(usage) = chunk_usage {
            self.output.usage = parse_chunk_usage(usage, self.model);
        }

        let Some(choice) = chunk
            .get("choices")
            .and_then(JsonValue::as_array)
            .and_then(|choices| choices.first())
            .filter(|choice| js_truthy(Some(choice)))
        else {
            return Ok(());
        };

        // Fallback: some providers (e.g., Moonshot) return usage in
        // choice.usage instead of the standard chunk.usage.
        if chunk_usage.is_none() {
            if let Some(usage) = choice.get("usage").filter(|usage| js_truthy(Some(usage))) {
                self.output.usage = parse_chunk_usage(usage, self.model);
            }
        }

        if let Some(finish_reason) = choice
            .get("finish_reason")
            .and_then(JsonValue::as_str)
            .filter(|reason| !reason.is_empty())
        {
            self.output.raw_stop_reason = Some(finish_reason.to_owned());
            let (stop_reason, error_message) = map_stop_reason(finish_reason);
            self.output.stop_reason = stop_reason;
            if let Some(error_message) = error_message {
                self.output.error_message = Some(error_message);
            }
            self.has_finish_reason = true;
        }

        let Some(delta) = choice.get("delta").filter(|delta| js_truthy(Some(delta))) else {
            return Ok(());
        };

        if let Some(content) = delta
            .get("content")
            .and_then(JsonValue::as_str)
            .filter(|content| !content.is_empty())
        {
            let index = self.ensure_text_block();
            if let AssistantContentBlock::Text(text) = &mut self.output.content[index] {
                text.text.push_str(content);
            }
            self.push(AssistantMessageEvent::TextDelta {
                content_index: index,
                delta: content.to_owned(),
                partial: self.partial(),
            });
        }

        // Some endpoints return reasoning in reasoning_content (llama.cpp) or
        // reasoning; use the first non-empty field to avoid duplication.
        let reasoning = ["reasoning_content", "reasoning", "reasoning_text"]
            .into_iter()
            .find_map(|field| {
                delta
                    .get(field)
                    .and_then(JsonValue::as_str)
                    .filter(|value| !value.is_empty())
                    .map(|value| (field, value))
            });
        if let Some((field, reasoning_delta)) = reasoning {
            let thinking_signature = if self.model.provider == "opencode-go" && field == "reasoning"
            {
                "reasoning_content"
            } else {
                field
            };
            let index = self.ensure_thinking_block(thinking_signature);
            if let AssistantContentBlock::Thinking(thinking) = &mut self.output.content[index] {
                thinking.thinking.push_str(reasoning_delta);
            }
            self.push(AssistantMessageEvent::ThinkingDelta {
                content_index: index,
                delta: reasoning_delta.to_owned(),
                partial: self.partial(),
            });
        }

        if let Some(tool_calls) = delta
            .get("tool_calls")
            .filter(|tool_calls| js_truthy(Some(tool_calls)))
            .and_then(JsonValue::as_array)
        {
            for tool_call in tool_calls {
                self.handle_tool_call_delta(tool_call)?;
            }
        }

        if let Some(reasoning_details) =
            delta.get("reasoning_details").and_then(JsonValue::as_array)
        {
            for detail in reasoning_details {
                if !is_openai_reasoning_detail(detail) {
                    continue;
                }
                self.ensure_thinking_block("");
                // Keep provider replay data in the signature slot. OpenRouter
                // streams reasoning_details as deltas: consecutive
                // text/summary deltas merge; encrypted entries stay discrete.
                append_openai_reasoning_detail(
                    self.streamed_reasoning_details.get_or_insert_with(Vec::new),
                    detail,
                );
            }
        }
        Ok(())
    }

    fn handle_tool_call_delta(&mut self, tool_call: &JsonValue) -> Result<(), Thrown> {
        let index = self.ensure_tool_call_block(tool_call);
        if let Some(id) = tool_call
            .get("id")
            .and_then(JsonValue::as_str)
            .filter(|id| !id.is_empty())
        {
            if self.tool_call(index).id.is_empty() {
                id.clone_into(&mut self.tool_call(index).id);
                self.tool_blocks_by_id.insert(id.to_owned(), index);
            }
        }
        let function = tool_call.get("function").filter(|f| js_truthy(Some(f)));
        let custom = tool_call.get("custom").filter(|c| js_truthy(Some(c)));
        let name = function
            .and_then(|function| function.get("name"))
            .filter(|name| !name.is_null())
            .or_else(|| custom.and_then(|custom| custom.get("name")))
            .and_then(JsonValue::as_str);
        if let Some(name) = name.filter(|name| !name.is_empty()) {
            if self.tool_call(index).name.is_empty() {
                name.clone_into(&mut self.tool_call(index).name);
            }
        }

        let mut delta = String::new();
        if let Some(arguments) = function
            .and_then(|function| function.get("arguments"))
            .and_then(JsonValue::as_str)
            .filter(|arguments| !arguments.is_empty())
        {
            arguments.clone_into(&mut delta);
            let scratch = self.scratch.entry(index).or_default();
            let partial_args = scratch.partial_args.get_or_insert_with(String::new);
            partial_args.push_str(arguments);
            let parsed = parse_streaming_json_object(Some(partial_args));
            self.tool_call(index).arguments = parsed;
        } else if let Some(input) = custom
            .and_then(|custom| custom.get("input"))
            .and_then(JsonValue::as_str)
            .filter(|input| !input.is_empty())
        {
            let next_input = self.custom_tool_call_input(index) + input;
            delta = self
                .append_custom_tool_call_input(index, &next_input, GrammarInputClose::KeepOpen)?
                .unwrap_or_default();
        }
        self.push(AssistantMessageEvent::ToolCallDelta {
            content_index: index,
            delta,
            partial: self.partial(),
        });
        Ok(())
    }

    /// TS `finishBlock` over every block, in order.
    ///
    /// # Errors
    ///
    /// Grammar tool input that changed after it was closed.
    pub(crate) fn finish_blocks(&mut self) -> Result<(), Thrown> {
        for index in 0..self.output.content.len() {
            match &self.output.content[index] {
                AssistantContentBlock::Text(text) => {
                    let content = text.text.clone();
                    self.push(AssistantMessageEvent::TextEnd {
                        content_index: index,
                        content,
                        partial: self.partial(),
                    });
                }
                AssistantContentBlock::Thinking(_) => {
                    self.apply_streamed_reasoning_details();
                    let AssistantContentBlock::Thinking(thinking) = &self.output.content[index]
                    else {
                        continue;
                    };
                    let content = thinking.thinking.clone();
                    self.push(AssistantMessageEvent::ThinkingEnd {
                        content_index: index,
                        content,
                        partial: self.partial(),
                    });
                }
                AssistantContentBlock::ToolCall(_) => {
                    let has_custom_input = self
                        .scratch
                        .get(&index)
                        .is_some_and(|scratch| scratch.custom_input.is_some());
                    if has_custom_input {
                        let input = self.custom_tool_call_input(index);
                        if let Some(delta) = self.append_custom_tool_call_input(
                            index,
                            &input,
                            GrammarInputClose::Close,
                        )? {
                            self.push(AssistantMessageEvent::ToolCallDelta {
                                content_index: index,
                                delta,
                                partial: self.partial(),
                            });
                        }
                    } else {
                        let partial_args = self
                            .scratch
                            .get(&index)
                            .and_then(|scratch| scratch.partial_args.clone());
                        self.tool_call(index).arguments =
                            parse_streaming_json_object(partial_args.as_deref());
                    }
                    // Finalize in place and drop the scratch buffers so
                    // replay only carries parsed arguments.
                    self.scratch.remove(&index);
                    let tool_call = self.tool_call(index).clone();
                    self.push(AssistantMessageEvent::ToolCallEnd {
                        content_index: index,
                        tool_call,
                        partial: self.partial(),
                    });
                }
            }
        }
        Ok(())
    }
}
