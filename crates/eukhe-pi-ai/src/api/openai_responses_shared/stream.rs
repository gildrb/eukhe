//! TS `processResponsesStream`: folds `OpenAI` Responses stream events into
//! the assistant message and emits the normalized events.
//!
//! The TS streaming scratch fields of a tool-call block (`partialJson`,
//! `customInput`) are kept beside the message, keyed by content index, so
//! the blocks never carry them; a block is unfinished while it has scratch.

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use futures::{Stream, StreamExt};
use serde_json::json;

use super::{GrammarToolInputProperties, JsonObject};
use crate::api::constrained_sampling::{
    append_grammar_tool_input_json_delta, GrammarInputClose, GrammarToolInputJsonBuffer,
};
use crate::models::calculate_cost;
use crate::types::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, JsonValue, Model,
    OnProviderStreamEvent, StopReason, TextContent, ThinkingContent, ToolCall, Usage, UsageCost,
};
use crate::utils::diagnostics::{ErrorObject, Thrown};
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::js::{js_to_string, json_stringify};
use crate::utils::json_parse::{json_parse, parse_streaming_json_object};

/// TS `resolveServiceTier(responseServiceTier, requestServiceTier)`.
pub type ResolveServiceTierFn =
    Arc<dyn Fn(Option<&str>, Option<&str>) -> Option<String> + Send + Sync>;

/// TS `applyServiceTierPricing(usage, serviceTier)`.
pub type ApplyServiceTierPricingFn = Arc<dyn Fn(&mut Usage, Option<&str>) + Send + Sync>;

/// TS `OpenAIResponsesStreamOptions`.
#[derive(Clone, Default)]
pub struct OpenAIResponsesStreamOptions {
    pub on_provider_stream_event: Option<OnProviderStreamEvent>,
    /// The requested `service_tier` wire value.
    pub service_tier: Option<String>,
    pub grammar_tool_input_properties: Option<GrammarToolInputProperties>,
    pub resolve_service_tier: Option<ResolveServiceTierFn>,
    pub apply_service_tier_pricing: Option<ApplyServiceTierPricingFn>,
}

impl fmt::Debug for OpenAIResponsesStreamOptions {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("OpenAIResponsesStreamOptions")
            .field(
                "on_provider_stream_event",
                &self
                    .on_provider_stream_event
                    .as_ref()
                    .map(|_| "OnProviderStreamEvent"),
            )
            .field("service_tier", &self.service_tier)
            .field(
                "grammar_tool_input_properties",
                &self.grammar_tool_input_properties,
            )
            .field(
                "resolve_service_tier",
                &self
                    .resolve_service_tier
                    .as_ref()
                    .map(|_| "ResolveServiceTierFn"),
            )
            .field(
                "apply_service_tier_pricing",
                &self
                    .apply_service_tier_pricing
                    .as_ref()
                    .map(|_| "ApplyServiceTierPricingFn"),
            )
            .finish()
    }
}

/// `new Error(message)`.
fn error(message: impl Into<String>) -> Thrown {
    ErrorObject::new(message).thrown()
}

/// A JS template-literal interpolation of an optional JSON value.
fn template(value: Option<&JsonValue>) -> String {
    value.map_or_else(|| "undefined".to_owned(), js_to_string)
}

/// JS truthiness of an optional JSON value.
fn truthy(value: Option<&JsonValue>) -> bool {
    value.is_some_and(crate::api::openai_sdk::js_truthy)
}

/// `array?.map((x) => x[key]).join(sep)`: `undefined`/`null` join as "".
fn join_field(value: Option<&JsonValue>, key: &str, separator: &str) -> String {
    let Some(JsonValue::Array(items)) = value else {
        return String::new();
    };
    items
        .iter()
        .map(|item| match item.get(key) {
            None | Some(JsonValue::Null) => String::new(),
            Some(value) => js_to_string(value),
        })
        .collect::<Vec<_>>()
        .join(separator)
}

/// The output slot kinds of TS `ResponsesOutputSlot`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SlotKind {
    Thinking,
    Text,
    ToolCall,
}

#[derive(Debug, Clone, Copy)]
struct Slot {
    kind: SlotKind,
    content_index: usize,
}

/// TS `customInput` scratch of a grammar tool call.
#[derive(Debug, Clone)]
struct CustomInput {
    property: String,
    json_buffer: GrammarToolInputJsonBuffer,
}

/// The TS streaming scratch of one tool-call block.
#[derive(Debug, Clone, Default)]
struct ToolScratch {
    partial_json: Option<String>,
    custom_input: Option<CustomInput>,
}

/// A JS `Map` key for `event.output_index` (which may be absent).
fn slot_key(event: &JsonValue) -> String {
    event
        .get("output_index")
        .map_or_else(|| "undefined".to_owned(), json_stringify)
}

/// TS `encodeTextSignatureV1(id, phase)`: `{ v: 1, id, phase? }`.
fn encode_text_signature(id: Option<&JsonValue>, phase: Option<&JsonValue>) -> String {
    let mut payload = JsonObject::new();
    payload.insert("v".to_owned(), json!(1));
    if let Some(id) = id {
        payload.insert("id".to_owned(), id.clone());
    }
    if let Some(phase) = phase.filter(|phase| truthy(Some(phase))) {
        payload.insert("phase".to_owned(), phase.clone());
    }
    json_stringify(&JsonValue::Object(payload))
}

struct Processor<'a> {
    output: &'a mut AssistantMessage,
    stream: &'a AssistantMessageEventStream,
    model: &'a Model,
    options: &'a OpenAIResponsesStreamOptions,
    saw_terminal_response_event: bool,
    output_slots: HashMap<String, Slot>,
    reasoning_blocks_by_id: HashMap<String, usize>,
    scratch: HashMap<usize, ToolScratch>,
}

impl Processor<'_> {
    fn partial(&self) -> AssistantMessage {
        self.output.clone()
    }

    fn apply_message_phase_stop_reason(&mut self, item: &JsonValue) {
        if item.get("type").and_then(JsonValue::as_str) == Some("message")
            && item.get("phase").and_then(JsonValue::as_str) == Some("final_answer")
        {
            self.output.stop_reason = StopReason::Stop;
        }
    }

    fn get_slot(&self, key: &str, kind: SlotKind) -> Option<Slot> {
        self.output_slots
            .get(key)
            .copied()
            .filter(|slot| slot.kind == kind)
    }

    fn push_tool_call_delta(&self, slot: Slot, delta: Option<String>) {
        if let Some(delta) = delta {
            self.stream.push(AssistantMessageEvent::ToolCallDelta {
                content_index: slot.content_index,
                delta,
                partial: self.partial(),
            });
        }
    }

    fn thinking_mut(&mut self, index: usize) -> Option<&mut ThinkingContent> {
        match self.output.content.get_mut(index) {
            Some(AssistantContentBlock::Thinking(block)) => Some(block),
            _ => None,
        }
    }

    fn text_mut(&mut self, index: usize) -> Option<&mut TextContent> {
        match self.output.content.get_mut(index) {
            Some(AssistantContentBlock::Text(block)) => Some(block),
            _ => None,
        }
    }

    fn tool_call_mut(&mut self, index: usize) -> Option<&mut ToolCall> {
        match self.output.content.get_mut(index) {
            Some(AssistantContentBlock::ToolCall(block)) => Some(block),
            _ => None,
        }
    }

    fn tool_call(&self, index: usize) -> Option<&ToolCall> {
        match self.output.content.get(index) {
            Some(AssistantContentBlock::ToolCall(block)) => Some(block),
            _ => None,
        }
    }

    fn push_block(&mut self, key: String, kind: SlotKind, block: AssistantContentBlock) -> Slot {
        self.output.content.push(block);
        let slot = Slot {
            kind,
            content_index: self.output.content.len() - 1,
        };
        self.output_slots.insert(key, slot);
        slot
    }

    #[allow(clippy::too_many_lines)] // One TS closure; arms mirror the TS item types.
    fn create_slot(&mut self, key: String, item: &JsonValue) -> Option<Slot> {
        let item_type = item.get("type").and_then(JsonValue::as_str);
        match item_type {
            Some("reasoning") => {
                let slot = self.push_block(
                    key,
                    SlotKind::Thinking,
                    AssistantContentBlock::Thinking(ThinkingContent::default()),
                );
                self.stream.push(AssistantMessageEvent::ThinkingStart {
                    content_index: slot.content_index,
                    partial: self.partial(),
                });
                Some(slot)
            }
            Some("message") => {
                self.apply_message_phase_stop_reason(item);
                let slot = self.push_block(
                    key,
                    SlotKind::Text,
                    AssistantContentBlock::Text(TextContent::new("")),
                );
                self.stream.push(AssistantMessageEvent::TextStart {
                    content_index: slot.content_index,
                    partial: self.partial(),
                });
                Some(slot)
            }
            Some("function_call") => {
                let partial_json = match item.get("arguments") {
                    Some(value) if truthy(Some(value)) => js_to_string(value),
                    _ => String::new(),
                };
                let block = ToolCall {
                    id: format!(
                        "{}|{}",
                        template(item.get("call_id")),
                        template(item.get("id"))
                    ),
                    name: template(item.get("name")),
                    arguments: JsonObject::new(),
                    thought_signature: None,
                    namespace: item
                        .get("namespace")
                        .and_then(JsonValue::as_str)
                        .map(str::to_owned),
                };
                let slot = self.push_block(
                    key,
                    SlotKind::ToolCall,
                    AssistantContentBlock::ToolCall(block),
                );
                self.scratch.insert(
                    slot.content_index,
                    ToolScratch {
                        partial_json: Some(partial_json),
                        custom_input: None,
                    },
                );
                self.stream.push(AssistantMessageEvent::ToolCallStart {
                    content_index: slot.content_index,
                    partial: self.partial(),
                });
                Some(slot)
            }
            Some("custom_tool_call") => {
                let name = template(item.get("name"));
                let input_property = self
                    .options
                    .grammar_tool_input_properties
                    .as_ref()
                    .and_then(|grammar| grammar.get(&name))
                    .cloned()
                    .unwrap_or_else(|| "input".to_owned());
                let input = match item.get("input") {
                    Some(value) if truthy(Some(value)) => value.clone(),
                    _ => json!(""),
                };
                let mut arguments = JsonObject::new();
                arguments.insert(input_property.clone(), input);
                let block = ToolCall {
                    id: format!(
                        "{}|{}",
                        template(item.get("call_id")),
                        template(item.get("id"))
                    ),
                    name,
                    arguments,
                    thought_signature: None,
                    namespace: item
                        .get("namespace")
                        .and_then(JsonValue::as_str)
                        .map(str::to_owned),
                };
                let slot = self.push_block(
                    key,
                    SlotKind::ToolCall,
                    AssistantContentBlock::ToolCall(block),
                );
                self.scratch.insert(
                    slot.content_index,
                    ToolScratch {
                        partial_json: None,
                        custom_input: Some(CustomInput {
                            property: input_property,
                            json_buffer: GrammarToolInputJsonBuffer::default(),
                        }),
                    },
                );
                self.stream.push(AssistantMessageEvent::ToolCallStart {
                    content_index: slot.content_index,
                    partial: self.partial(),
                });
                Some(slot)
            }
            _ => None,
        }
    }

    /// TS `getCustomToolCallInput`.
    fn custom_tool_call_input(&self, index: usize) -> String {
        let Some(property) = self
            .scratch
            .get(&index)
            .and_then(|scratch| scratch.custom_input.as_ref())
            .map(|custom| custom.property.clone())
        else {
            return String::new();
        };
        match self
            .tool_call(index)
            .and_then(|block| block.arguments.get(&property))
        {
            Some(JsonValue::String(text)) => text.clone(),
            _ => String::new(),
        }
    }

    /// TS `appendCustomToolCallInput`.
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
        )?;
        let property = custom.property.clone();
        if let Some(block) = self.tool_call_mut(index) {
            let mut arguments = JsonObject::new();
            arguments.insert(property, JsonValue::String(next_input.to_owned()));
            block.arguments = arguments;
        }
        Ok(delta)
    }

    fn has_custom_input(&self, index: usize) -> bool {
        self.scratch
            .get(&index)
            .is_some_and(|scratch| scratch.custom_input.is_some())
    }

    fn partial_json(&self, index: usize) -> Option<&String> {
        self.scratch
            .get(&index)
            .and_then(|scratch| scratch.partial_json.as_ref())
    }

    /// TS `backfillReasoningSignatures`.
    fn backfill_reasoning_signatures(
        &mut self,
        response_output: &[JsonValue],
    ) -> Result<(), Thrown> {
        for item in response_output {
            if item.get("type").and_then(JsonValue::as_str) != Some("reasoning")
                || !truthy(item.get("encrypted_content"))
            {
                continue;
            }
            let Some(index) = self
                .reasoning_blocks_by_id
                .get(&template(item.get("id")))
                .copied()
            else {
                continue;
            };
            let Some(block) = self.thinking_mut(index) else {
                continue;
            };
            let Some(signature) = block
                .thinking_signature
                .as_deref()
                .filter(|signature| !signature.is_empty())
            else {
                continue;
            };
            let stored = json_parse(signature)
                .map_err(|error| ErrorObject::named("SyntaxError", error.message).thrown())?;
            if truthy(stored.get("encrypted_content")) {
                continue;
            }
            let mut merged = match stored {
                JsonValue::Object(object) => object,
                _ => JsonObject::new(),
            };
            merged.insert(
                "encrypted_content".to_owned(),
                item.get("encrypted_content").cloned().unwrap_or_default(),
            );
            block.thinking_signature = Some(json_stringify(&JsonValue::Object(merged)));
        }
        Ok(())
    }

    /// TS `finalizeResponse`.
    fn finalize_response(&mut self, response: Option<&JsonValue>) -> Result<(), Thrown> {
        self.saw_terminal_response_event = true;
        let Some(response) = response.filter(|response| !response.is_null()) else {
            return Err(ErrorObject::named(
                "TypeError",
                format!(
                    "Cannot read properties of {} (reading 'output')",
                    if response.is_some() {
                        "null"
                    } else {
                        "undefined"
                    }
                ),
            )
            .thrown());
        };
        let response_output = match response.get("output") {
            Some(JsonValue::Array(items)) => items.clone(),
            _ => Vec::new(),
        };
        self.backfill_reasoning_signatures(&response_output)?;
        if let Some(id) = response.get("id").filter(|id| truthy(Some(id))) {
            self.output.response_id = Some(js_to_string(id));
        }
        if let Some(usage) = response.get("usage").filter(|usage| truthy(Some(usage))) {
            let number = |value: Option<&JsonValue>| -> f64 {
                value.and_then(JsonValue::as_f64).unwrap_or(0.0)
            };
            let input_details = usage.get("input_tokens_details");
            let cached_tokens =
                number(input_details.and_then(|details| details.get("cached_tokens")));
            let cache_write_tokens =
                number(input_details.and_then(|details| details.get("cache_write_tokens")));
            // OpenAI includes cached and cache-write tokens in input_tokens, so subtract both.
            let input =
                (number(usage.get("input_tokens")) - cached_tokens - cache_write_tokens).max(0.0);
            self.output.usage = Usage {
                input: to_count(input),
                output: to_count(number(usage.get("output_tokens"))),
                cache_read: to_count(cached_tokens),
                cache_write: to_count(cache_write_tokens),
                cache_write_1h: None,
                reasoning: Some(to_count(number(
                    usage
                        .get("output_tokens_details")
                        .and_then(|details| details.get("reasoning_tokens")),
                ))),
                total_tokens: to_count(number(usage.get("total_tokens"))),
                cost: UsageCost::default(),
            };
        }
        calculate_cost(self.model, &mut self.output.usage);
        if let Some(apply) = &self.options.apply_service_tier_pricing {
            let response_tier = response.get("service_tier").and_then(JsonValue::as_str);
            let request_tier = self.options.service_tier.as_deref();
            let service_tier = match &self.options.resolve_service_tier {
                Some(resolve) => resolve(response_tier, request_tier),
                None => response_tier.or(request_tier).map(str::to_owned),
            };
            apply(&mut self.output.usage, service_tier.as_deref());
        }
        // Map status to stop reason. For incomplete responses, retain the
        // provider's specific reason so max-output truncation and content
        // filtering stay distinct.
        let status = response.get("status").and_then(JsonValue::as_str);
        let incomplete_reason = response
            .get("incomplete_details")
            .and_then(|details| details.get("reason"))
            .and_then(JsonValue::as_str);
        self.output.raw_stop_reason = match (status, incomplete_reason) {
            (_, Some(reason)) if !reason.is_empty() => {
                Some(format!("{}.{reason}", status.unwrap_or("undefined")))
            }
            (status, _) => status.map(str::to_owned),
        };
        let mapped = map_stop_reason(
            status,
            incomplete_reason.filter(|reason| !reason.is_empty()),
        )?;
        self.output.stop_reason = mapped.stop_reason;
        self.output.error_message = mapped.error_message;
        if self.output.stop_reason == StopReason::Stop
            && self
                .output
                .content
                .iter()
                .any(|block| matches!(block, AssistantContentBlock::ToolCall(_)))
        {
            self.output.stop_reason = StopReason::ToolUse;
        }
        Ok(())
    }

    fn push_thinking_delta(&mut self, key: &str, delta: String) {
        let Some(slot) = self.get_slot(key, SlotKind::Thinking) else {
            return;
        };
        if let Some(block) = self.thinking_mut(slot.content_index) {
            block.thinking.push_str(&delta);
        }
        self.stream.push(AssistantMessageEvent::ThinkingDelta {
            content_index: slot.content_index,
            delta,
            partial: self.partial(),
        });
    }

    fn push_text_delta(&mut self, key: &str, delta: String) {
        let Some(slot) = self.get_slot(key, SlotKind::Text) else {
            return;
        };
        if let Some(block) = self.text_mut(slot.content_index) {
            block.text.push_str(&delta);
        }
        self.stream.push(AssistantMessageEvent::TextDelta {
            content_index: slot.content_index,
            delta,
            partial: self.partial(),
        });
    }

    #[allow(clippy::too_many_lines)] // One TS event dispatch; arms mirror the TS branches.
    fn handle_event(&mut self, event: &JsonValue) -> Result<(), Thrown> {
        let key = slot_key(event);
        match event.get("type").and_then(JsonValue::as_str) {
            Some("response.created") => {
                let id = event
                    .get("response")
                    .and_then(|response| response.get("id"));
                self.output.response_id = id.map(js_to_string);
            }
            Some("response.output_item.added") => {
                let item = event.get("item").cloned().unwrap_or_default();
                self.create_slot(key, &item);
            }
            Some("response.reasoning_summary_text.delta" | "response.reasoning_text.delta") => {
                self.push_thinking_delta(&key, template(event.get("delta")));
            }
            Some("response.reasoning_summary_part.done") => {
                self.push_thinking_delta(&key, "\n\n".to_owned());
            }
            Some("response.output_text.delta" | "response.refusal.delta") => {
                self.push_text_delta(&key, template(event.get("delta")));
            }
            Some("response.function_call_arguments.delta") => {
                let Some(slot) = self.get_slot(&key, SlotKind::ToolCall) else {
                    return Ok(());
                };
                let Some(partial_json) = self.partial_json(slot.content_index) else {
                    return Ok(());
                };
                let delta = template(event.get("delta"));
                let partial_json = format!("{partial_json}{delta}");
                let arguments = parse_streaming_json_object(Some(&partial_json));
                if let Some(scratch) = self.scratch.get_mut(&slot.content_index) {
                    scratch.partial_json = Some(partial_json);
                }
                if let Some(block) = self.tool_call_mut(slot.content_index) {
                    block.arguments = arguments;
                }
                self.push_tool_call_delta(slot, Some(delta));
            }
            Some("response.function_call_arguments.done") => {
                let Some(slot) = self.get_slot(&key, SlotKind::ToolCall) else {
                    return Ok(());
                };
                let Some(previous_partial_json) = self.partial_json(slot.content_index).cloned()
                else {
                    return Ok(());
                };
                let arguments_text = template(event.get("arguments"));
                let arguments = parse_streaming_json_object(Some(&arguments_text));
                if let Some(scratch) = self.scratch.get_mut(&slot.content_index) {
                    scratch.partial_json = Some(arguments_text.clone());
                }
                if let Some(block) = self.tool_call_mut(slot.content_index) {
                    block.arguments = arguments;
                }
                if let Some(delta) = arguments_text.strip_prefix(previous_partial_json.as_str()) {
                    if !delta.is_empty() {
                        self.push_tool_call_delta(slot, Some(delta.to_owned()));
                    }
                }
            }
            Some("response.custom_tool_call_input.delta") => {
                let Some(slot) = self.get_slot(&key, SlotKind::ToolCall) else {
                    return Ok(());
                };
                if !self.has_custom_input(slot.content_index) {
                    return Ok(());
                }
                let next_input = format!(
                    "{}{}",
                    self.custom_tool_call_input(slot.content_index),
                    template(event.get("delta"))
                );
                let delta = self.append_custom_tool_call_input(
                    slot.content_index,
                    &next_input,
                    GrammarInputClose::KeepOpen,
                )?;
                self.push_tool_call_delta(slot, delta);
            }
            Some("response.custom_tool_call_input.done") => {
                let Some(slot) = self.get_slot(&key, SlotKind::ToolCall) else {
                    return Ok(());
                };
                if !self.has_custom_input(slot.content_index) {
                    return Ok(());
                }
                let input = template(event.get("input"));
                let delta = self.append_custom_tool_call_input(
                    slot.content_index,
                    &input,
                    GrammarInputClose::Close,
                )?;
                self.push_tool_call_delta(slot, delta);
            }
            Some("response.output_item.done") => {
                let item = event.get("item").cloned().unwrap_or_default();
                self.handle_output_item_done(&key, &item)?;
            }
            Some("response.completed" | "response.incomplete") => {
                self.finalize_response(event.get("response"))?;
            }
            Some("error") => {
                return Err(error(format!(
                    "Error Code {}: {}",
                    template(event.get("code")),
                    template(event.get("message"))
                )));
            }
            Some("response.failed") => {
                self.saw_terminal_response_event = true;
                let response = event.get("response");
                self.output.raw_stop_reason = response
                    .and_then(|response| response.get("status"))
                    .filter(|status| !status.is_null())
                    .map(js_to_string);
                let response_error = response.and_then(|response| response.get("error"));
                let details = response.and_then(|response| response.get("incomplete_details"));
                let details_reason = details.and_then(|details| details.get("reason"));
                let message = if truthy(response_error) {
                    let code = response_error
                        .and_then(|error| error.get("code"))
                        .filter(|code| truthy(Some(code)))
                        .map_or_else(|| "unknown".to_owned(), js_to_string);
                    let message = response_error
                        .and_then(|error| error.get("message"))
                        .filter(|message| truthy(Some(message)))
                        .map_or_else(|| "no message".to_owned(), js_to_string);
                    format!("{code}: {message}")
                } else if truthy(details_reason) {
                    format!("incomplete: {}", template(details_reason))
                } else {
                    "Unknown error (no error details in response)".to_owned()
                };
                return Err(error(message));
            }
            _ => {}
        }
        Ok(())
    }

    #[allow(clippy::too_many_lines)] // One TS branch; arms mirror the TS item types.
    fn handle_output_item_done(&mut self, key: &str, item: &JsonValue) -> Result<(), Thrown> {
        self.apply_message_phase_stop_reason(item);
        let slot = match self.output_slots.get(key).copied() {
            Some(slot) => Some(slot),
            None => self.create_slot(key.to_owned(), item),
        };
        let item_type = item.get("type").and_then(JsonValue::as_str);
        match (item_type, slot) {
            (Some("reasoning"), Some(slot)) if slot.kind == SlotKind::Thinking => {
                let summary_text = join_field(item.get("summary"), "text", "\n\n");
                let content_text = join_field(item.get("content"), "text", "\n\n");
                let signature = json_stringify(item);
                let thinking = {
                    let Some(block) = self.thinking_mut(slot.content_index) else {
                        return Ok(());
                    };
                    if !summary_text.is_empty() {
                        block.thinking = summary_text;
                    } else if !content_text.is_empty() {
                        block.thinking = content_text;
                    }
                    block.thinking_signature = Some(signature);
                    block.thinking.clone()
                };
                self.reasoning_blocks_by_id
                    .insert(template(item.get("id")), slot.content_index);
                self.stream.push(AssistantMessageEvent::ThinkingEnd {
                    content_index: slot.content_index,
                    content: thinking,
                    partial: self.partial(),
                });
                self.output_slots.remove(key);
            }
            (Some("message"), Some(slot)) if slot.kind == SlotKind::Text => {
                let text = match item.get("content") {
                    Some(JsonValue::Array(parts)) => parts
                        .iter()
                        .map(|part| {
                            let field = if part.get("type").and_then(JsonValue::as_str)
                                == Some("output_text")
                            {
                                "text"
                            } else {
                                "refusal"
                            };
                            match part.get(field) {
                                None | Some(JsonValue::Null) => String::new(),
                                Some(value) => js_to_string(value),
                            }
                        })
                        .collect::<String>(),
                    _ => String::new(),
                };
                let phase = item.get("phase").filter(|phase| !phase.is_null());
                let signature = encode_text_signature(item.get("id"), phase);
                let Some(block) = self.text_mut(slot.content_index) else {
                    return Ok(());
                };
                block.text.clone_from(&text);
                block.text_signature = Some(signature);
                self.stream.push(AssistantMessageEvent::TextEnd {
                    content_index: slot.content_index,
                    content: text,
                    partial: self.partial(),
                });
                self.output_slots.remove(key);
            }
            (Some("function_call"), Some(slot))
                if slot.kind == SlotKind::ToolCall
                    && self.partial_json(slot.content_index).is_some() =>
            {
                let source = match item.get("arguments") {
                    Some(value) if truthy(Some(value)) => js_to_string(value),
                    _ => match self.partial_json(slot.content_index) {
                        Some(partial) if !partial.is_empty() => partial.clone(),
                        _ => "{}".to_owned(),
                    },
                };
                let arguments = parse_streaming_json_object(Some(&source));
                let namespace = item.get("namespace").and_then(JsonValue::as_str);
                // Finalize in place and strip the scratch buffer so replay
                // only carries parsed arguments.
                self.scratch.remove(&slot.content_index);
                let Some(block) = self.tool_call_mut(slot.content_index) else {
                    return Ok(());
                };
                block.arguments = arguments;
                if let Some(namespace) = namespace {
                    block.namespace = Some(namespace.to_owned());
                }
                let tool_call = block.clone();
                self.stream.push(AssistantMessageEvent::ToolCallEnd {
                    content_index: slot.content_index,
                    tool_call,
                    partial: self.partial(),
                });
                self.output_slots.remove(key);
            }
            (Some("custom_tool_call"), Some(slot))
                if slot.kind == SlotKind::ToolCall && self.has_custom_input(slot.content_index) =>
            {
                let input = match item.get("input") {
                    None | Some(JsonValue::Null) => self.custom_tool_call_input(slot.content_index),
                    Some(value) => js_to_string(value),
                };
                let delta = self.append_custom_tool_call_input(
                    slot.content_index,
                    &input,
                    GrammarInputClose::Close,
                )?;
                self.push_tool_call_delta(slot, delta);
                let namespace = item.get("namespace").and_then(JsonValue::as_str);
                self.scratch.remove(&slot.content_index);
                let Some(block) = self.tool_call_mut(slot.content_index) else {
                    return Ok(());
                };
                if let Some(namespace) = namespace {
                    block.namespace = Some(namespace.to_owned());
                }
                let tool_call = block.clone();
                self.stream.push(AssistantMessageEvent::ToolCallEnd {
                    content_index: slot.content_index,
                    tool_call,
                    partial: self.partial(),
                });
                self.output_slots.remove(key);
            }
            _ => {}
        }
        Ok(())
    }
}

/// A token count from a JS number (non-negative integers in practice).
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)] // Saturating JS-number → count.
fn to_count(value: f64) -> u64 {
    if value.is_finite() && value > 0.0 {
        value as u64
    } else {
        0
    }
}

struct MappedStop {
    stop_reason: StopReason,
    error_message: Option<String>,
}

/// TS `mapStopReason`.
fn map_stop_reason(
    status: Option<&str>,
    incomplete_reason: Option<&str>,
) -> Result<MappedStop, Thrown> {
    let stop = |stop_reason| MappedStop {
        stop_reason,
        error_message: None,
    };
    let Some(status) = status else {
        return Ok(stop(StopReason::Stop));
    };
    Ok(match status {
        // "in_progress" and "queued" are wonky ...
        "completed" | "in_progress" | "queued" => stop(StopReason::Stop),
        "incomplete" => {
            if incomplete_reason == Some("max_output_tokens") {
                stop(StopReason::Length)
            } else {
                MappedStop {
                    stop_reason: StopReason::Error,
                    error_message: Some(incomplete_reason.map_or_else(
                        || "Response incomplete without a provider reason".to_owned(),
                        |reason| format!("Response incomplete: {reason}"),
                    )),
                }
            }
        }
        "failed" | "cancelled" => stop(StopReason::Error),
        other => return Err(error(format!("Unhandled stop reason: {other}"))),
    })
}

/// TS `processResponsesStream`. Errors of `events` propagate unchanged.
///
/// # Errors
///
/// What TS throws: stream errors, `error` / `response.failed` events, a
/// stream without terminal response event, unfinished tool calls, callback
/// failures.
pub async fn process_responses_stream<S>(
    events: S,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
    model: &Model,
    options: &OpenAIResponsesStreamOptions,
) -> Result<(), Thrown>
where
    S: Stream<Item = Result<JsonValue, Thrown>> + Send,
{
    let mut processor = Processor {
        output,
        stream,
        model,
        options,
        saw_terminal_response_event: false,
        output_slots: HashMap::new(),
        reasoning_blocks_by_id: HashMap::new(),
        scratch: HashMap::new(),
    };
    let mut events = std::pin::pin!(events);
    while let Some(event) = events.next().await {
        let event = event?;
        if let Some(observer) = &options.on_provider_stream_event {
            observer(&event, model).await?;
        }
        processor.handle_event(&event)?;
    }
    if !processor.saw_terminal_response_event {
        return Err(error(
            "OpenAI Responses stream ended before a terminal response event",
        ));
    }
    // The agent runs every tool call in the final message. Refuse to hand over
    // calls whose output_item.done never arrived: their arguments may be cut
    // off or mixed up, e.g. when a non-compliant server omits output_index.
    // Finished calls have their scratch buffers removed.
    if processor.output.stop_reason == StopReason::ToolUse {
        for (index, block) in processor.output.content.iter().enumerate() {
            let AssistantContentBlock::ToolCall(tool_call) = block else {
                continue;
            };
            if processor.scratch.contains_key(&index) {
                return Err(error(format!(
                    "OpenAI Responses stream completed with an unfinished tool call: {} ({})",
                    tool_call.name, tool_call.id
                )));
            }
        }
    }
    Ok(())
}
