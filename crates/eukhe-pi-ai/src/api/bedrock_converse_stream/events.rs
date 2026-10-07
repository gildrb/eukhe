//! Converse stream event handling: content-block start/delta/stop, usage
//! metadata, and the streaming scratch state of each block. Section of the
//! port of `api/bedrock-converse-stream.ts`.

use base64::engine::general_purpose::STANDARD;
use base64::Engine as _;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, JsonObject, JsonValue, Model,
    TextContent, ThinkingContent, ToolCall,
};

use crate::models::calculate_cost;
use crate::utils::event_stream::AssistantMessageEventStream;
use crate::utils::js::js_to_string;
use crate::utils::json_parse::parse_streaming_json_object;

/// Matches the placeholder the Anthropic API path uses for redacted thinking.
pub(crate) const REDACTED_THINKING_PLACEHOLDER: &str = "[Reasoning redacted]";

/// The streaming scratch fields TS keeps on each content block (TS `Block`):
/// the provider block index, the tool-call `partialJson` buffer, and the
/// encrypted reasoning chunks. Never part of the persisted message.
#[derive(Debug, Default)]
struct BlockScratch {
    /// `block.index`; `None` once deleted (or created from an absent index).
    index: Option<JsonValue>,
    partial_json: Option<String>,
    redacted_chunks: Option<Vec<Vec<u8>>>,
}

/// The scratch state parallel to `output.content`.
#[derive(Debug, Default)]
pub(crate) struct StreamBlocks {
    scratch: Vec<BlockScratch>,
}

/// JS `===` between two optional JSON values (`undefined` when `None`).
fn strict_equals(left: Option<&JsonValue>, right: Option<&JsonValue>) -> bool {
    match (left, right) {
        (None, None) | (Some(JsonValue::Null), Some(JsonValue::Null)) => true,
        (Some(JsonValue::Number(left)), Some(JsonValue::Number(right))) => {
            left.as_f64() == right.as_f64()
        }
        (Some(JsonValue::String(left)), Some(JsonValue::String(right))) => left == right,
        (Some(JsonValue::Bool(left)), Some(JsonValue::Bool(right))) => left == right,
        _ => false,
    }
}

/// JS truthiness.
fn truthy(value: Option<&JsonValue>) -> bool {
    match value {
        None | Some(JsonValue::Null) => false,
        Some(JsonValue::Bool(flag)) => *flag,
        Some(JsonValue::Number(number)) => number.as_f64().is_some_and(|n| n != 0.0),
        Some(JsonValue::String(text)) => !text.is_empty(),
        Some(JsonValue::Array(_) | JsonValue::Object(_)) => true,
    }
}

/// JS `value || ""` for a string-typed member.
fn string_or_empty(value: Option<&JsonValue>) -> String {
    if truthy(value) {
        value.map(js_to_string).unwrap_or_default()
    } else {
        String::new()
    }
}

/// JS `value || 0` for a token count.
// Token counts are integral JS numbers far below 2^53.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn count_or_zero(value: Option<&JsonValue>) -> u64 {
    value
        .and_then(|value| {
            value.as_u64().or_else(|| {
                value
                    .as_f64()
                    .filter(|n| n.is_finite() && *n > 0.0)
                    .map(|n| n as u64)
            })
        })
        .unwrap_or(0)
}

/// The blob bytes of a validated base64 member (the SDK's `Uint8Array`).
fn blob_bytes(value: Option<&JsonValue>) -> Vec<u8> {
    value
        .and_then(JsonValue::as_str)
        .and_then(|text| STANDARD.decode(text).ok())
        .unwrap_or_default()
}

impl StreamBlocks {
    fn find(&self, index: Option<&JsonValue>) -> Option<usize> {
        self.scratch
            .iter()
            .position(|block| strict_equals(block.index.as_ref(), index))
    }

    fn push(
        &mut self,
        output: &mut AssistantMessage,
        block: AssistantContentBlock,
        scratch: BlockScratch,
    ) -> usize {
        output.content.push(block);
        self.scratch.push(scratch);
        output.content.len() - 1
    }

    /// TS `handleContentBlockStart`.
    pub(crate) fn handle_content_block_start(
        &mut self,
        event: &JsonObject,
        output: &mut AssistantMessage,
        stream: &AssistantMessageEventStream,
    ) {
        let index = event.get("contentBlockIndex");
        let Some(tool_use) = event
            .get("start")
            .and_then(|start| start.get("toolUse"))
            .filter(|tool_use| truthy(Some(tool_use)))
        else {
            return;
        };
        let content_index = self.push(
            output,
            AssistantContentBlock::ToolCall(ToolCall {
                id: string_or_empty(tool_use.get("toolUseId")),
                name: string_or_empty(tool_use.get("name")),
                arguments: JsonObject::new(),
                thought_signature: None,
                namespace: None,
            }),
            BlockScratch {
                index: index.cloned(),
                partial_json: Some(String::new()),
                redacted_chunks: None,
            },
        );
        stream.push(AssistantMessageEvent::ToolCallStart {
            content_index,
            partial: output.clone(),
        });
    }

    /// TS `handleContentBlockDelta`.
    // A 1:1 port of the TS handler's three delta branches.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn handle_content_block_delta(
        &mut self,
        event: &JsonObject,
        output: &mut AssistantMessage,
        stream: &AssistantMessageEventStream,
    ) {
        let content_block_index = event.get("contentBlockIndex");
        let delta = event.get("delta");
        let mut index = self.find(content_block_index);

        if let Some(text) = delta.and_then(|delta| delta.get("text")) {
            // No `contentBlockStart` is sent for text blocks.
            if index.is_none() {
                let content_index = self.push(
                    output,
                    AssistantContentBlock::Text(TextContent::new("")),
                    BlockScratch {
                        index: content_block_index.cloned(),
                        ..BlockScratch::default()
                    },
                );
                index = Some(content_index);
                stream.push(AssistantMessageEvent::TextStart {
                    content_index,
                    partial: output.clone(),
                });
            }
            if let Some(content_index) = index {
                if let AssistantContentBlock::Text(block) = &mut output.content[content_index] {
                    let text = js_to_string(text);
                    block.text.push_str(&text);
                    stream.push(AssistantMessageEvent::TextDelta {
                        content_index,
                        delta: text,
                        partial: output.clone(),
                    });
                }
            }
            return;
        }

        let tool_use = delta
            .and_then(|delta| delta.get("toolUse"))
            .filter(|tool_use| truthy(Some(tool_use)));
        if let (Some(tool_use), Some(content_index)) = (tool_use, index) {
            if matches!(
                output.content[content_index],
                AssistantContentBlock::ToolCall(_)
            ) {
                let input = string_or_empty(tool_use.get("input"));
                let scratch = &mut self.scratch[content_index];
                let partial_json = scratch.partial_json.get_or_insert_with(String::new);
                partial_json.push_str(&input);
                let arguments = parse_streaming_json_object(Some(partial_json));
                if let AssistantContentBlock::ToolCall(block) = &mut output.content[content_index] {
                    block.arguments = arguments;
                }
                stream.push(AssistantMessageEvent::ToolCallDelta {
                    content_index,
                    delta: input,
                    partial: output.clone(),
                });
                return;
            }
        }

        let Some(reasoning) = delta
            .and_then(|delta| delta.get("reasoningContent"))
            .filter(|reasoning| truthy(Some(reasoning)))
        else {
            return;
        };
        let thinking_index = if let Some(existing) = index {
            existing
        } else {
            let content_index = self.push(
                output,
                AssistantContentBlock::Thinking(ThinkingContent {
                    thinking: String::new(),
                    thinking_signature: Some(String::new()),
                    redacted: None,
                }),
                BlockScratch {
                    index: content_block_index.cloned(),
                    ..BlockScratch::default()
                },
            );
            stream.push(AssistantMessageEvent::ThinkingStart {
                content_index,
                partial: output.clone(),
            });
            content_index
        };
        if !matches!(
            output.content[thinking_index],
            AssistantContentBlock::Thinking(_)
        ) {
            return;
        }
        if truthy(reasoning.get("text")) {
            let text = string_or_empty(reasoning.get("text"));
            if let AssistantContentBlock::Thinking(block) = &mut output.content[thinking_index] {
                block.thinking.push_str(&text);
            }
            stream.push(AssistantMessageEvent::ThinkingDelta {
                content_index: thinking_index,
                delta: text,
                partial: output.clone(),
            });
        }
        // `thinkingSignature` holds either an Anthropic signature or an
        // opaque redacted payload, never both.
        if truthy(reasoning.get("signature")) {
            let signature = string_or_empty(reasoning.get("signature"));
            if let AssistantContentBlock::Thinking(block) = &mut output.content[thinking_index] {
                if block.redacted != Some(true) {
                    block
                        .thinking_signature
                        .get_or_insert_with(String::new)
                        .push_str(&signature);
                }
            }
        }
        let redacted = blob_bytes(reasoning.get("redactedContent"));
        if !redacted.is_empty() {
            // Encrypted reasoning from non-Anthropic models (e.g. OpenAI
            // GPT-5.6): kept verbatim and replayed on the next turn.
            let mut placeholder_added = false;
            if let AssistantContentBlock::Thinking(block) = &mut output.content[thinking_index] {
                if block.redacted != Some(true) {
                    block.redacted = Some(true);
                    block.thinking_signature = Some(String::new());
                    block.thinking.push_str(REDACTED_THINKING_PLACEHOLDER);
                    placeholder_added = true;
                }
            }
            if placeholder_added {
                stream.push(AssistantMessageEvent::ThinkingDelta {
                    content_index: thinking_index,
                    delta: REDACTED_THINKING_PLACEHOLDER.to_owned(),
                    partial: output.clone(),
                });
            }
            self.scratch[thinking_index]
                .redacted_chunks
                .get_or_insert_with(Vec::new)
                .push(redacted);
        }
    }

    /// TS `flushRedactedContent`: encodes the buffered encrypted reasoning
    /// into `thinkingSignature` and drops the buffer.
    fn flush_redacted_content(&mut self, output: &mut AssistantMessage, content_index: usize) {
        let Some(chunks) = self.scratch[content_index].redacted_chunks.take() else {
            return;
        };
        if let AssistantContentBlock::Thinking(block) = &mut output.content[content_index] {
            block.thinking_signature = Some(STANDARD.encode(chunks.concat()));
        }
    }

    /// TS `finalizeStreamingBlock` for every block: strips the scratch state.
    pub(crate) fn finalize(&mut self, output: &mut AssistantMessage) {
        for content_index in 0..self.scratch.len() {
            self.scratch[content_index].index = None;
            self.scratch[content_index].partial_json = None;
            self.flush_redacted_content(output, content_index);
        }
    }

    /// TS `handleContentBlockStop`.
    pub(crate) fn handle_content_block_stop(
        &mut self,
        event: &JsonObject,
        output: &mut AssistantMessage,
        stream: &AssistantMessageEventStream,
    ) {
        let Some(content_index) = self.find(event.get("contentBlockIndex")) else {
            return;
        };
        self.scratch[content_index].index = None;
        match &output.content[content_index] {
            AssistantContentBlock::Text(block) => {
                let content = block.text.clone();
                stream.push(AssistantMessageEvent::TextEnd {
                    content_index,
                    content,
                    partial: output.clone(),
                });
            }
            AssistantContentBlock::Thinking(_) => {
                self.flush_redacted_content(output, content_index);
                let AssistantContentBlock::Thinking(block) = &output.content[content_index] else {
                    return;
                };
                let content = block.thinking.clone();
                stream.push(AssistantMessageEvent::ThinkingEnd {
                    content_index,
                    content,
                    partial: output.clone(),
                });
            }
            AssistantContentBlock::ToolCall(_) => {
                // Finalize in place and strip the scratch buffer so replay only
                // carries parsed arguments.
                let partial_json = self.scratch[content_index].partial_json.take();
                let arguments = parse_streaming_json_object(partial_json.as_deref());
                let AssistantContentBlock::ToolCall(block) = &mut output.content[content_index]
                else {
                    return;
                };
                block.arguments = arguments;
                let tool_call = block.clone();
                stream.push(AssistantMessageEvent::ToolCallEnd {
                    content_index,
                    tool_call,
                    partial: output.clone(),
                });
            }
        }
    }
}

/// TS `handleMetadata`.
pub(crate) fn handle_metadata(event: &JsonObject, model: &Model, output: &mut AssistantMessage) {
    let Some(usage) = event.get("usage").filter(|usage| truthy(Some(usage))) else {
        return;
    };
    output.usage.input = count_or_zero(usage.get("inputTokens"));
    output.usage.output = count_or_zero(usage.get("outputTokens"));
    output.usage.cache_read = count_or_zero(usage.get("cacheReadInputTokens"));
    output.usage.cache_write = count_or_zero(usage.get("cacheWriteInputTokens"));
    output.usage.cache_write_1h =
        usage
            .get("cacheDetails")
            .and_then(JsonValue::as_array)
            .map(|details| {
                details
                    .iter()
                    .filter(|detail| detail.get("ttl").and_then(JsonValue::as_str) == Some("1h"))
                    .map(|detail| count_or_zero(detail.get("inputTokens")))
                    .sum()
            });
    let total = count_or_zero(usage.get("totalTokens"));
    output.usage.total_tokens = if total == 0 {
        output.usage.input + output.usage.output
    } else {
        total
    };
    calculate_cost(model, &mut output.usage);
}
