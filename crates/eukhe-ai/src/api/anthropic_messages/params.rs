//! Request construction: TS `getCacheControl`, `getBetaFeatures`,
//! `buildParams`, `convertMessages`, omp `planAnthropicEffortControls`,
//! `convertTools`, and the content/tool helpers they use.

use std::borrow::Borrow;
use std::collections::HashSet;

use eukhe_types::pi_ai::{
    AnthropicDisabledThinking, AssistantContentBlock, CacheRetention, JsonObject, JsonValue,
    Message, Model, ModelThinkingLevel, ProviderEnv, ThinkingLevel, Tool, ToolResultMessage,
    UserContent, UserContentBlock,
};
use serde_json::json;

use super::{
    billing, get_anthropic_compat, model_compat, AnthropicOptions, AnthropicToolChoice,
    CLAUDE_CODE_SYSTEM_PROMPT, CLAUDE_CODE_VERSION,
};
use crate::api::cache_breakpoints::{
    has_assistant_cache_breakpoint, has_cache_breakpoint, placed_marks,
};
use crate::api::constrained_sampling::{
    get_json_schema_tool_parameters, StrictPlan, StrictSupport, StrictToolParameters,
};
use crate::api::simple_options::thinking_budget_for_level;
use crate::api::tool_result_content::sent_blocks;
use crate::api::transform_messages::transform_messages;
use crate::models::{adaptive_thinking, thinking_level_map};
use crate::quirks::Quirks;
use crate::utils::diagnostics::Thrown;
use crate::utils::js::js_trim;
use crate::utils::provider_env::get_provider_env_value;
use crate::utils::sanitize_unicode::sanitize_surrogates;
use crate::utils::text::{render_system_message_update, split_system_prompt};
use crate::utils::transcript::{get_current_tools, get_initial_system_message};

const FINE_GRAINED_TOOL_STREAMING_BETA: &str = "fine-grained-tool-streaming-2025-05-14";
const INTERLEAVED_THINKING_BETA: &str = "interleaved-thinking-2025-05-14";
const SERVER_SIDE_FALLBACK_BETA: &str = "server-side-fallback-2026-07-01";
const MID_CONVERSATION_OUTPUT_CONFIG_BETA: &str = "mid-conversation-output-config-2026-07-01";
const THINKING_BINDING_CONTROLS_BETA: &str = "thinking-binding-controls-2026-08-01";
const INLINE_TOOLS_BETA: &str = "inline-tools-2026-09-15";

/// Claude Code 2.x tool names (canonical casing).
const CLAUDE_CODE_TOOLS: [&str; 17] = [
    "Read",
    "Write",
    "Edit",
    "Bash",
    "Grep",
    "Glob",
    "AskUserQuestion",
    "EnterPlanMode",
    "ExitPlanMode",
    "KillShell",
    "NotebookEdit",
    "Skill",
    "Task",
    "TaskOutput",
    "TodoWrite",
    "WebFetch",
    "WebSearch",
];

/// TS `toClaudeCodeName`: CC canonical casing when the name matches
/// case-insensitively.
pub(crate) fn to_claude_code_name(name: &str) -> String {
    let lower = name.to_lowercase();
    CLAUDE_CODE_TOOLS
        .iter()
        .find(|tool| tool.to_lowercase() == lower)
        .map_or_else(|| name.to_owned(), |tool| (*tool).to_owned())
}

/// TS `fromClaudeCodeName`.
pub(crate) fn from_claude_code_name(name: &str, tools: &[Tool]) -> String {
    let lower = name.to_lowercase();
    tools
        .iter()
        .find(|tool| tool.name.to_lowercase() == lower)
        .map_or_else(|| name.to_owned(), |tool| tool.name.clone())
}

/// TS `resolveCacheRetention`: defaults to short; `PI_CACHE_RETENTION=long`
/// for backward compatibility.
pub(crate) fn resolve_cache_retention(
    cache_retention: Option<CacheRetention>,
    env: Option<&ProviderEnv>,
) -> CacheRetention {
    if let Some(retention) = cache_retention {
        return retention;
    }
    if get_provider_env_value("PI_CACHE_RETENTION", env).as_deref() == Some("long") {
        return CacheRetention::Long;
    }
    CacheRetention::Short
}

/// TS `getCacheControl(...).cacheControl`.
fn get_cache_control(
    model: &Model,
    cache_retention: Option<CacheRetention>,
    env: Option<&ProviderEnv>,
) -> Option<JsonValue> {
    let retention = resolve_cache_retention(cache_retention, env);
    match retention {
        CacheRetention::None => None,
        CacheRetention::Long if get_anthropic_compat(model).supports_long_cache_retention => {
            Some(json!({ "type": "ephemeral", "ttl": "1h" }))
        }
        CacheRetention::Long | CacheRetention::Short => Some(json!({ "type": "ephemeral" })),
    }
}

/// TS `normalizeToolCallId`: Anthropic's id pattern and 64-char limit.
pub(crate) fn normalize_tool_call_id(id: &str) -> String {
    let replaced: String = id
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' || c == '-' {
                c
            } else {
                '_'
            }
        })
        .collect();
    // Non-ASCII chars became `_`, so code units equal chars here except for
    // astral chars, which JS replaces per surrogate (two `_`).
    let mut out = String::new();
    let mut units = 0usize;
    for (original, replaced) in id.chars().zip(replaced.chars()) {
        let width = original.len_utf16();
        for _ in 0..width {
            if units == 64 {
                return out;
            }
            out.push(replaced);
            units += 1;
        }
    }
    out
}

fn image_block(data: &str, mime_type: &str) -> JsonValue {
    json!({
        "type": "image",
        "source": { "type": "base64", "media_type": mime_type, "data": data },
    })
}

/// TS `convertContentBlocks`.
fn convert_content_blocks<B: Borrow<UserContentBlock>>(content: &[B]) -> JsonValue {
    let has_images = content
        .iter()
        .any(|block| matches!(block.borrow(), UserContentBlock::Image(_)));
    if !has_images {
        let text: Vec<&str> = content
            .iter()
            .map(|block| match block.borrow() {
                UserContentBlock::Text(text) => text.text.as_str(),
                UserContentBlock::Image(_) => "",
            })
            .collect();
        return JsonValue::String(sanitize_surrogates(&text.join("\n")).into_owned());
    }
    let mut blocks: Vec<JsonValue> = content
        .iter()
        .map(|block| match block.borrow() {
            UserContentBlock::Text(text) => {
                json!({ "type": "text", "text": sanitize_surrogates(&text.text) })
            }
            UserContentBlock::Image(image) => image_block(&image.data, &image.mime_type),
        })
        .collect();
    let has_text = content
        .iter()
        .any(|block| matches!(block.borrow(), UserContentBlock::Text(_)));
    if !has_text {
        blocks.insert(0, json!({ "type": "text", "text": "(see attached image)" }));
    }
    JsonValue::Array(blocks)
}

/// TS `convertToolResult`. eukhe addition: the blocks sent are the
/// compiled core's ([`sent_blocks`]): an error result's images go as text
/// lines, as Anthropic takes only text in a `tool_result` marked
/// `is_error` (a 400 otherwise, and the result stays in the transcript for
/// every later request).
fn convert_tool_result(message: &ToolResultMessage) -> JsonValue {
    json!({
        "type": "tool_result",
        "tool_use_id": message.tool_call_id,
        "content": convert_content_blocks(&sent_blocks(&message.content, message.is_error)),
        "is_error": message.is_error,
    })
}

/// TS `isAnthropicEffort`.
pub(crate) fn is_anthropic_effort(value: &str) -> bool {
    matches!(value, "low" | "medium" | "high" | "xhigh" | "max")
}

/// What a reply of a per-message-effort model records in
/// `providerThinkingLevel` when its request left no effort in force (omp
/// records `{topLevel: null, tail: null}`); otherwise it records the effort.
pub(crate) const NO_EFFORT: &str = "none";

/// A reply of the managed provider whose request recorded its effort
/// controls: its wire index and the effort it left in force (`None`: none).
type EffortRecord = (usize, Option<String>);

/// TS `ConvertedAnthropicMessages`.
struct ConvertedMessages {
    messages: Vec<JsonValue>,
    assistant_levels: Vec<EffortRecord>,
}

/// Settings of [`convert_messages`].
struct ConvertSettings<'a> {
    is_oauth_token: bool,
    cache_control: Option<&'a JsonValue>,
    allow_empty_signature: bool,
    managed_provider: Option<&'a str>,
    /// Native tool changes: converts `tool_addition` definitions.
    native_tools: Option<NativeTools<'a>>,
}

#[derive(Clone, Copy)]
struct NativeTools<'a> {
    supports_eager_tool_input_streaming: bool,
    strict: &'a StrictPlan,
}

fn is_blank(text: &str) -> bool {
    js_trim(text).is_empty()
}

#[allow(clippy::too_many_lines)] // 1:1 port of the TS `convertMessages` body.
/// TS `convertMessages`. eukhe addition: user and assistant text blocks with
/// a `cache_breakpoint` carry the request's `cache_control` mark.
fn convert_messages(
    transformed: &[Message],
    settings: &ConvertSettings<'_>,
) -> Result<ConvertedMessages, Thrown> {
    let mut params: Vec<JsonValue> = Vec::new();
    let mut assistant_levels: Vec<EffortRecord> = Vec::new();
    let mut pending_system: Vec<JsonValue> = Vec::new();
    let mut index = 0;
    while index < transformed.len() {
        match &transformed[index] {
            Message::System(message) => {
                let text = render_system_message_update(message);
                let mut blocks: Vec<JsonValue> = Vec::new();
                if !text.is_empty() {
                    blocks.push(json!({ "type": "text", "text": sanitize_surrogates(&text) }));
                }
                if let Some(native) = settings.native_tools {
                    let added = message.tools_added.clone().unwrap_or_default();
                    let redefined: HashSet<&str> =
                        added.iter().map(|tool| tool.name.as_str()).collect();
                    for tool in message.tools_removed.iter().flatten() {
                        if redefined.contains(tool.name.as_str()) {
                            continue;
                        }
                        let name = if settings.is_oauth_token {
                            to_claude_code_name(&tool.name)
                        } else {
                            tool.name.clone()
                        };
                        blocks.push(json!({
                            "type": "tool_removal",
                            "tool": { "type": "tool_reference", "name": name },
                        }));
                    }
                    for definition in convert_tools(
                        &added,
                        settings.is_oauth_token,
                        native.supports_eager_tool_input_streaming,
                        native.strict,
                        None,
                    )? {
                        blocks.push(json!({
                            "type": "tool_addition",
                            "tool": { "type": "tool_definition", "definition": definition },
                        }));
                    }
                }
                if !blocks.is_empty() {
                    pending_system.push(json!({ "role": "system", "content": blocks }));
                }
            }
            Message::User(message) => match &message.content {
                UserContent::Text(text) => {
                    if !is_blank(text) {
                        params
                            .push(json!({ "role": "user", "content": sanitize_surrogates(text) }));
                    }
                }
                UserContent::Blocks(items) => {
                    let blocks: Vec<JsonValue> = items
                        .iter()
                        .filter(|item| match item {
                            UserContentBlock::Text(text) => !is_blank(&text.text),
                            UserContentBlock::Image(_) => true,
                        })
                        .map(|item| match item {
                            UserContentBlock::Text(text) => {
                                let mut block =
                                    json!({ "type": "text", "text": sanitize_surrogates(&text.text) });
                                if let Some(cache_control) =
                                    settings.cache_control.filter(|_| has_cache_breakpoint(item))
                                {
                                    block["cache_control"] = cache_control.clone();
                                }
                                block
                            }
                            UserContentBlock::Image(image) => {
                                image_block(&image.data, &image.mime_type)
                            }
                        })
                        .collect();
                    if !blocks.is_empty() {
                        params.push(json!({ "role": "user", "content": blocks }));
                    }
                }
            },
            Message::Assistant(message) => {
                params.append(&mut pending_system);
                let mut blocks: Vec<JsonValue> = Vec::new();
                for block in &message.content {
                    match block {
                        AssistantContentBlock::Text(text) => {
                            if is_blank(&text.text) {
                                continue;
                            }
                            let mut text_block =
                                json!({ "type": "text", "text": sanitize_surrogates(&text.text) });
                            if let Some(cache_control) = settings
                                .cache_control
                                .filter(|_| has_assistant_cache_breakpoint(block))
                            {
                                text_block["cache_control"] = cache_control.clone();
                            }
                            blocks.push(text_block);
                        }
                        AssistantContentBlock::Thinking(thinking) => {
                            if thinking.redacted == Some(true) {
                                // TS `data: block.thinkingSignature!`; an
                                // absent signature serializes as no key.
                                let mut redacted = json!({ "type": "redacted_thinking" });
                                if let Some(signature) = &thinking.thinking_signature {
                                    redacted["data"] = JsonValue::String(signature.clone());
                                }
                                blocks.push(redacted);
                                continue;
                            }
                            let signature = thinking
                                .thinking_signature
                                .as_deref()
                                .filter(|signature| !is_blank(signature));
                            if is_blank(&thinking.thinking) && signature.is_none() {
                                continue;
                            }
                            let text = sanitize_surrogates(&thinking.thinking);
                            blocks.push(match signature {
                                None if settings.allow_empty_signature => json!({
                                    "type": "thinking", "thinking": text, "signature": "",
                                }),
                                None => json!({ "type": "text", "text": text }),
                                Some(signature) => json!({
                                    "type": "thinking", "thinking": text, "signature": signature,
                                }),
                            });
                        }
                        AssistantContentBlock::ToolCall(call) => {
                            let name = if settings.is_oauth_token {
                                to_claude_code_name(&call.name)
                            } else {
                                call.name.clone()
                            };
                            blocks.push(json!({
                                "type": "tool_use",
                                "id": call.id,
                                "name": name,
                                "input": call.arguments,
                            }));
                        }
                    }
                }
                if blocks.is_empty() {
                    index += 1;
                    continue;
                }
                let message_index = params.len();
                params.push(json!({ "role": "assistant", "content": blocks }));
                if let (Some(managed), Some(level)) =
                    (settings.managed_provider, &message.provider_thinking_level)
                {
                    if message.api == "anthropic-messages" && message.provider == managed {
                        if is_anthropic_effort(level) {
                            assistant_levels.push((message_index, Some(level.clone())));
                        } else if level == NO_EFFORT {
                            assistant_levels.push((message_index, None));
                        }
                    }
                }
            }
            Message::ToolResult(_) => {
                let mut results: Vec<JsonValue> = Vec::new();
                while let Some(Message::ToolResult(result)) = transformed.get(index) {
                    results.push(convert_tool_result(result));
                    index += 1;
                }
                params.push(json!({ "role": "user", "content": results }));
                continue;
            }
        }
        index += 1;
    }
    params.append(&mut pending_system);

    if let (Some(cache_control), Some(last)) = (settings.cache_control, params.last_mut()) {
        let role = last.get("role").and_then(JsonValue::as_str);
        if matches!(role, Some("user" | "system")) {
            match last.get_mut("content") {
                Some(JsonValue::Array(blocks)) => {
                    if let Some(block) = blocks.last_mut() {
                        let kind = block.get("type").and_then(JsonValue::as_str);
                        if matches!(
                            kind,
                            Some(
                                "text" | "image" | "tool_result" | "tool_addition" | "tool_removal"
                            )
                        ) {
                            block["cache_control"] = cache_control.clone();
                        }
                    }
                }
                Some(JsonValue::String(text)) => {
                    let text = std::mem::take(text);
                    last["content"] = json!([
                        { "type": "text", "text": text, "cache_control": cache_control },
                    ]);
                }
                _ => {}
            }
        }
    }

    Ok(ConvertedMessages {
        messages: params,
        assistant_levels,
    })
}

/// omp `planAnthropicEffortControls`: the request's effort controls.
struct EffortPlan {
    /// Top-level `output_config.effort`: byte-stable across a conversation,
    /// the first recorded request's effort, or this request's when none is
    /// recorded.
    top_level: Option<String>,
    /// Per-message effort controls: the wire index each goes before, and
    /// its effort.
    inserts: Vec<(usize, String)>,
    /// The effort in force after this request: what its reply records.
    tail: Option<String>,
}

/// omp `planAnthropicEffortControls`: top-level effort stays the first
/// recorded request's, every recorded change replays as a per-message
/// control before the reply of the request that made it, and this request's
/// own change (`current`) goes last.
fn plan_effort_controls(
    messages: &[JsonValue],
    records: &[EffortRecord],
    current: Option<&str>,
) -> EffortPlan {
    let top_level = match records.first() {
        Some((_, first)) => first.clone(),
        None => current.map(str::to_owned),
    };
    let mut tail = top_level.clone();
    let mut inserts: Vec<(usize, String)> = Vec::new();
    let change = |index: usize, effort: &str, inserts: &mut Vec<(usize, String)>| match inserts
        .iter_mut()
        .find(|(at, _)| *at == index)
    {
        Some(existing) => effort.clone_into(&mut existing.1),
        None => inserts.push((index, effort.to_owned())),
    };
    for (index, recorded) in records {
        if let Some(recorded) = recorded {
            if tail.as_deref() != Some(recorded.as_str()) {
                change(
                    effort_insert_index(messages, *index),
                    recorded,
                    &mut inserts,
                );
                tail = Some(recorded.clone());
            }
        }
    }
    if let Some(current) = current {
        if tail.as_deref() != Some(current) {
            change(
                effort_insert_index(messages, messages.len()),
                current,
                &mut inserts,
            );
            tail = Some(current.to_owned());
        }
    }
    EffortPlan {
        top_level,
        inserts,
        tail,
    }
}

/// omp `anthropicEffortInsertIndex`: the slot of an effort control for the
/// reply that lands at `end`: before the turn's user message, where
/// Anthropic applies it to that reply, or at `end` when the request
/// continues a tool loop, so it never lands between a `tool_use` and its
/// `tool_result`.
fn effort_insert_index(messages: &[JsonValue], end: usize) -> usize {
    for index in (0..end).rev() {
        let message = &messages[index];
        match message.get("role").and_then(JsonValue::as_str) {
            Some("assistant") => return end,
            Some("user") if !is_tool_results(message) => return index,
            _ => {}
        }
    }
    end
}

/// Whether a wire `user` message carries tool results only (omp's
/// `toolResult` messages).
fn is_tool_results(message: &JsonValue) -> bool {
    message
        .get("content")
        .and_then(JsonValue::as_array)
        .is_some_and(|blocks| {
            !blocks.is_empty()
                && blocks.iter().all(|block| {
                    block.get("type").and_then(JsonValue::as_str) == Some("tool_result")
                })
        })
}

/// omp `effortControlsBlockDisabledThinking`: Anthropic rejects a
/// per-message effort control with thinking off, and `disabled` above
/// `high` effort; both outlive a thinking toggle.
fn effort_controls_block_disabled_thinking(
    messages: &[JsonValue],
    records: &[EffortRecord],
) -> bool {
    let plan = plan_effort_controls(messages, records, None);
    !plan.inserts.is_empty() || matches!(plan.top_level.as_deref(), Some("xhigh" | "max"))
}

/// The wire messages with the planned effort controls spliced in.
fn insert_effort_controls(
    messages: Vec<JsonValue>,
    mut inserts: Vec<(usize, String)>,
) -> Vec<JsonValue> {
    if inserts.is_empty() {
        return messages;
    }
    inserts.sort_by_key(|(index, _)| *index);
    let control = |effort: String| json!({ "role": "system", "content": [], "output_config": { "effort": effort } });
    let mut wire = Vec::with_capacity(messages.len() + inserts.len());
    let mut pending = inserts.into_iter().peekable();
    for (index, message) in messages.into_iter().enumerate() {
        while let Some((_, effort)) = pending.next_if(|(at, _)| *at == index) {
            wire.push(control(effort));
        }
        wire.push(message);
    }
    wire.extend(pending.map(|(_, effort)| control(effort)));
    wire
}

/// omp `buildParams` for a per-message-effort model: the request's own
/// `thinking` (before the prefix binding) and the effort it asks for.
fn per_message_effort_thinking(
    options: &AnthropicOptions,
    disabled_thinking: Option<AnthropicDisabledThinking>,
    display: &str,
    messages: &[JsonValue],
    records: &[EffortRecord],
) -> (Option<JsonValue>, Option<String>) {
    match options.thinking_enabled {
        Some(true) => (
            Some(json!({ "type": "adaptive", "display": display })),
            options.effort.clone().filter(|effort| !effort.is_empty()),
        ),
        Some(false) => match disabled_thinking {
            Some(AnthropicDisabledThinking::Disabled)
                if !effort_controls_block_disabled_thinking(messages, records) =>
            {
                (Some(json!({ "type": "disabled" })), None)
            }
            Some(AnthropicDisabledThinking::BetweenTools) => {
                (Some(json!({ "type": "between_tools" })), None)
            }
            // Adaptive-only models cannot turn thinking off: an omitted
            // `thinking` is adaptive, so off pins the lowest effort.
            Some(AnthropicDisabledThinking::Disabled) | None => (None, Some("low".to_owned())),
        },
        None => (None, None),
    }
}

/// Keywords Anthropic strict tool use rejects for the whole request.
const ANTHROPIC_STRICT_UNSUPPORTED_KEYWORDS: [&str; 11] = [
    "minimum",
    "maximum",
    "exclusiveMinimum",
    "exclusiveMaximum",
    "multipleOf",
    "maxItems",
    "uniqueItems",
    "minContains",
    "maxContains",
    "minProperties",
    "maxProperties",
];
const ANTHROPIC_STRICT_STRING_FORMATS: [&str; 10] = [
    "date-time",
    "time",
    "date",
    "duration",
    "email",
    "hostname",
    "uri",
    "ipv4",
    "ipv6",
    "uuid",
];

/// TS `isAnthropicStrictUnsupportedKeyword`.
fn is_anthropic_strict_unsupported_keyword(key: &str, value: &JsonValue) -> bool {
    if ANTHROPIC_STRICT_UNSUPPORTED_KEYWORDS.contains(&key) {
        return true;
    }
    if key == "minItems" {
        // TS `value !== 0 && value !== 1`: exact comparison with the literals.
        #[allow(clippy::float_cmp)]
        let allowed = value.as_f64().is_some_and(|n| n == 0.0 || n == 1.0);
        return !allowed;
    }
    if key == "format" {
        return !value
            .as_str()
            .is_some_and(|format| ANTHROPIC_STRICT_STRING_FORMATS.contains(&format));
    }
    false
}

/// TS `convertTools`.
pub(crate) fn convert_tools(
    tools: &[Tool],
    is_oauth_token: bool,
    supports_eager_tool_input_streaming: bool,
    strict_plan: &StrictPlan,
    cache_control: Option<&JsonValue>,
) -> Result<Vec<JsonValue>, Thrown> {
    let last = tools.len().saturating_sub(1);
    tools
        .iter()
        .enumerate()
        .map(|(index, tool)| {
            let strict =
                strict_plan.resolve(tool, Some(&is_anthropic_strict_unsupported_keyword))?;
            let parameters = get_json_schema_tool_parameters(
                tool,
                if strict == Some(true) {
                    StrictToolParameters::Strict
                } else {
                    StrictToolParameters::AsDeclared
                },
            )?;
            let properties = match parameters.get("properties") {
                None | Some(JsonValue::Null) => json!({}),
                Some(value) => value.clone(),
            };
            let required = match parameters.get("required") {
                None | Some(JsonValue::Null) => json!([]),
                Some(value) => value.clone(),
            };
            let input_schema = if strict == Some(true) {
                let mut schema = match &parameters {
                    JsonValue::Object(object) => object.clone(),
                    _ => JsonObject::new(),
                };
                schema.insert("type".into(), "object".into());
                schema.insert("properties".into(), properties);
                schema.insert("required".into(), required);
                JsonValue::Object(schema)
            } else {
                json!({ "type": "object", "properties": properties, "required": required })
            };
            let mut converted = JsonObject::new();
            let name = if is_oauth_token {
                to_claude_code_name(&tool.name)
            } else {
                tool.name.clone()
            };
            converted.insert("name".into(), name.into());
            converted.insert("description".into(), tool.description.clone().into());
            if supports_eager_tool_input_streaming {
                converted.insert("eager_input_streaming".into(), true.into());
            }
            if strict == Some(true) {
                converted.insert("strict".into(), true.into());
            }
            converted.insert("input_schema".into(), input_schema);
            if let Some(cache_control) = cache_control.filter(|_| index == last) {
                converted.insert("cache_control".into(), cache_control.clone());
            }
            Ok(JsonValue::Object(converted))
        })
        .collect()
}

/// TS `DEFERRED_TOOL_PLACEHOLDER`.
fn deferred_tool_placeholder() -> JsonValue {
    json!({
        "name": "__pi_deferred_placeholder__",
        "description": "Reserved placeholder. Never available. Never call this.",
        "input_schema": { "type": "object", "properties": {}, "required": [] },
        "defer_loading": true,
    })
}

/// TS `getBetaFeatures`.
fn get_beta_features(
    model: &Model,
    messages: &[Message],
    is_oauth_token: bool,
    native_tool_changes: bool,
    thinking_binding: bool,
    options: &AnthropicOptions,
) -> Vec<String> {
    let mut configured: Option<Option<String>> = None;
    for (name, value) in model.headers.iter().flatten() {
        if name.to_lowercase() == "anthropic-beta" {
            configured = Some(Some(value.clone()));
        }
    }
    for (name, value) in options.stream.request.headers.iter().flatten() {
        if name.to_lowercase() == "anthropic-beta" {
            configured = Some(value.clone());
        }
    }
    let dedupe = |features: Vec<String>| -> Vec<String> {
        let mut seen = HashSet::new();
        features
            .into_iter()
            .filter(|feature| seen.insert(feature.clone()))
            .collect()
    };
    match configured {
        Some(None) => return Vec::new(),
        Some(Some(value)) => {
            return dedupe(
                value
                    .split(',')
                    .map(|feature| js_trim(feature).to_owned())
                    .filter(|feature| !feature.is_empty())
                    .collect(),
            );
        }
        None => {}
    }
    let compat = model_compat(model);
    let mut features: Vec<String> = Vec::new();
    if is_oauth_token {
        features.push("claude-code-20250219".into());
        features.push("oauth-2025-04-20".into());
    }
    if !get_current_tools(messages).is_empty()
        && !get_anthropic_compat(model).supports_eager_tool_input_streaming
    {
        features.push(FINE_GRAINED_TOOL_STREAMING_BETA.into());
    }
    if model.reasoning
        && options.thinking_enabled == Some(true)
        && options.interleaved_thinking.unwrap_or(true)
        && !adaptive_thinking(model)
    {
        features.push(INTERLEAVED_THINKING_BETA.into());
    }
    if compat
        .and_then(|compat| compat.allowed_fallback_models.as_ref())
        .is_some_and(|models| !models.is_empty())
    {
        features.push(SERVER_SIDE_FALLBACK_BETA.into());
    }
    if compat.and_then(|compat| compat.supports_mid_convo_effort) == Some(true) {
        features.push(MID_CONVERSATION_OUTPUT_CONFIG_BETA.into());
    }
    // omp: the binding beta follows the body's `thinking.block_binding`.
    if thinking_binding {
        features.push(THINKING_BINDING_CONTROLS_BETA.into());
    }
    if native_tool_changes {
        features.push(INLINE_TOOLS_BETA.into());
    }
    dedupe(features)
}

/// TS `buildParams`; also returns what the reply of a per-message-effort
/// model records in `providerThinkingLevel` (the effort the request left in
/// force, or [`NO_EFFORT`]); `None` for other models.
///
/// eukhe addition: marked user blocks spend cache-mark slots first; the
/// optional marks take the slots left, in this order
/// (`eukhe_bend::rules::cache_marks::grant`): the system prompt's shared
/// prefix (the whole prompt without a
/// [`StreamOptions::system_cache_breakpoint`](crate::types::StreamOptions)),
/// the last tool, and the end of the session's tail of the prompt.
#[allow(clippy::too_many_lines)] // 1:1 port of the TS `buildParams` body.
pub(crate) fn build_params(
    model: &Model,
    messages: &[Message],
    is_oauth_token: bool,
    options: &AnthropicOptions,
) -> Result<(JsonObject, Option<String>), Thrown> {
    let cache_control = get_cache_control(
        model,
        options.stream.cache_retention,
        options.stream.request.env.as_ref(),
    );
    let compat = get_anthropic_compat(model);
    let model_compat = model_compat(model);
    let mid_convo_effort =
        model_compat.and_then(|compat| compat.supports_mid_convo_effort) == Some(true);
    let initial_system = get_initial_system_message(messages);
    // eukhe addition: the shared prefix of the prompt and the session's tail
    // go as blocks of their own, so the prefix's mark is the same in every
    // session.
    let (system_prefix, system_tail) = split_system_prompt(
        initial_system,
        options.stream.system_cache_breakpoint.as_deref(),
    );
    let normalize =
        |id: &str, _: &Model, _: &eukhe_types::pi_ai::AssistantMessage| normalize_tool_call_id(id);
    let transformed = transform_messages(messages, model, Some(&normalize));
    let conversation = if initial_system.is_some() {
        &transformed[1..]
    } else {
        &transformed[..]
    };
    let initial_tools: Vec<Tool> = initial_system
        .and_then(|system| system.tools_added.clone())
        .unwrap_or_default();
    let native_tool_changes = compat.supports_mid_convo_system_messages
        && compat.supports_mid_convo_tool_changes
        && !initial_tools.is_empty();
    let request_tools: Vec<Tool> = if native_tool_changes {
        initial_tools.clone()
    } else {
        get_current_tools(messages)
    };
    let added_tools = conversation
        .iter()
        .filter(|_| native_tool_changes)
        .filter_map(|message| match message {
            Message::System(system) => system.tools_added.as_ref(),
            Message::User(_) | Message::Assistant(_) | Message::ToolResult(_) => None,
        })
        .flatten();
    let strict = StrictPlan::new(
        request_tools.iter().chain(added_tools),
        StrictSupport {
            supported: compat.supports_strict_tools,
            cap: compat.strict_cap,
        },
        Some(&is_anthropic_strict_unsupported_keyword),
    )?;
    let converted = convert_messages(
        conversation,
        &ConvertSettings {
            is_oauth_token,
            cache_control: cache_control.as_ref(),
            allow_empty_signature: compat.allow_empty_signature,
            managed_provider: mid_convo_effort.then_some(model.provider.as_str()),
            native_tools: native_tool_changes.then_some(NativeTools {
                supports_eager_tool_input_streaming: compat.supports_eager_tool_input_streaming,
                strict: &strict,
            }),
        },
    )?;
    let display = options
        .thinking_display
        .clone()
        .unwrap_or_else(|| "summarized".to_owned());
    // omp `buildParams` of a per-message-effort model: the request's own
    // thinking and effort, the prefix binding, then the effort plan.
    let mut effort_thinking: Option<JsonValue> = None;
    let mut effort_plan: Option<EffortPlan> = None;
    let wire_messages = if mid_convo_effort {
        let records = &converted.assistant_levels;
        let (mut thinking, current) = per_message_effort_thinking(
            options,
            model_compat.and_then(|compat| compat.disabled_thinking),
            &display,
            &converted.messages,
            records,
        );
        let binding = model_compat
            .and_then(|compat| compat.supports_thinking_binding_controls)
            .unwrap_or(true);
        if binding {
            let bound = thinking.get_or_insert_with(|| json!({ "type": "adaptive" }));
            if matches!(bound["type"].as_str(), Some("adaptive" | "enabled")) {
                bound["block_binding"] = json!({ "prefix_mismatch_behavior": "drop_block" });
            }
        }
        let mut plan = plan_effort_controls(&converted.messages, records, current.as_deref());
        // `between_tools` is a 400 at `xhigh`/`max` effort, and the effort in
        // force outlives a thinking toggle: the default adaptive request
        // accepts every effort.
        if thinking
            .as_ref()
            .is_some_and(|thinking| thinking["type"] == "between_tools")
            && matches!(plan.top_level.as_deref(), Some("xhigh" | "max"))
        {
            thinking = None;
        }
        let inserts = std::mem::take(&mut plan.inserts);
        effort_thinking = thinking;
        effort_plan = Some(plan);
        insert_effort_controls(converted.messages, inserts)
    } else {
        converted.messages
    };
    let betas = get_beta_features(
        model,
        messages,
        is_oauth_token,
        native_tool_changes,
        effort_thinking
            .as_ref()
            .is_some_and(|thinking| thinking.get("block_binding").is_some()),
        options,
    );

    let tool_cache_control = cache_control
        .as_ref()
        .filter(|_| compat.supports_cache_control_on_tools);
    let [prefix_mark, tools_mark, tail_mark] = eukhe_bend::rules::cache_marks::grant(
        placed_marks(&wire_messages, "cache_control"),
        [
            cache_control.is_some() && !system_prefix.is_empty(),
            tool_cache_control.is_some() && !request_tools.is_empty(),
            cache_control.is_some() && !system_tail.is_empty(),
        ],
    );

    let mut params = JsonObject::new();
    params.insert("model".into(), model.id.clone().into());
    params.insert("messages".into(), JsonValue::Array(wire_messages));
    params.insert(
        "max_tokens".into(),
        options.stream.max_tokens.unwrap_or(model.max_tokens).into(),
    );
    params.insert("stream".into(), true.into());
    if !betas.is_empty() {
        params.insert("betas".into(), betas.into());
    }

    let system_block = |text: &str, marked: bool| {
        let mut block = json!({ "type": "text", "text": text });
        if let Some(cache_control) = cache_control.as_ref().filter(|_| marked) {
            block["cache_control"] = cache_control.clone();
        }
        block
    };
    let mut system = Vec::new();
    if is_oauth_token {
        // Claude Code's billing attribution opens `system`, uncached; the
        // client patches its `cch` into the serialized body. The identity
        // block after it is too short to be worth a mark.
        let first_user_text = params
            .get("messages")
            .and_then(JsonValue::as_array)
            .map_or("", |messages| billing::first_user_text(messages));
        system.push(json!({
            "type": "text",
            "text": billing::billing_header(first_user_text, CLAUDE_CODE_VERSION),
        }));
        system.push(json!({ "type": "text", "text": CLAUDE_CODE_SYSTEM_PROMPT }));
    }
    for (text, marked) in [(&system_prefix, prefix_mark), (&system_tail, tail_mark)] {
        if !text.is_empty() {
            system.push(system_block(&sanitize_surrogates(text), marked));
        }
    }
    if !system.is_empty() {
        params.insert("system".into(), JsonValue::Array(system));
    }

    if let Some(temperature) = options.stream.temperature {
        if options.thinking_enabled != Some(true)
            && !mid_convo_effort
            && compat.supports_temperature
        {
            params.insert(
                "temperature".into(),
                crate::utils::js::js_number_value(temperature),
            );
        }
    }

    let tools_cache = tool_cache_control.filter(|_| tools_mark);
    if native_tool_changes {
        let mut tools = convert_tools(
            &initial_tools,
            is_oauth_token,
            compat.supports_eager_tool_input_streaming,
            &strict,
            tools_cache,
        )?;
        tools.push(deferred_tool_placeholder());
        params.insert("tools".into(), JsonValue::Array(tools));
    } else if !request_tools.is_empty() {
        params.insert(
            "tools".into(),
            JsonValue::Array(convert_tools(
                &request_tools,
                is_oauth_token,
                compat.supports_eager_tool_input_streaming,
                &strict,
                tools_cache,
            )?),
        );
    }

    let recorded_effort = if let Some(plan) = effort_plan {
        if let Some(thinking) = effort_thinking {
            params.insert("thinking".into(), thinking);
        }
        if let Some(effort) = &plan.top_level {
            params.insert("output_config".into(), json!({ "effort": effort }));
        }
        Some(plan.tail.unwrap_or_else(|| NO_EFFORT.to_owned()))
    } else {
        None
    };
    if !mid_convo_effort && model.reasoning {
        let quirks = Quirks::of(model);
        if options.thinking_enabled == Some(true) {
            if adaptive_thinking(model) {
                // omp `buildParams`: `display` only where the model takes
                // it (Claude 4.7 and later; 4.6 rejects it with a 400).
                let mut thinking = json!({ "type": "adaptive" });
                if quirks.thinking_display() == Some(true) {
                    thinking["display"] = display.into();
                }
                params.insert("thinking".into(), thinking);
                if let Some(effort) = options.effort.as_ref().filter(|effort| !effort.is_empty()) {
                    params.insert("output_config".into(), json!({ "effort": effort }));
                }
            } else {
                // No budget from the caller: the default budget of the
                // smallest level.
                let budget = options
                    .thinking_budget_tokens
                    .filter(|&b| b != 0)
                    .unwrap_or_else(|| thinking_budget_for_level(ThinkingLevel::Minimal, None));
                params.insert(
                    "thinking".into(),
                    json!({ "type": "enabled", "budget_tokens": budget, "display": display }),
                );
            }
        } else if options.thinking_enabled == Some(false)
            && thinking_level_map(model).and_then(|map| map.get(&ModelThinkingLevel::Off))
                != Some(&None)
        {
            params.insert("thinking".into(), json!({ "type": "disabled" }));
        }
    }

    if let Some(JsonValue::String(user_id)) = options
        .stream
        .metadata
        .as_ref()
        .and_then(|metadata| metadata.get("user_id"))
    {
        params.insert("metadata".into(), json!({ "user_id": user_id }));
    }

    if let Some(tool_choice) = &options.tool_choice {
        params.insert(
            "tool_choice".into(),
            match tool_choice {
                AnthropicToolChoice::Auto => json!({ "type": "auto" }),
                AnthropicToolChoice::Any => json!({ "type": "any" }),
                AnthropicToolChoice::None => json!({ "type": "none" }),
                AnthropicToolChoice::Tool { name } => json!({ "type": "tool", "name": name }),
            },
        );
    }

    if let Some(models) = model_compat
        .and_then(|compat| compat.allowed_fallback_models.as_ref())
        .filter(|models| !models.is_empty())
    {
        params.insert(
            "fallbacks".into(),
            JsonValue::Array(
                models
                    .iter()
                    .map(|fallback| json!({ "model": fallback.model }))
                    .collect(),
            ),
        );
    }

    Ok((params, recorded_effort))
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::pi_ai::TextContent;

    fn tool_result(is_error: bool) -> ToolResultMessage {
        ToolResultMessage {
            tool_call_id: "c1".to_string(),
            tool_name: "shot".to_string(),
            content: vec![
                UserContentBlock::Text(TextContent::new("failed")),
                UserContentBlock::Image(eukhe_types::pi_ai::ImageContent {
                    data: "AA==".to_string(),
                    mime_type: "image/png".to_string(),
                }),
            ],
            details: None,
            usage: None,
            nested_calls: None,
            is_error,
            timestamp: 1,
            duration_ms: None,
        }
    }

    /// Regression: an error tool result that carried an image was sent
    /// with the image block, which Anthropic refuses ("all content must be
    /// type `text` if `is_error` is true"); every later request of the
    /// session failed the same way. Its images now go as text lines; a
    /// successful result keeps them.
    #[test]
    fn an_error_tool_result_sends_text_only() {
        assert_eq!(
            (
                convert_tool_result(&tool_result(true)),
                convert_tool_result(&tool_result(false)),
            ),
            (
                json!({
                    "type": "tool_result",
                    "tool_use_id": "c1",
                    "content": "failed\n[image omitted: error result]",
                    "is_error": true,
                }),
                json!({
                    "type": "tool_result",
                    "tool_use_id": "c1",
                    "content": [
                        { "type": "text", "text": "failed" },
                        {
                            "type": "image",
                            "source": { "type": "base64", "media_type": "image/png", "data": "AA==" },
                        },
                    ],
                    "is_error": false,
                }),
            )
        );
    }

    #[test]
    fn normalizes_tool_call_ids() {
        assert_eq!(normalize_tool_call_id("call|abc.def"), "call_abc_def");
        assert_eq!(normalize_tool_call_id(&"a".repeat(70)), "a".repeat(64));
        assert_eq!(normalize_tool_call_id("x😀"), "x__");
    }

    #[test]
    fn claude_code_names() {
        assert_eq!(to_claude_code_name("todowrite"), "TodoWrite");
        assert_eq!(to_claude_code_name("custom"), "custom");
    }
}
