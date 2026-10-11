//! Request payload of the Mistral chat API: the SDK-style (camelCase)
//! payload `onPayload` sees, built from the transcript, and its conversion to
//! the `snake_case` wire format. Section of the port of
//! `api/mistral-conversations.ts`.

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, JsonObject, JsonValue, Message, Modality, Model, Tool,
    ToolResultMessage, UserContent, UserContentBlock,
};
use serde_json::json;

use crate::api::constrained_sampling::{
    get_json_schema_tool_parameters, resolve_json_schema_strict_sampling, StrictToolParameters,
};
use crate::utils::diagnostics::{thrown, Thrown};

use super::{is_truthy, type_error, MistralOptions};
use crate::utils::js::{js_number_value, js_trim, json_stringify};
use crate::utils::sanitize_unicode::sanitize_surrogates;
use crate::utils::text::{get_system_message_text, render_system_message_update};
use crate::utils::transcript::get_current_tools;

/// TS `buildChatPayload`: the SDK-style payload, keys in TS insertion order.
pub(super) fn build_chat_payload(
    model: &Model,
    context_messages: &[Message],
    messages: &[Message],
    options: &MistralOptions,
) -> Result<JsonObject, Thrown> {
    let mut payload = JsonObject::new();
    payload.insert("model".into(), JsonValue::String(model.id.clone()));
    payload.insert("stream".into(), JsonValue::Bool(true));
    payload.insert(
        "messages".into(),
        JsonValue::Array(to_chat_messages(
            messages,
            model.input.contains(&Modality::Image),
        )),
    );

    let current_tools = get_current_tools(context_messages);
    if !current_tools.is_empty() {
        payload.insert(
            "tools".into(),
            JsonValue::Array(to_function_tools(&current_tools)?),
        );
    }
    if let Some(temperature) = options.stream.temperature {
        payload.insert("temperature".into(), js_number_value(temperature));
    }
    if let Some(max_tokens) = options.stream.max_tokens {
        payload.insert("maxTokens".into(), JsonValue::from(max_tokens));
    }
    if let Some(tool_choice) = options
        .tool_choice
        .as_ref()
        .filter(|choice| is_truthy(choice))
    {
        if let Some(mapped) = map_tool_choice(tool_choice)? {
            payload.insert("toolChoice".into(), mapped);
        }
    }
    if let Some(prompt_mode) = options.prompt_mode.as_ref().filter(|mode| is_truthy(mode)) {
        payload.insert("promptMode".into(), prompt_mode.clone());
    }
    if let Some(effort) = options
        .reasoning_effort
        .as_ref()
        .filter(|effort| is_truthy(effort))
    {
        payload.insert("reasoningEffort".into(), effort.clone());
    }
    if let Some(session_id) = options.prompt_cache_session_id() {
        payload.insert(
            "promptCacheKey".into(),
            JsonValue::String(session_id.to_owned()),
        );
    }
    Ok(payload)
}

/// TS `toFunctionTools`.
fn to_function_tools(tools: &[Tool]) -> Result<Vec<JsonValue>, Thrown> {
    tools
        .iter()
        .map(|tool| {
            let strict = resolve_json_schema_strict_sampling(tool, true, None).map_err(thrown)?;
            // TS `stripSymbolKeys`: TypeBox `Kind` symbols do not exist on
            // Rust JSON values, so the parameters are already plain JSON.
            let parameters_mode = if strict == Some(true) {
                StrictToolParameters::Strict
            } else {
                StrictToolParameters::AsDeclared
            };
            let parameters =
                get_json_schema_tool_parameters(tool, parameters_mode).map_err(thrown)?;
            Ok(json!({
                "type": "function",
                "function": {
                    "name": tool.name,
                    "description": tool.description,
                    "parameters": parameters,
                    "strict": strict.unwrap_or(false),
                },
            }))
        })
        .collect()
}

fn image_url(mime_type: &str, data: &str) -> String {
    format!("data:{mime_type};base64,{data}")
}

/// TS `toChatMessages`.
pub(super) fn to_chat_messages(messages: &[Message], supports_images: bool) -> Vec<JsonValue> {
    let mut result = Vec::new();
    for (index, message) in messages.iter().enumerate() {
        match message {
            Message::System(system) => {
                let text = if index == 0 {
                    get_system_message_text(system)
                } else {
                    render_system_message_update(system)
                };
                if !text.is_empty() {
                    result.push(json!({ "role": "system", "content": sanitize_surrogates(&text) }));
                }
            }
            Message::User(user) => match &user.content {
                UserContent::Text(text) => {
                    result.push(json!({ "role": "user", "content": sanitize_surrogates(text) }));
                }
                UserContent::Blocks(blocks) => {
                    let had_images = blocks
                        .iter()
                        .any(|block| matches!(block, UserContentBlock::Image(_)));
                    let content: Vec<JsonValue> = blocks
                        .iter()
                        .filter(|block| {
                            matches!(block, UserContentBlock::Text(_)) || supports_images
                        })
                        .map(|block| match block {
                            UserContentBlock::Text(text) => {
                                json!({ "type": "text", "text": sanitize_surrogates(&text.text) })
                            }
                            UserContentBlock::Image(image) => json!({
                                "type": "image_url",
                                "imageUrl": image_url(&image.mime_type, &image.data),
                            }),
                        })
                        .collect();
                    if !content.is_empty() {
                        result.push(json!({ "role": "user", "content": content }));
                    } else if had_images && !supports_images {
                        result.push(json!({
                            "role": "user",
                            "content": "(image omitted: model does not support images)",
                        }));
                    }
                }
            },
            Message::Assistant(assistant) => {
                if let Some(message) = assistant_message(assistant) {
                    result.push(message);
                }
            }
            Message::ToolResult(tool_result) => {
                result.push(tool_result_message(tool_result, supports_images));
            }
        }
    }
    result
}

/// The assistant branch of TS `toChatMessages`; `None` when nothing replays.
fn assistant_message(assistant: &AssistantMessage) -> Option<JsonValue> {
    let mut content_parts = Vec::new();
    let mut tool_calls = Vec::new();
    for block in &assistant.content {
        match block {
            AssistantContentBlock::Text(text) => {
                if !js_trim(&text.text).is_empty() {
                    content_parts
                        .push(json!({ "type": "text", "text": sanitize_surrogates(&text.text) }));
                }
            }
            AssistantContentBlock::Thinking(thinking) => {
                if !js_trim(&thinking.thinking).is_empty() {
                    content_parts.push(json!({
                        "type": "thinking",
                        "thinking": [{
                            "type": "text",
                            "text": sanitize_surrogates(&thinking.thinking),
                        }],
                    }));
                }
            }
            AssistantContentBlock::ToolCall(call) => tool_calls.push(json!({
                "id": call.id,
                "type": "function",
                "function": {
                    "name": call.name,
                    "arguments": json_stringify(&JsonValue::Object(call.arguments.clone())),
                },
                "index": 0,
            })),
        }
    }
    if content_parts.is_empty() && tool_calls.is_empty() {
        return None;
    }
    let mut message = JsonObject::new();
    message.insert("role".into(), "assistant".into());
    message.insert("prefix".into(), false.into());
    if !content_parts.is_empty() {
        message.insert("content".into(), JsonValue::Array(content_parts));
    }
    if !tool_calls.is_empty() {
        message.insert("toolCalls".into(), JsonValue::Array(tool_calls));
    }
    Some(JsonValue::Object(message))
}

fn tool_result_message(message: &ToolResultMessage, supports_images: bool) -> JsonValue {
    let text_result = message
        .content
        .iter()
        .filter_map(|part| match part {
            UserContentBlock::Text(text) => Some(sanitize_surrogates(&text.text).into_owned()),
            UserContentBlock::Image(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n");
    let has_images = message
        .content
        .iter()
        .any(|part| matches!(part, UserContentBlock::Image(_)));
    let tool_text =
        build_tool_result_text(&text_result, has_images, supports_images, message.is_error);
    let mut tool_content = vec![json!({ "type": "text", "text": tool_text })];
    if supports_images {
        for part in &message.content {
            if let UserContentBlock::Image(image) = part {
                tool_content.push(json!({
                    "type": "image_url",
                    "imageUrl": image_url(&image.mime_type, &image.data),
                }));
            }
        }
    }
    json!({
        "role": "tool",
        "toolCallId": message.tool_call_id,
        "name": message.tool_name,
        "content": tool_content,
    })
}

/// TS `buildToolResultText`.
fn build_tool_result_text(
    text: &str,
    has_images: bool,
    supports_images: bool,
    is_error: bool,
) -> String {
    let trimmed = js_trim(text);
    let error_prefix = if is_error { "[tool error] " } else { "" };
    if !trimmed.is_empty() {
        let image_suffix = if has_images && !supports_images {
            "\n[tool image omitted: model does not support images]"
        } else {
            ""
        };
        return format!("{error_prefix}{trimmed}{image_suffix}");
    }
    let text = match (has_images, supports_images, is_error) {
        (true, true, true) => "[tool error] (see attached image)",
        (true, true, false) => "(see attached image)",
        (true, false, true) => "[tool error] (image omitted: model does not support images)",
        (true, false, false) => "(image omitted: model does not support images)",
        (false, _, true) => "[tool error] (no tool output)",
        (false, _, false) => "(no tool output)",
    };
    text.to_owned()
}

/// TS `mapToolChoice` for a truthy choice.
fn map_tool_choice(choice: &JsonValue) -> Result<Option<JsonValue>, Thrown> {
    if let JsonValue::String(name) = choice {
        if matches!(name.as_str(), "auto" | "none" | "any" | "required") {
            return Ok(Some(choice.clone()));
        }
    }
    // `choice.function.name`
    let function = match choice {
        JsonValue::Object(object) => object.get("function"),
        JsonValue::Null => {
            return Err(type_error(
                "Cannot read properties of null (reading 'function')",
            ))
        }
        JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::String(_) | JsonValue::Array(_) => {
            None
        }
    };
    let name = match function {
        None => {
            return Err(type_error(
                "Cannot read properties of undefined (reading 'name')",
            ))
        }
        Some(JsonValue::Null) => {
            return Err(type_error(
                "Cannot read properties of null (reading 'name')",
            ))
        }
        Some(JsonValue::Object(function)) => function.get("name").cloned(),
        Some(_) => None,
    };
    let mut function = JsonObject::new();
    if let Some(name) = name {
        function.insert("name".into(), name);
    }
    Ok(Some(json!({ "type": "function", "function": function })))
}

/// TS `remapMistralProperty`: move `source` to `target` (appended unless
/// `target` exists), keeping the order of the other keys.
fn remap_property(record: &mut JsonObject, source: &str, target: &str) {
    if let Some(value) = record.shift_remove(source) {
        // JS assigns `target` before deleting `source`: a new key lands after
        // the existing ones, an existing key keeps its position.
        record.insert(target.to_owned(), value);
    }
}

/// TS `{ ...value }` of a non-null, non-undefined JSON value.
fn spread(value: &JsonValue) -> JsonObject {
    match value {
        JsonValue::Object(object) => object.clone(),
        JsonValue::Array(items) => items
            .iter()
            .enumerate()
            .map(|(index, item)| (index.to_string(), item.clone()))
            .collect(),
        JsonValue::String(text) => text
            .encode_utf16()
            .enumerate()
            .map(|(index, unit)| {
                (
                    index.to_string(),
                    JsonValue::String(String::from_utf16_lossy(&[unit])),
                )
            })
            .collect(),
        JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) => JsonObject::new(),
    }
}

fn property_read_error(value: &JsonValue, property: &str) -> Option<Thrown> {
    value.is_null().then(|| {
        type_error(&format!(
            "Cannot read properties of null (reading '{property}')"
        ))
    })
}

/// TS `toMistralWirePayload`.
pub(super) fn to_mistral_wire_payload(payload: &JsonValue) -> Result<JsonObject, Thrown> {
    if let Some(error) = property_read_error(payload, "messages") {
        return Err(error);
    }
    let mut wire_payload = spread(payload);
    for (source, target) in [
        ("topP", "top_p"),
        ("maxTokens", "max_tokens"),
        ("randomSeed", "random_seed"),
        ("responseFormat", "response_format"),
        ("toolChoice", "tool_choice"),
        ("presencePenalty", "presence_penalty"),
        ("frequencyPenalty", "frequency_penalty"),
        ("parallelToolCalls", "parallel_tool_calls"),
        ("reasoningEffort", "reasoning_effort"),
        ("promptMode", "prompt_mode"),
        ("promptCacheKey", "prompt_cache_key"),
        ("safePrompt", "safe_prompt"),
    ] {
        remap_property(&mut wire_payload, source, target);
    }
    // `payload.messages.map(...)`
    let messages = match payload.get("messages") {
        Some(JsonValue::Array(messages)) => messages
            .iter()
            .map(to_mistral_wire_message)
            .collect::<Result<Vec<_>, _>>()?,
        Some(JsonValue::Null) => {
            return Err(type_error("Cannot read properties of null (reading 'map')"))
        }
        None => {
            return Err(type_error(
                "Cannot read properties of undefined (reading 'map')",
            ))
        }
        Some(_) => return Err(type_error("payload.messages.map is not a function")),
    };
    wire_payload.insert("messages".into(), JsonValue::Array(messages));

    if let Some(JsonValue::Object(response_format)) = wire_payload.get("response_format") {
        let mut wire_response_format = response_format.clone();
        remap_property(&mut wire_response_format, "jsonSchema", "json_schema");
        if let Some(JsonValue::Object(json_schema)) = wire_response_format.get("json_schema") {
            let mut wire_json_schema = json_schema.clone();
            remap_property(&mut wire_json_schema, "schemaDefinition", "schema");
            wire_response_format.insert("json_schema".into(), JsonValue::Object(wire_json_schema));
        }
        wire_payload.insert(
            "response_format".into(),
            JsonValue::Object(wire_response_format),
        );
    }
    Ok(wire_payload)
}

/// TS `toMistralWireMessage`.
fn to_mistral_wire_message(message: &JsonValue) -> Result<JsonValue, Thrown> {
    if let Some(error) = property_read_error(message, "content") {
        return Err(error);
    }
    let mut wire_message = spread(message);
    remap_property(&mut wire_message, "toolCalls", "tool_calls");
    remap_property(&mut wire_message, "toolCallId", "tool_call_id");
    if let Some(JsonValue::Array(content)) = message.get("content") {
        let chunks = content.iter().map(to_mistral_wire_content_chunk).collect();
        wire_message.insert("content".into(), JsonValue::Array(chunks));
    }
    Ok(JsonValue::Object(wire_message))
}

/// TS `toMistralWireContentChunk`.
fn to_mistral_wire_content_chunk(chunk: &JsonValue) -> JsonValue {
    let mut wire_chunk = spread(chunk);
    for (source, target) in [
        ("imageUrl", "image_url"),
        ("documentUrl", "document_url"),
        ("documentName", "document_name"),
        ("fileId", "file_id"),
        ("referenceIds", "reference_ids"),
        ("inputAudio", "input_audio"),
    ] {
        remap_property(&mut wire_chunk, source, target);
    }
    JsonValue::Object(wire_chunk)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn remap_appends_new_target_and_keeps_order() {
        let JsonValue::Object(mut record) = json!({ "a": 1, "maxTokens": 2, "b": 3 }) else {
            unreachable!()
        };
        remap_property(&mut record, "maxTokens", "max_tokens");
        assert_eq!(
            json_stringify(&JsonValue::Object(record)),
            r#"{"a":1,"b":3,"max_tokens":2}"#
        );
    }

    #[test]
    fn tool_result_text_variants() {
        assert_eq!(
            build_tool_result_text(" x ", true, false, true),
            "[tool error] x\n[tool image omitted: model does not support images]"
        );
        assert_eq!(
            build_tool_result_text("", true, true, false),
            "(see attached image)"
        );
        assert_eq!(
            build_tool_result_text("", false, false, true),
            "[tool error] (no tool output)"
        );
    }
}
