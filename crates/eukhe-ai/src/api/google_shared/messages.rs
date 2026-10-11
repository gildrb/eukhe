//! `convertMessages` of `google-shared.ts`: transcript messages to Gemini
//! `Content[]`.

use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, JsonObject, JsonValue, Message, Modality, Model,
    ToolResultMessage, TranscriptContext, UserContent, UserContentBlock, UserMessage,
};
use serde_json::json;

use super::super::transform_messages::transform_messages;
use super::{
    requires_tool_call_id, resolve_thought_signature, supports_multimodal_function_response,
};
use crate::utils::js::js_trim;
use crate::utils::sanitize_unicode::sanitize_surrogates;
use crate::utils::transcript::{collapse_system_messages, without_initial_system_message};

/// `!text || text.trim() === ""`.
fn is_blank(text: &str) -> bool {
    js_trim(text).is_empty()
}

/// `id.replace(/[^a-zA-Z0-9_-]/g, "_").slice(0, 64)`: the regex has no `u`
/// flag, so every UTF-16 code unit of a non-matching char becomes `_`.
fn sanitize_tool_call_id(id: &str) -> String {
    let mut sanitized = String::with_capacity(id.len());
    for ch in id.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' || ch == '-' {
            sanitized.push(ch);
        } else {
            for _ in 0..ch.len_utf16() {
                sanitized.push('_');
            }
        }
    }
    sanitized.truncate(64);
    sanitized
}

fn inline_data_part(mime_type: &str, data: &str) -> JsonValue {
    json!({ "inlineData": { "mimeType": mime_type, "data": data } })
}

fn content(role: &str, parts: Vec<JsonValue>) -> JsonValue {
    let mut object = JsonObject::new();
    object.insert("role".into(), role.into());
    object.insert("parts".into(), JsonValue::Array(parts));
    JsonValue::Object(object)
}

/// A part with `text` and an optional `thoughtSignature`.
fn text_part(thought: bool, text: &str, signature: Option<String>) -> JsonValue {
    let mut part = JsonObject::new();
    if thought {
        part.insert("thought".into(), true.into());
    }
    part.insert("text".into(), sanitize_surrogates(text).into());
    if let Some(signature) = signature {
        part.insert("thoughtSignature".into(), signature.into());
    }
    JsonValue::Object(part)
}

/// Convert internal messages to Gemini `Content[]` format.
#[must_use]
pub fn convert_messages(model: &Model, context: &TranscriptContext) -> Vec<JsonValue> {
    // Gemini has no mid-conversation system messages; the leading prompt is
    // sent as systemInstruction.
    let collapsed = collapse_system_messages(context.clone());
    let conversation = without_initial_system_message(collapsed.messages());
    let normalize_tool_call_id = |id: &str, _model: &Model, _source: &AssistantMessage| -> String {
        if requires_tool_call_id(&model.id) {
            sanitize_tool_call_id(id)
        } else {
            id.to_owned()
        }
    };
    let transformed = transform_messages(conversation, model, Some(&normalize_tool_call_id));

    let mut contents: Vec<JsonValue> = Vec::new();
    for message in &transformed {
        match message {
            Message::User(user) => {
                if let Some(user_content) = convert_user(user) {
                    contents.push(user_content);
                }
            }
            Message::Assistant(assistant) => {
                let parts = convert_assistant(model, assistant);
                if !parts.is_empty() {
                    contents.push(content("model", parts));
                }
            }
            Message::ToolResult(result) => convert_tool_result(model, result, &mut contents),
            Message::System(_) => {}
        }
    }
    contents
}

fn convert_user(user: &UserMessage) -> Option<JsonValue> {
    match &user.content {
        UserContent::Text(text) => Some(content(
            "user",
            vec![json!({ "text": sanitize_surrogates(text) })],
        )),
        UserContent::Blocks(blocks) => {
            let parts: Vec<JsonValue> = blocks
                .iter()
                .map(|item| match item {
                    UserContentBlock::Text(text) => {
                        json!({ "text": sanitize_surrogates(&text.text) })
                    }
                    UserContentBlock::Image(image) => {
                        inline_data_part(&image.mime_type, &image.data)
                    }
                })
                .collect();
            (!parts.is_empty()).then(|| content("user", parts))
        }
    }
}

fn convert_assistant(model: &Model, assistant: &AssistantMessage) -> Vec<JsonValue> {
    // Only keep thinking blocks when the message is from the same provider
    // and model.
    let same_model = assistant.provider == model.provider && assistant.model == model.id;
    let mut parts = Vec::new();
    for block in &assistant.content {
        match block {
            AssistantContentBlock::Text(text) => {
                let signature =
                    resolve_thought_signature(same_model, text.text_signature.as_deref());
                // Skip empty text blocks unless they carry a thought
                // signature: Gemini can attach the signature to a part whose
                // visible text is empty and requires it echoed back; dropping
                // it breaks the reasoning chain.
                if is_blank(&text.text) && signature.is_none() {
                    continue;
                }
                parts.push(text_part(false, &text.text, signature));
            }
            AssistantContentBlock::Thinking(thinking) => {
                if same_model {
                    // An empty thinking block is dropped only when it carries
                    // no signature.
                    let signature = resolve_thought_signature(
                        same_model,
                        thinking.thinking_signature.as_deref(),
                    );
                    if is_blank(&thinking.thinking) && signature.is_none() {
                        continue;
                    }
                    parts.push(text_part(true, &thinking.thinking, signature));
                } else {
                    // Cross-provider/model: plain text without tags (so the
                    // model does not mimic them); the signature is unusable,
                    // and empty blocks stay dropped.
                    if is_blank(&thinking.thinking) {
                        continue;
                    }
                    parts.push(text_part(false, &thinking.thinking, None));
                }
            }
            AssistantContentBlock::ToolCall(tool_call) => {
                let signature =
                    resolve_thought_signature(same_model, tool_call.thought_signature.as_deref());
                let mut function_call = JsonObject::new();
                function_call.insert("name".into(), tool_call.name.clone().into());
                function_call.insert(
                    "args".into(),
                    JsonValue::Object(tool_call.arguments.clone()),
                );
                if requires_tool_call_id(&model.id) {
                    function_call.insert("id".into(), tool_call.id.clone().into());
                }
                let mut part = JsonObject::new();
                part.insert("functionCall".into(), JsonValue::Object(function_call));
                if let Some(signature) = signature {
                    part.insert("thoughtSignature".into(), signature.into());
                }
                parts.push(JsonValue::Object(part));
            }
        }
    }
    parts
}

fn convert_tool_result(model: &Model, result: &ToolResultMessage, contents: &mut Vec<JsonValue>) {
    let text_result = result
        .content
        .iter()
        .filter_map(|block| match block {
            UserContentBlock::Text(text) => Some(text.text.as_str()),
            UserContentBlock::Image(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n");
    let image_parts: Vec<JsonValue> = if model.input.contains(&Modality::Image) {
        result
            .content
            .iter()
            .filter_map(|block| match block {
                UserContentBlock::Image(image) => {
                    Some(inline_data_part(&image.mime_type, &image.data))
                }
                UserContentBlock::Text(_) => None,
            })
            .collect()
    } else {
        Vec::new()
    };
    let has_text = !text_result.is_empty();
    let has_images = !image_parts.is_empty();
    // Gemini 3+ supports multimodal function responses with images nested
    // inside functionResponse.parts; Claude and other non-Gemini models
    // behind Cloud Code Assist and Gemini < 3 still need a separate user
    // image turn.
    let multimodal_response = supports_multimodal_function_response(&model.id);

    // "output" key for success, "error" key for errors.
    let response_value = if has_text {
        sanitize_surrogates(&text_result).into_owned()
    } else if has_images {
        "(see attached image)".to_owned()
    } else {
        String::new()
    };
    let mut function_response = JsonObject::new();
    function_response.insert("name".into(), result.tool_name.clone().into());
    function_response.insert(
        "response".into(),
        if result.is_error {
            json!({ "error": response_value })
        } else {
            json!({ "output": response_value })
        },
    );
    if has_images && multimodal_response {
        function_response.insert("parts".into(), JsonValue::Array(image_parts.clone()));
    }
    if requires_tool_call_id(&model.id) {
        function_response.insert("id".into(), result.tool_call_id.clone().into());
    }
    let function_response_part =
        json!({ "functionResponse": JsonValue::Object(function_response) });

    // Cloud Code Assist API requires all function responses in a single user
    // turn: merge into the last content when it is a user turn with function
    // responses.
    let merge_target = contents
        .last_mut()
        .filter(|last| {
            last.get("role").and_then(JsonValue::as_str) == Some("user")
                && last
                    .get("parts")
                    .and_then(JsonValue::as_array)
                    .is_some_and(|parts| {
                        parts.iter().any(|part| {
                            part.get("functionResponse")
                                .is_some_and(|value| !value.is_null())
                        })
                    })
        })
        .and_then(|last| last.get_mut("parts"))
        .and_then(JsonValue::as_array_mut);
    match merge_target {
        Some(parts) => parts.push(function_response_part),
        None => contents.push(content("user", vec![function_response_part])),
    }

    // For Gemini < 3, add images in a separate user message.
    if has_images && !multimodal_response {
        let mut parts = vec![json!({ "text": "Tool result image:" })];
        parts.extend(image_parts);
        contents.push(content("user", parts));
    }
}
