//! The `@google/genai` request transforms for `generateContent` parameters:
//! `generateContentParametersToMldev` (Gemini API) and
//! `generateContentParametersToVertex` (Vertex AI), with the `tModel`,
//! `tContents`, `tContent`, `tTools`, and `tTool` normalizers.
//!
//! The transforms rebuild each object field by field, so the request body
//! has the SDK's key order (not the order of the parameters) and drops
//! fields the SDK does not know. Values the SDK passes through further
//! converters pi-ai never produces (`responseSchema`/`tSchema`,
//! `speechConfig`, `imageConfig`, safety settings, Google Search/Maps tool
//! configs, `parameters` without `$schema`/`processJsonSchema`) are copied
//! unchanged.

use eukhe_types::pi_ai::{JsonObject, JsonValue};
use serde_json::json;

use crate::utils::diagnostics::{ErrorObject, Thrown};

/// The transformed request: the `{model}` URL parameter and the JSON body.
pub(super) struct TransformedRequest {
    pub(super) model: String,
    pub(super) body: JsonObject,
}

/// Which backend's transform runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Backend {
    Mldev,
    Vertex,
}

fn error(message: impl Into<String>) -> Thrown {
    ErrorObject::new(message).thrown()
}

fn only_vertex(name: &str) -> Thrown {
    error(format!(
        "{name} parameter is only supported in Gemini Enterprise Agent Platform mode, not in Gemini Developer API mode."
    ))
}

fn only_mldev(name: &str) -> Thrown {
    error(format!(
        "{name} parameter is only supported in Gemini Developer API mode, not in Gemini Enterprise Agent Platform mode."
    ))
}

/// `getValueByPath(from, [key]) != null`.
fn present<'a>(from: &'a JsonObject, key: &str) -> Option<&'a JsonValue> {
    from.get(key).filter(|value| !value.is_null())
}

/// `getValueByPath(from, [key]) !== undefined`.
fn defined(from: &JsonObject, key: &str) -> bool {
    from.contains_key(key)
}

/// Copy `from[key]` to `to[key]` when it is not null/undefined.
fn copy(from: &JsonObject, to: &mut JsonObject, key: &str) {
    if let Some(value) = present(from, key) {
        to.insert(key.to_owned(), value.clone());
    }
}

/// `getValueByPath` on a non-object yields `undefined` for every key.
fn as_object(value: &JsonValue) -> JsonObject {
    value.as_object().cloned().unwrap_or_default()
}

/// `tModel(apiClient, model)`.
fn t_model(model: Option<&JsonValue>, backend: Backend) -> Result<String, Thrown> {
    let Some(model) = model
        .and_then(JsonValue::as_str)
        .filter(|model| !model.is_empty())
    else {
        return Err(error("model is required and must be a string"));
    };
    if model.contains("..") || model.contains('?') || model.contains('&') {
        return Err(error("invalid model parameter"));
    }
    Ok(match backend {
        Backend::Vertex => {
            if model.starts_with("publishers/")
                || model.starts_with("projects/")
                || model.starts_with("models/")
            {
                model.to_owned()
            } else if let Some((publisher, rest)) = model.split_once('/') {
                // `model.split('/', 2)`: the second element ends at the next `/`.
                let name = rest.split('/').next().unwrap_or_default();
                format!("publishers/{publisher}/models/{name}")
            } else {
                format!("publishers/google/models/{model}")
            }
        }
        Backend::Mldev => {
            if model.starts_with("models/") || model.starts_with("tunedModels/") {
                model.to_owned()
            } else {
                format!("models/{model}")
            }
        }
    })
}

/// `_isContent(origin)`.
fn is_content(value: &JsonValue) -> bool {
    value
        .as_object()
        .and_then(|object| object.get("parts"))
        .is_some_and(JsonValue::is_array)
}

/// `tPart(origin)`.
fn t_part(value: &JsonValue) -> Result<JsonValue, Thrown> {
    match value {
        JsonValue::Null => Err(error("PartUnion is required")),
        JsonValue::Object(_) | JsonValue::Array(_) => Ok(value.clone()),
        JsonValue::String(text) => Ok(json!({ "text": text })),
        JsonValue::Bool(_) => Err(error("Unsupported part type: boolean")),
        JsonValue::Number(_) => Err(error("Unsupported part type: number")),
    }
}

/// `tParts(origin)`.
fn t_parts(value: &JsonValue) -> Result<Vec<JsonValue>, Thrown> {
    match value {
        JsonValue::Null => Err(error("PartListUnion is required")),
        JsonValue::Array(items) if items.is_empty() => Err(error("PartListUnion is required")),
        JsonValue::Array(items) => items.iter().map(t_part).collect(),
        other => Ok(vec![t_part(other)?]),
    }
}

/// `tContent(origin)`.
fn t_content(value: &JsonValue) -> Result<JsonValue, Thrown> {
    if value.is_null() {
        return Err(error("ContentUnion is required"));
    }
    if is_content(value) {
        return Ok(value.clone());
    }
    Ok(json!({ "role": "user", "parts": t_parts(value)? }))
}

fn has_key(value: &JsonValue, key: &str) -> bool {
    value
        .as_object()
        .is_some_and(|object| object.contains_key(key))
}

/// `tContents(origin)`.
fn t_contents(value: &JsonValue) -> Result<Vec<JsonValue>, Thrown> {
    let items = match value {
        JsonValue::Null => return Err(error("contents are required")),
        JsonValue::Array(items) if items.is_empty() => {
            return Err(error("contents are required"));
        }
        JsonValue::Array(items) => items,
        other => {
            if has_key(other, "functionCall") || has_key(other, "functionResponse") {
                return Err(error(
                    "To specify functionCall or functionResponse parts, please wrap them in a Content object, specifying the role for them",
                ));
            }
            return Ok(vec![t_content(other)?]);
        }
    };
    let content_array = is_content(&items[0]);
    let mut result = Vec::new();
    let mut accumulated = Vec::new();
    for item in items {
        let item_is_content = is_content(item);
        if item_is_content != content_array {
            return Err(error(
                "Mixing Content and Parts is not supported, please group the parts into a the appropriate Content objects and specify the roles for them",
            ));
        }
        if item_is_content {
            result.push(item.clone());
        } else if has_key(item, "functionCall") || has_key(item, "functionResponse") {
            return Err(error(
                "To specify functionCall or functionResponse parts, please wrap them, and any other parts, in Content objects as appropriate, specifying the role for them",
            ));
        } else {
            accumulated.push(item.clone());
        }
    }
    if !content_array {
        result.push(json!({ "role": "user", "parts": t_parts(&JsonValue::Array(accumulated))? }));
    }
    Ok(result)
}

/// `blobToMldev` / `fileDataToMldev`: `displayName` is Vertex-only.
fn blob_or_file_to_mldev(value: &JsonValue, keys: [&str; 2]) -> Result<JsonValue, Thrown> {
    let from = as_object(value);
    let mut to = JsonObject::new();
    if keys[0] == "data" {
        copy(&from, &mut to, "data");
        if defined(&from, "displayName") {
            return Err(only_vertex("displayName"));
        }
        copy(&from, &mut to, "mimeType");
    } else {
        if defined(&from, "displayName") {
            return Err(only_vertex("displayName"));
        }
        copy(&from, &mut to, keys[0]);
        copy(&from, &mut to, keys[1]);
    }
    Ok(JsonValue::Object(to))
}

/// `functionCallToMldev`.
fn function_call_to_mldev(value: &JsonValue) -> Result<JsonValue, Thrown> {
    let from = as_object(value);
    let mut to = JsonObject::new();
    copy(&from, &mut to, "args");
    copy(&from, &mut to, "id");
    copy(&from, &mut to, "name");
    if defined(&from, "partialArgs") {
        return Err(only_vertex("partialArgs"));
    }
    if defined(&from, "willContinue") {
        return Err(only_vertex("willContinue"));
    }
    Ok(JsonValue::Object(to))
}

/// `partToMldev` / `partToVertex`.
fn part_to(value: &JsonValue, backend: Backend) -> Result<JsonValue, Thrown> {
    let from = as_object(value);
    let mut to = JsonObject::new();
    copy(&from, &mut to, "mediaResolution");
    match backend {
        Backend::Mldev => {
            copy(&from, &mut to, "toolCall");
            copy(&from, &mut to, "toolResponse");
        }
        Backend::Vertex => {
            if defined(&from, "toolCall") {
                return Err(only_mldev("toolCall"));
            }
            if defined(&from, "toolResponse") {
                return Err(only_mldev("toolResponse"));
            }
        }
    }
    copy(&from, &mut to, "audioTranscription");
    copy(&from, &mut to, "codeExecutionResult");
    copy(&from, &mut to, "executableCode");
    if let Some(file_data) = present(&from, "fileData") {
        let file_data = match backend {
            Backend::Mldev => blob_or_file_to_mldev(file_data, ["fileUri", "mimeType"])?,
            Backend::Vertex => file_data.clone(),
        };
        to.insert("fileData".into(), file_data);
    }
    if let Some(function_call) = present(&from, "functionCall") {
        let function_call = match backend {
            Backend::Mldev => function_call_to_mldev(function_call)?,
            Backend::Vertex => function_call.clone(),
        };
        to.insert("functionCall".into(), function_call);
    }
    copy(&from, &mut to, "functionResponse");
    if let Some(inline_data) = present(&from, "inlineData") {
        let inline_data = match backend {
            Backend::Mldev => blob_or_file_to_mldev(inline_data, ["data", "mimeType"])?,
            Backend::Vertex => inline_data.clone(),
        };
        to.insert("inlineData".into(), inline_data);
    }
    copy(&from, &mut to, "text");
    copy(&from, &mut to, "thought");
    copy(&from, &mut to, "thoughtSignature");
    copy(&from, &mut to, "videoMetadata");
    match backend {
        Backend::Mldev => copy(&from, &mut to, "partMetadata"),
        Backend::Vertex => {
            if defined(&from, "partMetadata") {
                return Err(only_mldev("partMetadata"));
            }
        }
    }
    copy(&from, &mut to, "mediaProcessing");
    Ok(JsonValue::Object(to))
}

/// `contentToMldev` / `contentToVertex`.
fn content_to(value: &JsonValue, backend: Backend) -> Result<JsonValue, Thrown> {
    let from = as_object(value);
    let mut to = JsonObject::new();
    if let Some(parts) = present(&from, "parts") {
        let parts = match parts {
            JsonValue::Array(items) => JsonValue::Array(
                items
                    .iter()
                    .map(|part| part_to(part, backend))
                    .collect::<Result<_, _>>()?,
            ),
            other => other.clone(),
        };
        to.insert("parts".into(), parts);
    }
    copy(&from, &mut to, "role");
    Ok(JsonValue::Object(to))
}

/// `tTool(tool)`: a `parameters`/`response` schema that declares `$schema`
/// moves to `parametersJsonSchema`/`responseJsonSchema`.
fn t_tool(tool: &JsonValue) -> JsonValue {
    let mut tool = tool.clone();
    let Some(declarations) = tool
        .get_mut("functionDeclarations")
        .and_then(JsonValue::as_array_mut)
    else {
        return tool;
    };
    for declaration in declarations.iter_mut().filter_map(JsonValue::as_object_mut) {
        for (schema_key, json_schema_key) in [
            ("parameters", "parametersJsonSchema"),
            ("response", "responseJsonSchema"),
        ] {
            let declares_schema = declaration
                .get(schema_key)
                .filter(|schema| is_js_truthy(schema))
                .and_then(JsonValue::as_object)
                .is_some_and(|schema| schema.contains_key("$schema"));
            let has_json_schema = declaration.get(json_schema_key).is_some_and(is_js_truthy);
            if declares_schema && !has_json_schema {
                if let Some(schema) = declaration.shift_remove(schema_key) {
                    declaration.insert(json_schema_key.to_owned(), schema);
                }
            }
        }
    }
    tool
}

fn is_js_truthy(value: &JsonValue) -> bool {
    match value {
        JsonValue::Null => false,
        JsonValue::Bool(flag) => *flag,
        JsonValue::Number(number) => number.as_f64().is_some_and(|n| n != 0.0 && !n.is_nan()),
        JsonValue::String(text) => !text.is_empty(),
        JsonValue::Array(_) | JsonValue::Object(_) => true,
    }
}

/// `toolToMldev` / `toolToVertex`.
fn tool_to(value: &JsonValue, backend: Backend) -> Result<JsonValue, Thrown> {
    let from = as_object(&t_tool(value));
    let mut to = JsonObject::new();
    match backend {
        Backend::Mldev => {
            if defined(&from, "retrieval") {
                return Err(only_vertex("retrieval"));
            }
        }
        Backend::Vertex => copy(&from, &mut to, "retrieval"),
    }
    copy(&from, &mut to, "googleMaps");
    copy(&from, &mut to, "mcpServers");
    copy(&from, &mut to, "codeExecution");
    copy(&from, &mut to, "computerUse");
    match backend {
        Backend::Mldev => {
            if defined(&from, "enterpriseWebSearch") {
                return Err(only_vertex("enterpriseWebSearch"));
            }
            if defined(&from, "exaAiSearch") {
                return Err(only_vertex("exaAiSearch"));
            }
        }
        Backend::Vertex => {
            copy(&from, &mut to, "enterpriseWebSearch");
            copy(&from, &mut to, "exaAiSearch");
        }
    }
    copy(&from, &mut to, "functionDeclarations");
    copy(&from, &mut to, "googleSearch");
    copy(&from, &mut to, "googleSearchRetrieval");
    match backend {
        Backend::Mldev => {
            if defined(&from, "parallelAiSearch") {
                return Err(only_vertex("parallelAiSearch"));
            }
        }
        Backend::Vertex => copy(&from, &mut to, "parallelAiSearch"),
    }
    copy(&from, &mut to, "urlContext");
    match backend {
        Backend::Mldev => copy(&from, &mut to, "fileSearch"),
        Backend::Vertex => {
            if defined(&from, "fileSearch") {
                return Err(only_mldev("fileSearch"));
            }
        }
    }
    Ok(JsonValue::Object(to))
}

/// `toolConfigToMldev` / `toolConfigToVertex`.
fn tool_config_to(value: &JsonValue, backend: Backend) -> Result<JsonValue, Thrown> {
    let from = as_object(value);
    let mut to = JsonObject::new();
    if let Some(config) = present(&from, "functionCallingConfig") {
        let config = match backend {
            Backend::Mldev => {
                let config = as_object(config);
                let mut mapped = JsonObject::new();
                copy(&config, &mut mapped, "allowedFunctionNames");
                copy(&config, &mut mapped, "mode");
                if defined(&config, "streamFunctionCallArguments") {
                    return Err(only_vertex("streamFunctionCallArguments"));
                }
                JsonValue::Object(mapped)
            }
            Backend::Vertex => config.clone(),
        };
        to.insert("functionCallingConfig".into(), config);
    }
    copy(&from, &mut to, "retrievalConfig");
    match backend {
        Backend::Mldev => copy(&from, &mut to, "includeServerSideToolInvocations"),
        Backend::Vertex => {
            if defined(&from, "includeServerSideToolInvocations") {
                return Err(only_mldev("includeServerSideToolInvocations"));
            }
        }
    }
    Ok(JsonValue::Object(to))
}

/// `tTools(tools)`.
fn t_tools(value: &JsonValue) -> Result<&Vec<JsonValue>, Thrown> {
    value
        .as_array()
        .ok_or_else(|| error("tools is required and must be an array of Tools"))
}

/// `generateContentConfigToMldev` / `generateContentConfigToVertex`: the
/// generation config, writing the top-level fields into `parent`.
fn generate_content_config_to(
    config: &JsonValue,
    parent: &mut JsonObject,
    backend: Backend,
) -> Result<JsonObject, Thrown> {
    let from = as_object(config);
    let mut to = JsonObject::new();
    copy(&from, parent, "serviceTier");
    if let Some(system_instruction) = present(&from, "systemInstruction") {
        parent.insert(
            "systemInstruction".into(),
            content_to(&t_content(system_instruction)?, backend)?,
        );
    }
    for key in [
        "temperature",
        "topP",
        "topK",
        "candidateCount",
        "maxOutputTokens",
        "stopSequences",
        "responseLogprobs",
        "logprobs",
        "presencePenalty",
        "frequencyPenalty",
        "seed",
        "responseMimeType",
        "responseSchema",
        "responseJsonSchema",
    ] {
        copy(&from, &mut to, key);
    }
    match backend {
        Backend::Mldev => {
            if defined(&from, "routingConfig") {
                return Err(only_vertex("routingConfig"));
            }
            if defined(&from, "modelSelectionConfig") {
                return Err(only_vertex("modelSelectionConfig"));
            }
        }
        Backend::Vertex => {
            copy(&from, &mut to, "routingConfig");
            if let Some(selection) = present(&from, "modelSelectionConfig") {
                to.insert("modelConfig".into(), selection.clone());
            }
        }
    }
    copy(&from, parent, "safetySettings");
    if let Some(tools) = present(&from, "tools") {
        let tools = t_tools(tools)?
            .iter()
            .map(|tool| tool_to(tool, backend))
            .collect::<Result<Vec<_>, _>>()?;
        parent.insert("tools".into(), JsonValue::Array(tools));
    }
    if let Some(tool_config) = present(&from, "toolConfig") {
        parent.insert("toolConfig".into(), tool_config_to(tool_config, backend)?);
    }
    match backend {
        Backend::Mldev => {
            if defined(&from, "labels") {
                return Err(only_vertex("labels"));
            }
        }
        Backend::Vertex => copy(&from, parent, "labels"),
    }
    copy(&from, parent, "cachedContent");
    copy(&from, &mut to, "responseModalities");
    copy(&from, &mut to, "mediaResolution");
    copy(&from, &mut to, "speechConfig");
    match backend {
        Backend::Mldev => {
            if defined(&from, "audioTimestamp") {
                return Err(only_vertex("audioTimestamp"));
            }
        }
        Backend::Vertex => copy(&from, &mut to, "audioTimestamp"),
    }
    copy(&from, &mut to, "thinkingConfig");
    copy(&from, &mut to, "audioTranscriptionConfig");
    copy(&from, &mut to, "imageConfig");
    match backend {
        Backend::Mldev => {
            copy(&from, &mut to, "enableEnhancedCivicAnswers");
            if defined(&from, "modelArmorConfig") {
                return Err(only_vertex("modelArmorConfig"));
            }
        }
        Backend::Vertex => {
            if defined(&from, "enableEnhancedCivicAnswers") {
                return Err(only_mldev("enableEnhancedCivicAnswers"));
            }
            copy(&from, parent, "modelArmorConfig");
        }
    }
    Ok(to)
}

fn generate_content_parameters_to(
    params: &JsonValue,
    backend: Backend,
) -> Result<TransformedRequest, Thrown> {
    let from = as_object(params);
    let model = match present(&from, "model") {
        Some(model) => t_model(Some(model), backend)?,
        None => String::new(),
    };
    let mut body = JsonObject::new();
    if let Some(contents) = present(&from, "contents") {
        let contents = t_contents(contents)?
            .iter()
            .map(|content| content_to(content, backend))
            .collect::<Result<Vec<_>, _>>()?;
        body.insert("contents".into(), JsonValue::Array(contents));
    }
    if let Some(config) = present(&from, "config") {
        let generation_config = generate_content_config_to(config, &mut body, backend)?;
        body.insert(
            "generationConfig".into(),
            JsonValue::Object(generation_config),
        );
    }
    Ok(TransformedRequest { model, body })
}

/// `generateContentParametersToMldev(apiClient, params)`.
pub(super) fn generate_content_parameters_to_mldev(
    params: &JsonValue,
) -> Result<TransformedRequest, Thrown> {
    generate_content_parameters_to(params, Backend::Mldev)
}

/// `generateContentParametersToVertex(apiClient, params)`.
pub(super) fn generate_content_parameters_to_vertex(
    params: &JsonValue,
) -> Result<TransformedRequest, Thrown> {
    generate_content_parameters_to(params, Backend::Vertex)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mldev_body_follows_sdk_key_order() {
        let params = json!({
            "model": "gemini-2.5-flash",
            "contents": [
                { "role": "model", "parts": [
                    { "functionCall": { "name": "bash", "args": { "c": 1 }, "id": "x" }, "thoughtSignature": "AAAA" },
                    { "inlineData": { "mimeType": "image/png", "data": "abc" } }
                ] }
            ],
            "config": {
                "temperature": 0.5,
                "maxOutputTokens": 10,
                "systemInstruction": "be nice",
                "tools": [{ "functionDeclarations": [{ "name": "bash", "description": "d", "parametersJsonSchema": {} }] }],
                "toolConfig": { "functionCallingConfig": { "mode": "AUTO" } },
                "thinkingConfig": { "includeThoughts": true }
            }
        });
        let request = generate_content_parameters_to_mldev(&params).unwrap();
        assert_eq!(request.model, "models/gemini-2.5-flash");
        assert_eq!(
            crate::utils::js::json_stringify(&JsonValue::Object(request.body)),
            json!({
                "contents": [{ "parts": [
                    { "functionCall": { "args": { "c": 1 }, "id": "x", "name": "bash" }, "thoughtSignature": "AAAA" },
                    { "inlineData": { "data": "abc", "mimeType": "image/png" } }
                ], "role": "model" }],
                "systemInstruction": { "parts": [{ "text": "be nice" }], "role": "user" },
                "tools": [{ "functionDeclarations": [{ "name": "bash", "description": "d", "parametersJsonSchema": {} }] }],
                "toolConfig": { "functionCallingConfig": { "mode": "AUTO" } },
                "generationConfig": { "temperature": 0.5, "maxOutputTokens": 10, "thinkingConfig": { "includeThoughts": true } }
            })
            .to_string()
        );
    }

    #[test]
    fn vertex_keeps_function_call_and_inline_data_order() {
        let params = json!({
            "model": "gemini-3-flash-preview",
            "contents": [{ "role": "model", "parts": [
                { "functionCall": { "name": "bash", "args": {}, "id": "x" } },
                { "inlineData": { "mimeType": "image/png", "data": "abc" } }
            ] }],
            "config": {}
        });
        let request = generate_content_parameters_to_vertex(&params).unwrap();
        assert_eq!(
            request.model,
            "publishers/google/models/gemini-3-flash-preview"
        );
        assert_eq!(
            JsonValue::Object(request.body).to_string(),
            json!({
                "contents": [{ "parts": [
                    { "functionCall": { "name": "bash", "args": {}, "id": "x" } },
                    { "inlineData": { "mimeType": "image/png", "data": "abc" } }
                ], "role": "model" }],
                "generationConfig": {}
            })
            .to_string()
        );
    }

    #[test]
    fn empty_contents_are_rejected() {
        let error = generate_content_parameters_to_mldev(&json!({
            "model": "gemini-2.5-flash",
            "contents": [],
            "config": {}
        }))
        .err()
        .unwrap();
        assert_eq!(error.to_string(), "contents are required");
    }
}
