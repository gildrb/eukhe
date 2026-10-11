//! Ports of `google-shared-convert-tools`, `google-shared-gemini3-unsigned-tool-call`,
//! `google-shared-image-tool-result-routing`, `google-shared-retry`,
//! `google-shared-signed-empty-blocks`, `google-thinking-signature`, and the
//! `resolveGoogleThinkingLevel` case of `google-thinking-level-map`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use eukhe_types::pi_ai::{JsonValue, Model, ThinkingLevel, Tool, TranscriptContext};
use serde_json::json;

use super::test_support::{assistant, context, model};
use super::*;

// ---------------------------------------------------------------------------
// google-shared-convert-tools.test.ts
// ---------------------------------------------------------------------------

fn make_tool(parameters: JsonValue) -> Tool {
    Tool {
        name: "test_tool".to_owned(),
        description: "A test tool".to_owned(),
        parameters: parameters.into(),
        constrained_sampling: None,
    }
}

fn first_declaration(result: Option<&[JsonValue]>) -> &JsonValue {
    &result.expect("tools")[0]["functionDeclarations"][0]
}

#[test]
fn strips_json_schema_meta_keys_from_parameters_when_use_parameters_true() {
    let tools = [make_tool(json!({
        "$schema": "http://json-schema.org/draft-07/schema#",
        "$id": "urn:bash-tool",
        "$comment": "A bash tool for demonstration",
        "$defs": { "commandDef": { "type": "string" } },
        "definitions": { "legacyDef": { "type": "number" } },
        "type": "object",
        "properties": { "command": { "type": "string" } },
        "required": ["command"]
    }))];
    let result = convert_tools(&tools, ToolSchemaField::Parameters, true).unwrap();
    let declaration = first_declaration(result.as_deref());
    assert_eq!(
        declaration["parameters"],
        json!({
            "type": "object",
            "properties": { "command": { "type": "string" } },
            "required": ["command"]
        })
    );
    for key in ["$schema", "$id", "$comment", "$defs", "definitions"] {
        assert!(declaration["parameters"].get(key).is_none());
    }
}

#[test]
fn recursively_strips_nested_json_schema_meta_keys() {
    let tools = [make_tool(json!({
        "$schema": "http://json-schema.org/draft-07/schema#",
        "type": "object",
        "properties": {
            "deep": {
                "$schema": "http://json-schema.org/draft-07/schema#",
                "$id": "urn:nested",
                "type": "string"
            }
        }
    }))];
    let result = convert_tools(&tools, ToolSchemaField::Parameters, true).unwrap();
    assert_eq!(
        first_declaration(result.as_deref())["parameters"],
        json!({ "type": "object", "properties": { "deep": { "type": "string" } } })
    );
}

#[test]
fn preserves_ref_while_stripping_meta_keys() {
    let tools = [make_tool(json!({
        "$schema": "http://json-schema.org/draft-07/schema#",
        "type": "object",
        "properties": { "refProp": { "$ref": "#/$defs/someDef", "type": "string" } }
    }))];
    let result = convert_tools(&tools, ToolSchemaField::Parameters, true).unwrap();
    assert_eq!(
        first_declaration(result.as_deref())["parameters"],
        json!({
            "type": "object",
            "properties": { "refProp": { "$ref": "#/$defs/someDef", "type": "string" } }
        })
    );
}

#[test]
fn does_not_mutate_the_original_tool_parameters_object() {
    let original = json!({
        "$schema": "http://json-schema.org/draft-07/schema#",
        "type": "object",
        "properties": { "command": { "type": "string" } },
        "required": ["command"]
    });
    let tools = [make_tool(original.clone())];
    convert_tools(&tools, ToolSchemaField::Parameters, true).unwrap();
    assert_eq!(tools[0].parameters.json(), &original);
}

#[test]
fn preserves_schema_in_parameters_json_schema_when_use_parameters_false() {
    let parameters = json!({
        "$schema": "http://json-schema.org/draft-07/schema#",
        "type": "object",
        "properties": { "command": { "type": "string" } },
        "required": ["command"]
    });
    let tools = [make_tool(parameters.clone())];
    let result = convert_tools(&tools, ToolSchemaField::ParametersJsonSchema, true).unwrap();
    assert_eq!(
        first_declaration(result.as_deref())["parametersJsonSchema"],
        parameters
    );
}

#[test]
fn handles_tools_without_schema_gracefully() {
    let parameters = json!({
        "type": "object",
        "properties": { "path": { "type": "string" } },
        "required": ["path"]
    });
    let tools = [make_tool(parameters.clone())];
    let result = convert_tools(&tools, ToolSchemaField::Parameters, true).unwrap();
    assert_eq!(
        first_declaration(result.as_deref())["parameters"],
        parameters
    );
}

#[test]
fn uses_validated_function_calling_for_strict_tools_on_gemini_3() {
    let mut tool = make_tool(json!({ "type": "object", "properties": {} }));
    tool.constrained_sampling =
        serde_json::from_value(json!({ "type": "json_schema", "strict": "require" })).unwrap();

    assert!(supports_google_strict_tool_sampling(
        "gemini-3.1-pro-preview"
    ));
    assert!(!supports_google_strict_tool_sampling("gemini-2.5-pro"));
    assert_eq!(
        resolve_google_function_calling_mode(std::slice::from_ref(&tool), None, true).unwrap(),
        Some(FunctionCallingConfigMode::Validated)
    );
    assert_eq!(FunctionCallingConfigMode::Validated.as_str(), "VALIDATED");
    let error = resolve_google_function_calling_mode(&[tool], None, false).unwrap_err();
    assert!(error
        .to_string()
        .contains("Tool \"test_tool\" requires JSON-schema constrained sampling"));
}

#[test]
fn returns_undefined_for_empty_tool_list() {
    assert_eq!(
        convert_tools(&[], ToolSchemaField::ParametersJsonSchema, true).unwrap(),
        None
    );
    assert_eq!(
        convert_tools(&[], ToolSchemaField::Parameters, true).unwrap(),
        None
    );
}

// ---------------------------------------------------------------------------
// google-shared-gemini3-unsigned-tool-call.test.ts
// ---------------------------------------------------------------------------

fn gemini3_model(api: &str, provider: &str, id: &str) -> Model {
    model(&json!({
        "id": id,
        "name": "Gemini 3 Pro Preview",
        "api": api,
        "provider": provider,
        "baseUrl": "https://example.com"
    }))
}

fn unsigned_context(
    api: &str,
    provider: &str,
    id: &str,
    thought_signature: Option<&str>,
) -> TranscriptContext {
    let mut first_call = json!({
        "type": "toolCall", "id": "call_1", "name": "bash", "arguments": { "command": "echo hi" }
    });
    if let Some(signature) = thought_signature {
        first_call["thoughtSignature"] = json!(signature);
    }
    context(&json!({
        "messages": [
            { "role": "user", "content": "Hi", "timestamp": 0 },
            assistant(api, provider, id, &json!([
                first_call,
                { "type": "toolCall", "id": "call_2", "name": "bash", "arguments": { "command": "ls -la" } }
            ])),
            { "role": "toolResult", "toolCallId": "call_1", "toolName": "bash",
              "content": [{ "type": "text", "text": "hi" }], "isError": false, "timestamp": 0 },
            { "role": "toolResult", "toolCallId": "call_2", "toolName": "bash",
              "content": [{ "type": "text", "text": "files" }], "isError": false, "timestamp": 0 }
        ]
    }))
}

fn all_parts(contents: &[JsonValue]) -> Vec<&JsonValue> {
    contents
        .iter()
        .flat_map(|content| content["parts"].as_array().into_iter().flatten())
        .collect()
}

fn model_turn(contents: &[JsonValue]) -> &JsonValue {
    contents
        .iter()
        .find(|content| content["role"] == "model")
        .expect("model turn")
}

fn function_call_parts(turn: &JsonValue) -> Vec<&JsonValue> {
    turn["parts"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|part| part.get("functionCall").is_some())
        .collect()
}

#[test]
fn preserves_tool_call_ids_via_history() {
    for model in [
        gemini3_model("google-generative-ai", "google", "gemini-3-pro-preview"),
        gemini3_model("google-generative-ai", "google", "gemini-3.6-flash"),
        gemini3_model("google-vertex", "google-vertex", "gemini-3-pro-preview"),
    ] {
        let contents = convert_messages(
            &model,
            &unsigned_context(&model.api, &model.provider, &model.id, None),
        );
        let parts = all_parts(&contents);
        let call_ids: Vec<&JsonValue> = parts
            .iter()
            .filter_map(|part| part.get("functionCall").and_then(|call| call.get("id")))
            .collect();
        let response_ids: Vec<&JsonValue> = parts
            .iter()
            .filter_map(|part| part.get("functionResponse").and_then(|r| r.get("id")))
            .collect();
        assert_eq!(
            call_ids,
            [&json!("call_1"), &json!("call_2")],
            "{}",
            model.id
        );
        assert_eq!(
            response_ids,
            [&json!("call_1"), &json!("call_2")],
            "{}",
            model.id
        );
    }
}

#[test]
fn does_not_add_skip_thought_signature_validator_for_unsigned_google_gen_ai_tool_calls() {
    let model = gemini3_model("google-generative-ai", "google", "gemini-3-pro-preview");
    let contents = convert_messages(
        &model,
        &unsigned_context(&model.api, &model.provider, "other-model", None),
    );
    let turn = model_turn(&contents);
    let calls = function_call_parts(turn);
    assert_eq!(calls.len(), 2);
    assert!(calls[0].get("thoughtSignature").is_none());
    assert!(calls[1].get("thoughtSignature").is_none());
    assert!(!turn
        .to_string()
        .contains("skip_thought_signature_validator"));
    let historical = turn["parts"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|part| {
            part.get("text")
                .and_then(JsonValue::as_str)
                .is_some_and(|text| text.contains("Historical context"))
        })
        .count();
    assert_eq!(historical, 0);
}

#[test]
fn does_not_add_skip_thought_signature_validator_for_unsigned_vertex_tool_calls() {
    let model = gemini3_model("google-vertex", "google-vertex", "gemini-3-pro-preview");
    let contents = convert_messages(
        &model,
        &unsigned_context(&model.api, &model.provider, &model.id, None),
    );
    let turn = model_turn(&contents);
    let calls = function_call_parts(turn);
    assert_eq!(calls.len(), 2);
    assert!(calls[0].get("thoughtSignature").is_none());
    assert!(calls[1].get("thoughtSignature").is_none());
    assert!(!turn
        .to_string()
        .contains("skip_thought_signature_validator"));
}

#[test]
fn preserves_valid_thought_signature_when_present_for_the_same_provider_and_model() {
    let model = gemini3_model("google-generative-ai", "google", "gemini-3-pro-preview");
    let valid = "AAAAAAAAAAAAAAAAAAAAAA==";
    let contents = convert_messages(
        &model,
        &unsigned_context(&model.api, &model.provider, &model.id, Some(valid)),
    );
    let calls = function_call_parts(model_turn(&contents));
    assert_eq!(calls.len(), 2);
    assert_eq!(calls[0]["thoughtSignature"], json!(valid));
    assert!(calls[1].get("thoughtSignature").is_none());
}

#[test]
fn does_not_add_a_thought_signature_for_non_gemini_3_models() {
    let model = gemini3_model("google-generative-ai", "google", "gemini-2.5-flash");
    let contents = convert_messages(
        &model,
        &unsigned_context(&model.api, &model.provider, "other-model", None),
    );
    let calls = function_call_parts(model_turn(&contents));
    assert_eq!(calls.len(), 2);
    assert!(calls
        .iter()
        .all(|part| part["functionCall"].get("id").is_none()));
    assert!(calls
        .iter()
        .all(|part| part.get("thoughtSignature").is_none()));
    let responses: Vec<&JsonValue> = all_parts(&contents)
        .into_iter()
        .filter(|part| part.get("functionResponse").is_some())
        .collect();
    assert_eq!(responses.len(), 2);
    assert!(responses
        .iter()
        .all(|part| part["functionResponse"].get("id").is_none()));
}

#[test]
fn requires_tool_call_id_by_model() {
    for (expected, model_id) in [
        (false, "gemini-2.5-flash"),
        (true, "gemini-3.6-flash"),
        (true, "claude-sonnet-4-5"),
        (true, "gpt-oss-120b"),
    ] {
        assert_eq!(requires_tool_call_id(model_id), expected, "{model_id}");
    }
}

// ---------------------------------------------------------------------------
// google-shared-image-tool-result-routing.test.ts
// ---------------------------------------------------------------------------

fn image_model(id: &str) -> Model {
    model(&json!({
        "id": id,
        "api": "google-generative-ai",
        "provider": "google",
        "baseUrl": "https://example.com",
        "input": ["text", "image"]
    }))
}

fn image_context(model: &Model) -> TranscriptContext {
    context(&json!({
        "messages": [
            { "role": "user", "content": "read the files", "timestamp": 0 },
            assistant(&model.api, &model.provider, &model.id, &json!([
                { "type": "toolCall", "id": "call_a", "name": "read", "arguments": { "path": "a.txt" } },
                { "type": "toolCall", "id": "call_img", "name": "read", "arguments": { "path": "image.png" } },
                { "type": "toolCall", "id": "call_b", "name": "read", "arguments": { "path": "b.txt" } }
            ])),
            { "role": "toolResult", "toolCallId": "call_a", "toolName": "read",
              "content": [{ "type": "text", "text": "alpha text" }], "isError": false, "timestamp": 0 },
            { "role": "toolResult", "toolCallId": "call_img", "toolName": "read",
              "content": [{ "type": "image", "data": "abc", "mimeType": "image/png" }], "isError": false, "timestamp": 0 },
            { "role": "toolResult", "toolCallId": "call_b", "toolName": "read",
              "content": [{ "type": "text", "text": "beta text" }], "isError": false, "timestamp": 0 }
        ]
    }))
}

#[test]
fn keeps_separate_synthetic_image_turn_for_gemini_2_google_api_models() {
    let model = image_model("gemini-2.5-flash");
    let contents = convert_messages(&model, &image_context(&model));
    assert_eq!(contents.len(), 5);
    assert!(contents[2]["parts"]
        .as_array()
        .unwrap()
        .iter()
        .all(|part| part.get("functionResponse").is_some()));
    assert_eq!(contents[3]["parts"][0]["text"], json!("Tool result image:"));
    assert!(contents[3]["parts"][1].get("inlineData").is_some());
    assert!(contents[4]["parts"][0].get("functionResponse").is_some());
}

#[test]
fn nests_image_tool_results_for_gemini_3_google_api_models() {
    let model = image_model("gemini-3-pro-preview");
    let contents = convert_messages(&model, &image_context(&model));
    assert_eq!(contents.len(), 3);
    let parts = contents[2]["parts"].as_array().unwrap();
    assert_eq!(parts.len(), 3);
    let image_response = &parts[1]["functionResponse"];
    assert_eq!(image_response["parts"].as_array().unwrap().len(), 1);
    assert!(image_response["parts"][0].get("inlineData").is_some());
}

// ---------------------------------------------------------------------------
// google-shared-retry.test.ts
// ---------------------------------------------------------------------------

/// Shaped like `@google/genai`'s `ApiError`: has `status`, but no `headers`.
fn google_api_error(status: u16) -> Thrown {
    ErrorObject {
        status: Some(Some(JsonValue::from(status))),
        ..ErrorObject::new(format!("got status: {status}"))
    }
    .thrown()
}

#[tokio::test(start_paused = true)]
async fn retries_a_headers_less_sdk_error_with_a_retryable_status() {
    let calls = Arc::new(AtomicUsize::new(0));
    let counter = Arc::clone(&calls);
    let result = retry_google_request(
        move || {
            let attempt = counter.fetch_add(1, Ordering::SeqCst);
            async move {
                if attempt == 0 {
                    Err(google_api_error(429))
                } else {
                    Ok("ok")
                }
            }
        },
        Some(&GoogleRetryOptions {
            max_retries: Some(1),
            ..GoogleRetryOptions::default()
        }),
    )
    .await;
    assert_eq!(result.unwrap(), "ok");
    assert_eq!(calls.load(Ordering::SeqCst), 2);
}

#[tokio::test]
async fn does_not_retry_when_max_retries_is_unset() {
    let calls = Arc::new(AtomicUsize::new(0));
    let counter = Arc::clone(&calls);
    let error = retry_google_request(
        move || {
            counter.fetch_add(1, Ordering::SeqCst);
            async { Err::<&str, _>(google_api_error(429)) }
        },
        None,
    )
    .await
    .unwrap_err();
    let object = error.downcast_ref::<ErrorObject>().unwrap();
    assert_eq!(object.message, "got status: 429");
    assert_eq!(object.status, Some(Some(JsonValue::from(429))));
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

#[tokio::test]
async fn does_not_retry_a_non_retryable_status() {
    let calls = Arc::new(AtomicUsize::new(0));
    let counter = Arc::clone(&calls);
    let error = retry_google_request(
        move || {
            counter.fetch_add(1, Ordering::SeqCst);
            async { Err::<&str, _>(google_api_error(400)) }
        },
        Some(&GoogleRetryOptions {
            max_retries: Some(2),
            ..GoogleRetryOptions::default()
        }),
    )
    .await
    .unwrap_err();
    assert_eq!(error.to_string(), "got status: 400");
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

// ---------------------------------------------------------------------------
// google-shared-signed-empty-blocks.test.ts
// ---------------------------------------------------------------------------

const VALID_SIG: &str = "AAAAAAAAAAAAAAAAAAAAAA==";

fn signed_model() -> Model {
    gemini3_model("google-generative-ai", "google", "gemini-3-pro-preview")
}

fn signed_context(source_model: &str, content: &JsonValue) -> TranscriptContext {
    context(&json!({
        "messages": [
            { "role": "user", "content": "Hi", "timestamp": 0 },
            assistant("google-generative-ai", "google", source_model, content)
        ]
    }))
}

fn signed_parts(contents: &[JsonValue]) -> Vec<&JsonValue> {
    model_turn(contents)["parts"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|part| part.get("thoughtSignature") == Some(&json!(VALID_SIG)))
        .collect()
}

#[test]
fn keeps_a_signed_empty_thinking_block_so_its_signature_is_echoed_back() {
    let model = signed_model();
    let contents = convert_messages(
        &model,
        &signed_context(
            &model.id,
            &json!([
                { "type": "thinking", "thinking": "", "thinkingSignature": VALID_SIG },
                { "type": "toolCall", "id": "call_1", "name": "bash", "arguments": { "command": "ls" } }
            ]),
        ),
    );
    let signed = signed_parts(&contents);
    assert_eq!(signed.len(), 1);
    assert_eq!(signed[0]["thought"], json!(true));
}

#[test]
fn keeps_a_signed_empty_text_block_the_same_way() {
    let model = signed_model();
    let contents = convert_messages(
        &model,
        &signed_context(
            &model.id,
            &json!([
                { "type": "text", "text": "", "textSignature": VALID_SIG },
                { "type": "toolCall", "id": "call_1", "name": "bash", "arguments": { "command": "ls" } }
            ]),
        ),
    );
    assert_eq!(signed_parts(&contents).len(), 1);
}

#[test]
fn still_drops_unsigned_empty_blocks() {
    let model = signed_model();
    let contents = convert_messages(
        &model,
        &signed_context(
            &model.id,
            &json!([
                { "type": "thinking", "thinking": "" },
                { "type": "text", "text": "   " },
                { "type": "toolCall", "id": "call_1", "name": "bash", "arguments": { "command": "ls" } }
            ]),
        ),
    );
    let parts = model_turn(&contents)["parts"].as_array().unwrap();
    assert_eq!(parts.len(), 1);
    assert!(parts[0].get("functionCall").is_some());
}

#[test]
fn still_drops_signed_empty_blocks_from_a_different_provider_model() {
    let model = signed_model();
    let contents = convert_messages(
        &model,
        &signed_context(
            "other-model",
            &json!([
                { "type": "thinking", "thinking": "", "thinkingSignature": VALID_SIG },
                { "type": "text", "text": "", "textSignature": VALID_SIG },
                { "type": "toolCall", "id": "call_1", "name": "bash", "arguments": { "command": "ls" } }
            ]),
        ),
    );
    let turn = model_turn(&contents);
    let parts = turn["parts"].as_array().unwrap();
    assert_eq!(parts.len(), 1);
    assert!(parts[0].get("functionCall").is_some());
    assert!(!turn.to_string().contains(VALID_SIG));
}

// ---------------------------------------------------------------------------
// google-thinking-signature.test.ts
// ---------------------------------------------------------------------------

#[test]
fn treats_part_thought_true_as_thinking() {
    assert!(is_thinking_part(Some(&json!(true)), None));
    assert!(is_thinking_part(
        Some(&json!(true)),
        Some("opaque-signature")
    ));
}

#[test]
fn does_not_treat_thought_signature_alone_as_thinking() {
    assert!(!is_thinking_part(None, Some("opaque-signature")));
    assert!(!is_thinking_part(
        Some(&json!(false)),
        Some("opaque-signature")
    ));
}

#[test]
fn does_not_treat_empty_missing_signatures_as_thinking_if_thought_is_not_set() {
    assert!(!is_thinking_part(None, None));
    assert!(!is_thinking_part(Some(&json!(false)), Some("")));
}

#[test]
fn preserves_the_existing_signature_when_subsequent_deltas_omit_thought_signature() {
    let first = retain_thought_signature(None, Some("sig-1"));
    assert_eq!(first.as_deref(), Some("sig-1"));
    let second = retain_thought_signature(first, None);
    assert_eq!(second.as_deref(), Some("sig-1"));
    let third = retain_thought_signature(second, Some(""));
    assert_eq!(third.as_deref(), Some("sig-1"));
}

#[test]
fn updates_the_signature_when_a_new_non_empty_signature_arrives() {
    assert_eq!(
        retain_thought_signature(Some("sig-1".to_owned()), Some("sig-2")).as_deref(),
        Some("sig-2")
    );
}

// ---------------------------------------------------------------------------
// google-thinking-level-map.test.ts (resolveGoogleThinkingLevel)
// ---------------------------------------------------------------------------

fn level_map_model(map: &JsonValue) -> Model {
    model(&json!({
        "id": "gemini-3.7-flash",
        "api": "google-generative-ai",
        "provider": "test-google",
        "baseUrl": "https://example.invalid/v1beta",
        "thinkingLevelMap": map,
        "maxTokens": 4096
    }))
}

#[test]
fn exhaustively_resolves_supported_logical_levels_and_mapping_values() {
    for (level, expected) in [
        (ThinkingLevel::Minimal, ResolvedGoogleThinkingLevel::Minimal),
        (ThinkingLevel::Low, ResolvedGoogleThinkingLevel::Low),
        (ThinkingLevel::Medium, ResolvedGoogleThinkingLevel::Medium),
        (ThinkingLevel::High, ResolvedGoogleThinkingLevel::High),
    ] {
        assert_eq!(
            resolve_google_thinking_level(&level_map_model(&json!({})), level).unwrap(),
            expected
        );
    }

    for (mapped, expected) in [
        ("minimal", ResolvedGoogleThinkingLevel::Minimal),
        ("low", ResolvedGoogleThinkingLevel::Low),
        ("medium", ResolvedGoogleThinkingLevel::Medium),
        ("high", ResolvedGoogleThinkingLevel::High),
        ("MINIMAL", ResolvedGoogleThinkingLevel::Minimal),
        ("LOW", ResolvedGoogleThinkingLevel::Low),
        ("MEDIUM", ResolvedGoogleThinkingLevel::Medium),
        ("HIGH", ResolvedGoogleThinkingLevel::High),
    ] {
        let model = level_map_model(&json!({ "high": mapped, "xhigh": mapped, "max": mapped }));
        for level in [
            ThinkingLevel::High,
            ThinkingLevel::Xhigh,
            ThinkingLevel::Max,
        ] {
            assert_eq!(
                resolve_google_thinking_level(&model, level).unwrap(),
                expected
            );
        }
    }

    let invalid = level_map_model(&json!({ "xhigh": "extreme" }));
    assert_eq!(
        resolve_google_thinking_level(&invalid, ThinkingLevel::Xhigh)
            .unwrap_err()
            .to_string(),
        "Unsupported Google thinking level mapping for test-google/gemini-3.7-flash: xhigh -> extreme"
    );
    assert_eq!(
        resolve_google_thinking_level(&level_map_model(&json!({})), ThinkingLevel::Max)
            .unwrap_err()
            .to_string(),
        "Unsupported Google thinking level mapping for test-google/gemini-3.7-flash: max -> undefined"
    );
}
