//! Port of `test/anthropic-strict-tool-schema.test.ts`. `TypeBox` schemas are
//! written as the JSON `TypeBox` serializes.

mod anthropic_support;

use anthropic_support::{assert_match_object, capturing_on_payload, context, model, take_payload};
use eukhe_pi_ai::api::anthropic_messages::stream;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{CacheRetention, JsonValue};
use serde_json::json;

fn create_model() -> eukhe_types::pi_ai::Model {
    model(&json!({
        "id": "claude-opus-4-8",
        "name": "Claude Opus 4.8",
        "provider": "test-anthropic",
        "baseUrl": "http://127.0.0.1:9",
        "reasoning": true,
        "contextWindow": 200_000,
        "maxTokens": 32000,
        "compat": { "forceAdaptiveThinking": true, "supportsStrictTools": true },
    }))
}

fn create_tool(parameters: &JsonValue) -> JsonValue {
    json!({ "name": "lookup", "description": "Look up a value", "parameters": parameters })
}

fn create_strict_tool(parameters: &JsonValue) -> JsonValue {
    let mut tool = create_tool(parameters);
    tool["constrainedSampling"] = json!({ "type": "json_schema", "strict": "prefer" });
    tool
}

async fn capture_first_tool(tool: JsonValue) -> JsonValue {
    let (on_payload, captured) = capturing_on_payload();
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test-key".into());
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.on_payload = Some(on_payload);
    let context = context(&json!({
        "messages": [{ "role": "user", "content": "Use the tool", "timestamp": 1 }],
        "tools": [tool],
    }));
    let _ = stream(&create_model(), &context, options).result().await;
    take_payload(&captured)["tools"]
        .get(0)
        .cloned()
        .expect("Expected a tool in the captured Anthropic payload")
}

#[tokio::test]
async fn only_sends_the_full_input_schema_for_strict_json_schema_tools() {
    let legacy_parameters = json!({
        "additionalProperties": false,
        "title": "LookupInput",
        "type": "object",
        "properties": { "value": { "type": "string" } },
        "required": ["value"],
    });
    let legacy_tool = capture_first_tool(create_tool(&legacy_parameters)).await;
    assert_eq!(legacy_tool.get("strict"), None);
    assert_eq!(
        legacy_tool["input_schema"],
        json!({
            "type": "object",
            "properties": legacy_parameters["properties"],
            "required": legacy_parameters["required"],
        })
    );

    let strict_tool = capture_first_tool(create_strict_tool(&json!({
        "title": "StrictLookupInput",
        "type": "object",
        "properties": { "value": { "type": "string" }, "optional": { "type": "number" } },
        "required": ["value"],
    })))
    .await;
    assert_eq!(strict_tool.get("strict"), Some(&json!(true)));
    assert_match_object(
        &strict_tool["input_schema"],
        &json!({
            "additionalProperties": false,
            "required": ["value", "optional"],
            "properties": { "optional": { "anyOf": [{ "type": "number" }, { "type": "null" }] } },
            "title": "StrictLookupInput",
        }),
    );
}

// https://github.com/earendil-works/pi/issues/9953
#[tokio::test]
async fn sends_prefer_tools_non_strict_when_they_use_keywords_anthropic_strict_mode_rejects() {
    let unsupported_parameters = [
        json!({
            "type": "object",
            "properties": { "timeoutMs": { "minimum": 1, "maximum": 300_000, "type": "integer" } },
        }),
        json!({
            "type": "object",
            "properties": {
                "options": {
                    "type": "object",
                    "properties": { "tags": { "minItems": 2, "type": "array", "items": { "type": "string" } } },
                    "required": ["tags"],
                },
            },
            "required": ["options"],
        }),
        json!({
            "type": "object",
            "properties": { "expression": { "format": "regex", "type": "string" } },
            "required": ["expression"],
        }),
    ];
    for parameters in &unsupported_parameters {
        let tool = capture_first_tool(create_strict_tool(parameters)).await;
        assert_eq!(tool.get("strict"), None, "{parameters}");
    }

    let supported_tool = capture_first_tool(create_strict_tool(&json!({
        "type": "object",
        "properties": {
            "code": { "minLength": 1, "maxLength": 1000, "pattern": "^[a-z]+$", "type": "string" },
            "url": { "format": "uri", "type": "string" },
            "tags": { "minItems": 1, "type": "array", "items": { "type": "string" } },
        },
        "required": ["code", "url", "tags"],
    })))
    .await;
    assert_eq!(supported_tool.get("strict"), Some(&json!(true)));
}
