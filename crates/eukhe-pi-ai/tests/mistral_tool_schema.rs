//! Port of `test/mistral-tool-schema.test.ts`.

mod mistral_support;

use eukhe_pi_ai::compat::{complete, get_model};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_types::pi_ai::{Context, StopReason};
use mistral_support::{capture_payload, payload_of};
use serde_json::json;

/// TS: "strips `TypeBox` symbol keys before the SDK validates tool schemas".
/// Rust JSON schemas carry no symbol keys; the port checks the strict tool
/// payload (strict flag and plain nested parameters) and the request error.
#[tokio::test]
async fn strips_typebox_symbol_keys_before_the_sdk_validates_tool_schemas() {
    let mut model = get_model("mistral", "devstral-medium-latest").expect("model");
    model.base_url = "http://127.0.0.1:9".into();
    let context: Context = serde_json::from_value(json!({
        "messages": [{ "role": "user", "content": "Hi", "timestamp": 1 }],
        "tools": [{
            "name": "inspect_schema",
            "description": "Inspect the schema",
            "parameters": {
                "type": "object",
                "properties": {
                    "nested": {
                        "type": "object",
                        "properties": { "value": { "type": "string" } },
                        "required": ["value"],
                    },
                },
                "required": ["nested"],
            },
            "constrainedSampling": { "type": "json_schema", "strict": "require" },
        }],
    }))
    .expect("context");
    let (on_payload, store) = capture_payload(|_| None);
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("fake-key".into());
    options.stream.request.on_payload = Some(on_payload);

    let response = complete(&model, context, options).await.expect("dispatch");

    let payload = payload_of(&store);
    let tools = payload["tools"].as_array().expect("tools");
    assert_eq!(tools.len(), 1);
    assert_eq!(tools[0]["function"]["strict"], json!(true));
    let parameters = &tools[0]["function"]["parameters"];
    assert!(parameters.is_object());
    let properties = &parameters["properties"];
    assert!(properties.is_object());
    assert!(properties["nested"].is_object());
    assert_eq!(response.stop_reason, StopReason::Error);
    assert!(!response
        .error_message
        .as_deref()
        .unwrap_or_default()
        .contains("Input validation failed"));
}
