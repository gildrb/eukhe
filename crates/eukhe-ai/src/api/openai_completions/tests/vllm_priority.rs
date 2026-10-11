//! Port of `openai-completions-vllm-priority.test.ts`.

use serde_json::json;

use super::support::{capture_payload, context, model};
use crate::api::openai_completions::OpenAICompletionsOptions;
use crate::types::{JsonValue, Model};

/// `getModel("openai", "gpt-4o-mini")` without its `compat`, as an
/// `openai-completions` model, with `overrides` on top.
fn create_model(overrides: &JsonValue) -> Model {
    let catalog = crate::providers::openai_models::OPENAI_MODELS
        .get("gpt-4o-mini")
        .expect("gpt-4o-mini in the openai catalog");
    let mut value = serde_json::to_value(catalog).expect("serialize model");
    let object = value.as_object_mut().expect("model object");
    object.remove("compat");
    object.insert("api".to_owned(), json!("openai-completions"));
    for (key, field) in overrides.as_object().into_iter().flatten() {
        object.insert(key.clone(), field.clone());
    }
    model(value)
}

async fn capture_request(model: &Model) -> JsonValue {
    let mut options = OpenAICompletionsOptions::default();
    options.stream.request.api_key = Some("test-key".to_owned());
    capture_payload(
        model,
        &context(json!({
            "systemPrompt": "sys",
            "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }],
        })),
        options,
    )
    .await
}

#[tokio::test]
async fn sends_compat_vllm_priority_as_the_top_level_priority_request_field() {
    let payload =
        capture_request(&create_model(&json!({ "compat": { "vllmPriority": 10 } }))).await;

    assert_eq!(payload.get("priority"), Some(&json!(10)));
}

#[tokio::test]
async fn omits_priority_when_vllm_priority_is_not_set() {
    let payload = capture_request(&create_model(&json!({}))).await;

    assert_eq!(payload.get("priority"), None);
}
