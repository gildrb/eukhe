//! Port of `test/openai-responses-tool-result-images.test.ts`: tool result
//! images stay inside `function_call_output` on Responses APIs.
//!
//! Every case talks to a live provider. TS resolves the Copilot and Codex
//! keys with `test/oauth.ts` (stored OAuth credentials or env); here keys come
//! from the provider's env API key variables (`getEnvApiKey`).

use std::sync::{Arc, Mutex, PoisonError};

use base64::Engine as _;
use eukhe_pi_ai::compat::{complete, get_model};
use eukhe_pi_ai::env_api_keys::get_env_api_key;
use eukhe_pi_ai::types::{OnPayload, ProviderStreamOptions};
use eukhe_types::pi_ai::{
    AssistantContentBlock, Context, JsonValue, Message, Modality, Model, StopReason,
};
use futures::FutureExt;
use serde_json::json;

fn now() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis(),
    )
    .unwrap_or(u64::MAX)
}

fn get_image_tool() -> JsonValue {
    json!({
        "name": "get_circle_with_description",
        "description": "Returns a red circle image with a short text description.",
        "parameters": { "type": "object", "properties": {} },
    })
}

fn has_azure_openai_credentials() -> bool {
    let set = |name: &str| std::env::var(name).is_ok_and(|value| !value.is_empty());
    set("AZURE_OPENAI_API_KEY")
        && (set("AZURE_OPENAI_BASE_URL") || set("AZURE_OPENAI_RESOURCE_NAME"))
}

fn resolve_azure_deployment_name(model_id: &str) -> Option<String> {
    let map_value = std::env::var("AZURE_OPENAI_DEPLOYMENT_NAME_MAP").ok()?;
    map_value.split(',').find_map(|entry| {
        let mut parts = entry.trim().splitn(2, '=');
        let id = parts.next()?.trim();
        let deployment = parts.next()?.trim();
        (!id.is_empty() && !deployment.is_empty() && id == model_id).then(|| deployment.to_owned())
    })
}

fn options(api_key: Option<String>, extra: &JsonValue) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = api_key;
    options.extra = serde_json::from_value(extra.clone()).expect("extra");
    options
}

fn text_of(content: &[AssistantContentBlock]) -> String {
    content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join(" ")
}

async fn verify_tool_result_images_stay_in_function_call_output(
    model: &Model,
    options: ProviderStreamOptions,
) {
    if !model.input.contains(&Modality::Image) {
        println!(
            "Skipping responses tool-result image test. Model {} does not support images.",
            model.id
        );
        return;
    }

    let image_path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/red-circle.png");
    let base64_image =
        base64::engine::general_purpose::STANDARD.encode(std::fs::read(image_path).expect("image"));
    let tool_text = "A red circle with a diameter of 100 pixels.";

    let mut context: Context = serde_json::from_value(json!({
        "systemPrompt": "You are a helpful assistant that always uses the provided tool when asked.",
        "messages": [{
            "role": "user",
            "content": "Call get_circle_with_description, then describe both the tool text and the image. Mention the color and shape.",
            "timestamp": now(),
        }],
        "tools": [get_image_tool()],
    }))
    .expect("context");

    let first_response = complete(model, context.clone(), options.clone())
        .await
        .expect("first response");
    assert_eq!(
        first_response.stop_reason,
        StopReason::ToolUse,
        "Error: {:?}",
        first_response.error_message
    );

    let tool_call = first_response
        .content
        .iter()
        .find_map(|block| match block {
            AssistantContentBlock::ToolCall(call) => Some(call.clone()),
            _ => None,
        })
        .expect("Expected tool call");

    context
        .messages
        .push(Message::Assistant(first_response.clone()));
    context.messages.push(
        serde_json::from_value(json!({
            "role": "toolResult",
            "toolCallId": tool_call.id,
            "toolName": tool_call.name,
            "content": [
                { "type": "text", "text": tool_text },
                { "type": "image", "data": base64_image, "mimeType": "image/png" },
            ],
            "isError": false,
            "timestamp": now(),
        }))
        .expect("tool result"),
    );

    let captured_payload: Arc<Mutex<Option<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&captured_payload);
    let on_payload: OnPayload<Model> = Arc::new(move |payload, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        async { Ok(None) }.boxed()
    });
    let mut second_options = options;
    second_options.stream.request.on_payload = Some(on_payload);
    let second_response = complete(model, context, second_options)
        .await
        .expect("second response");

    assert_eq!(
        second_response.stop_reason,
        StopReason::Stop,
        "Error: {:?}",
        second_response.error_message
    );
    assert!(second_response
        .error_message
        .as_deref()
        .is_none_or(str::is_empty));

    let response_payload = captured_payload
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_function_call_output_payload(response_payload.as_ref(), tool_text);

    let response_text = text_of(&second_response.content).to_lowercase();
    assert!(response_text.contains("red"));
    assert!(response_text.contains("circle"));
}

/// The second request keeps the tool result text and image inside
/// `function_call_output`, with no later user message.
fn assert_function_call_output_payload(payload: Option<&JsonValue>, tool_text: &str) {
    let response_input = payload
        .and_then(|payload| payload["input"].as_array())
        .expect("Expected payload with input array");

    let function_call_output_index = response_input
        .iter()
        .position(|item| item["type"] == "function_call_output")
        .expect("Expected function_call_output item");
    let output_items = response_input[function_call_output_index]["output"]
        .as_array()
        .expect("Expected function_call_output output to be a content array");

    let text_item = output_items
        .iter()
        .find(|item| item["type"] == "input_text");
    let image_item = output_items
        .iter()
        .find(|item| item["type"] == "input_image");
    let (Some(text_item), Some(image_item)) = (text_item, image_item) else {
        panic!("Expected both input_text and input_image in function_call_output");
    };

    assert!(text_item["text"]
        .as_str()
        .expect("text")
        .contains(tool_text));
    assert!(image_item["image_url"]
        .as_str()
        .expect("image_url")
        .starts_with("data:image/png;base64,"));

    let later_user_messages = response_input[function_call_output_index + 1..]
        .iter()
        .filter(|item| item["role"] == "user")
        .count();
    assert_eq!(later_user_messages, 0);
}

/// `OpenAI` Responses Provider (gpt-5-mini)
#[tokio::test]
#[ignore = "needs OPENAI_API_KEY; run with --ignored"]
async fn openai_responses_should_send_tool_result_images_in_function_call_output() {
    let model = get_model("openai", "gpt-5-mini").expect("model");
    verify_tool_result_images_stay_in_function_call_output(
        &model,
        options(None, &json!({ "reasoningEffort": "low" })),
    )
    .await;
}

/// Azure `OpenAI` Responses Provider (gpt-4o-mini)
#[tokio::test]
#[ignore = "needs AZURE_OPENAI_API_KEY and AZURE_OPENAI_BASE_URL or AZURE_OPENAI_RESOURCE_NAME; run with --ignored"]
async fn azure_openai_responses_should_send_tool_result_images_in_function_call_output() {
    assert!(
        has_azure_openai_credentials(),
        "missing Azure OpenAI credentials"
    );
    let model = get_model("azure", "gpt-4o-mini").expect("model");
    let azure_options = resolve_azure_deployment_name(&model.id)
        .map_or_else(|| json!({}), |name| json!({ "azureDeploymentName": name }));
    verify_tool_result_images_stay_in_function_call_output(&model, options(None, &azure_options))
        .await;
}

/// GitHub Copilot Responses Provider (gpt-5-mini)
#[tokio::test]
#[ignore = "needs a GitHub Copilot token (COPILOT_GITHUB_TOKEN/GH_TOKEN/GITHUB_TOKEN); run with --ignored"]
async fn github_copilot_responses_should_send_tool_result_images_in_function_call_output() {
    let model = get_model("github-copilot", "gpt-5-mini").expect("model");
    let token = get_env_api_key("github-copilot", None).expect("github-copilot token");
    verify_tool_result_images_stay_in_function_call_output(
        &model,
        options(Some(token), &json!({ "reasoningEffort": "low" })),
    )
    .await;
}

/// `OpenAI` Codex Responses Provider (gpt-5.5)
#[tokio::test]
#[ignore = "needs an OpenAI Codex token in env; run with --ignored"]
async fn openai_codex_responses_should_send_tool_result_images_in_function_call_output() {
    let model = get_model("openai-codex", "gpt-5.5").expect("model");
    let token = get_env_api_key("openai-codex", None).expect("openai-codex token");
    verify_tool_result_images_stay_in_function_call_output(
        &model,
        options(Some(token), &json!({ "reasoningEffort": "low" })),
    )
    .await;
}
