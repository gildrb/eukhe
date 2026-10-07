//! Port of `test/github-copilot-anthropic.test.ts`. The mocked SDK
//! constructor and `beta.messages.create` become assertions on the request
//! captured by the `fetch` option: `apiKey: null` + `authToken` is the
//! `Authorization: Bearer` header without `X-Api-Key`, `defaultHeaders` are
//! the request headers, and `params.betas` is the `anthropic-beta` header.

mod anthropic_support;

use anthropic_support::{assert_match_object, collect, minimal_sse, mock_fetch, requests};
use eukhe_pi_ai::api::anthropic_messages::stream;
use eukhe_pi_ai::compat::get_model;
use eukhe_pi_ai::models::get_supported_thinking_levels;
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{Context, JsonValue, Model, TranscriptContext};
use serde_json::json;

fn context() -> TranscriptContext {
    let context: Context = serde_json::from_value(json!({
        "systemPrompt": "You are a helpful assistant.",
        "messages": [{ "role": "user", "content": "Hello", "timestamp": 1 }],
    }))
    .expect("context");
    normalize_context(context)
}

fn copilot_model(id: &str) -> Model {
    get_model("github-copilot", id).unwrap_or_else(|| panic!("github-copilot/{id}"))
}

fn model_json(model: &Model) -> JsonValue {
    serde_json::to_value(model).expect("model json")
}

fn levels(model: &Model) -> Vec<String> {
    get_supported_thinking_levels(model)
        .iter()
        .map(|level| {
            serde_json::to_value(level)
                .expect("level json")
                .as_str()
                .expect("level string")
                .to_owned()
        })
        .collect()
}

fn betas(header: Option<String>) -> Vec<String> {
    header
        .map(|value| {
            value
                .split(',')
                .map(|beta| beta.trim().to_owned())
                .collect()
        })
        .unwrap_or_default()
}

#[test]
fn applies_copilot_specific_adaptive_thinking_effort_overrides() {
    let opus47 = copilot_model("claude-opus-4.7");
    assert_match_object(
        &model_json(&opus47)["thinkingLevelMap"],
        &json!({ "minimal": "low", "xhigh": "xhigh", "max": "max" }),
    );
    assert!(levels(&opus47).contains(&"xhigh".to_owned()));
    assert!(levels(&opus47).contains(&"max".to_owned()));

    let opus5 = copilot_model("claude-opus-5");
    assert_eq!(opus5.api, "anthropic-messages");
    assert_eq!(opus5.context_window, 1_000_000);
    assert_match_object(
        &model_json(&opus5)["thinkingLevelMap"],
        &json!({ "minimal": "low", "xhigh": "xhigh", "max": "max" }),
    );
    assert!(levels(&opus5).contains(&"xhigh".to_owned()));
    assert!(levels(&opus5).contains(&"max".to_owned()));

    let opus55 = copilot_model("claude-opus-5.5");
    assert_eq!(opus55.api, "anthropic-messages");
    assert_eq!(opus55.context_window, 1_000_000);
    assert_eq!(levels(&opus55), ["low", "medium", "high", "xhigh", "max"]);

    let sonnet46 = copilot_model("claude-sonnet-4.6");
    assert_match_object(
        &model_json(&sonnet46)["thinkingLevelMap"],
        &json!({ "minimal": "low", "max": "max" }),
    );
    assert!(levels(&sonnet46).contains(&"max".to_owned()));
    assert!(!levels(&sonnet46).contains(&"xhigh".to_owned()));
}

#[tokio::test]
async fn uses_bearer_auth_copilot_headers_and_valid_anthropic_messages_payload() {
    let model = copilot_model("claude-sonnet-4.6");
    assert_eq!(model.api, "anthropic-messages");

    let (fetch, captured) = mock_fetch(minimal_sse());
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("tid_copilot_session_test_token".into());
    options.stream.request.fetch = Some(fetch);
    let _ = collect(stream(&model, &context(), options)).await;

    let request = requests(&captured).into_iter().next().expect("request");

    // Auth: apiKey null, authToken for Bearer
    assert_eq!(request.header("x-api-key"), None);
    assert_eq!(
        request.header("authorization").as_deref(),
        Some("Bearer tid_copilot_session_test_token")
    );

    // Copilot static headers from model.headers
    assert!(request
        .header("user-agent")
        .unwrap_or_default()
        .contains("GitHubCopilotChat"));
    assert_eq!(
        request.header("copilot-integration-id").as_deref(),
        Some("vscode-chat")
    );

    // Dynamic headers
    assert_eq!(request.header("x-initiator").as_deref(), Some("user"));
    assert_eq!(
        request.header("openai-intent").as_deref(),
        Some("conversation-edits")
    );

    // Payload is valid Anthropic Messages format
    let params = &request.body;
    assert!(!betas(request.header("anthropic-beta"))
        .contains(&"fine-grained-tool-streaming-2025-05-14".to_owned()));
    assert_eq!(params["model"], "claude-sonnet-4.6");
    assert_eq!(params["stream"], true);
    assert_eq!(params["max_tokens"], json!(model.max_tokens));
    assert!(params["messages"].is_array());
}

#[tokio::test]
async fn omits_interleaved_thinking_beta_for_adaptive_thinking_models() {
    let model = copilot_model("claude-sonnet-4.6");
    let (fetch, captured) = mock_fetch(minimal_sse());
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("tid_copilot_session_test_token".into());
    options.stream.request.fetch = Some(fetch);
    options
        .extra
        .insert("interleavedThinking".into(), json!(true));
    let _ = collect(stream(&model, &context(), options)).await;

    let request = requests(&captured).into_iter().next().expect("request");
    assert!(!betas(request.header("anthropic-beta"))
        .contains(&"interleaved-thinking-2025-05-14".to_owned()));
}
