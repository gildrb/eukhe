//! Port of `test/azure-openai-base-url.test.ts`.
//!
//! TS mocks the `openai` SDK's `AzureOpenAI` class and reads the client's
//! constructor `baseURL` / `defaultHeaders` and the `responses.create`
//! params. The Rust client has no constructor hook; the port observes the same
//! values on the request the client sends through a `fetch` mock: the URL is
//! `{baseURL}/responses?api-version=v1`, the headers carry `defaultHeaders`,
//! and the body is the params.

mod openai_responses_support;

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::api::azure_openai_responses::stream;
use eukhe_pi_ai::compat::get_model;
use eukhe_pi_ai::types::{
    JsonValue, Model, OnProviderStreamEvent, ProviderHeaders, ProviderStreamOptions, StopReason,
};
use eukhe_pi_ai::utils::pi_user_agent::get_pi_user_agent;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{AssistantMessage, Context, TranscriptContext};
use openai_responses_support::{mock_fetch, sse_events, CapturedRequest, MockResponse};
use serde_json::json;

const AZURE_ENV_KEYS: [&str; 4] = [
    "AZURE_OPENAI_BASE_URL",
    "AZURE_OPENAI_RESOURCE_NAME",
    "AZURE_OPENAI_API_VERSION",
    "AZURE_OPENAI_API_KEY",
];

/// Serializes process-env mutation within this binary (TS runs the cases of
/// a file sequentially).
static ENV_LOCK: tokio::sync::Mutex<()> = tokio::sync::Mutex::const_new(());

/// TS `beforeEach` / `afterEach`: clears the Azure env vars and restores the
/// originals on drop.
struct AzureEnv {
    originals: Vec<(&'static str, Option<std::ffi::OsString>)>,
    _lock: tokio::sync::MutexGuard<'static, ()>,
}

impl AzureEnv {
    async fn new() -> Self {
        let lock = ENV_LOCK.lock().await;
        let originals = AZURE_ENV_KEYS
            .iter()
            .map(|&key| (key, std::env::var_os(key)))
            .collect();
        for key in AZURE_ENV_KEYS {
            std::env::remove_var(key);
        }
        Self {
            originals,
            _lock: lock,
        }
    }
}

impl Drop for AzureEnv {
    fn drop(&mut self) {
        for (key, value) in &self.originals {
            match value {
                Some(value) => std::env::set_var(key, value),
                None => std::env::remove_var(key),
            }
        }
    }
}

fn context() -> TranscriptContext {
    normalize_context(context_value(&json!({})))
}

fn context_value(extra: &JsonValue) -> Context {
    let mut value = json!({
        "messages": [{ "role": "user", "content": "hello", "timestamp": now() }],
    });
    for (key, field) in extra.as_object().expect("object") {
        value[key] = field.clone();
    }
    serde_json::from_value(value).expect("context")
}

fn now() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock")
            .as_millis(),
    )
    .expect("epoch ms")
}

fn azure_model() -> Model {
    get_model("azure", "gpt-4o-mini").expect("azure/gpt-4o-mini")
}

/// Options with `apiKey: "test-api-key"` and the API-specific `extra` keys.
fn options(extra: &JsonValue) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions {
        extra: extra.as_object().expect("object").clone(),
        ..ProviderStreamOptions::default()
    };
    options.stream.request.api_key = Some("test-api-key".to_owned());
    options
}

/// The completed-response body the mock answers with.
fn completed_response() -> MockResponse {
    MockResponse::sse(sse_events(&[
        json!({ "type": "response.created", "sequence_number": 0, "response": { "id": "resp_azure" } }),
        json!({
            "type": "response.completed",
            "sequence_number": 1,
            "response": { "id": "resp_azure", "status": "completed" },
        }),
    ]))
}

/// Streams with `options` and returns the result and the single request.
async fn run(
    model: &Model,
    context: &TranscriptContext,
    mut options: ProviderStreamOptions,
) -> (AssistantMessage, Vec<CapturedRequest>) {
    let (fetch, captured) = mock_fetch(vec![completed_response()]);
    options.stream.request.fetch = Some(fetch);
    let result = stream(model, context, options).result().await;
    let requests = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    (result, requests)
}

fn single(requests: Vec<CapturedRequest>) -> CapturedRequest {
    assert_eq!(requests.len(), 1);
    requests.into_iter().next().expect("request")
}

/// TS `captureClientBaseUrl`: the request URL `{baseURL}/responses?api-version=v1`.
async fn capture_request_url(base_url: &str) -> String {
    std::env::set_var("AZURE_OPENAI_BASE_URL", base_url);
    let (_, requests) = run(&azure_model(), &context(), options(&json!({}))).await;
    single(requests).url
}

/// TS `captureClientHeaders`.
async fn capture_client_headers(headers: Option<ProviderHeaders>) -> CapturedRequest {
    let mut options = options(&json!({ "azureBaseUrl": "https://my-resource.openai.azure.com" }));
    options.stream.request.headers = headers;
    let (_, requests) = run(&azure_model(), &context(), options).await;
    single(requests)
}

async fn capture_params(extra: &JsonValue, session_id: Option<String>) -> JsonValue {
    let mut options = options(extra);
    options.stream.session_id = session_id;
    let (_, requests) = run(&azure_model(), &context(), options).await;
    single(requests).body
}

// --- azure base URL normalization ---

#[tokio::test]
async fn normalizes_cognitive_services_root_endpoints_to_openai_v1() {
    let _env = AzureEnv::new().await;
    let url =
        capture_request_url("https://marc-quicktests-resource.cognitiveservices.azure.com").await;
    assert_eq!(
        url,
        "https://marc-quicktests-resource.cognitiveservices.azure.com/openai/v1/responses?api-version=v1"
    );
}

#[tokio::test]
async fn normalizes_microsoft_foundry_root_endpoints_to_openai_v1() {
    let _env = AzureEnv::new().await;
    let url = capture_request_url("https://marc-quicktests-resource.ai.azure.com").await;
    assert_eq!(
        url,
        "https://marc-quicktests-resource.ai.azure.com/openai/v1/responses?api-version=v1"
    );
}

#[tokio::test]
async fn normalizes_azure_openai_root_endpoints_to_openai_v1() {
    let _env = AzureEnv::new().await;
    let url = capture_request_url("https://my-resource.openai.azure.com").await;
    assert_eq!(
        url,
        "https://my-resource.openai.azure.com/openai/v1/responses?api-version=v1"
    );
}

#[tokio::test]
async fn normalizes_openai_to_openai_v1() {
    let _env = AzureEnv::new().await;
    let url = capture_request_url("https://my-resource.cognitiveservices.azure.com/openai").await;
    assert_eq!(
        url,
        "https://my-resource.cognitiveservices.azure.com/openai/v1/responses?api-version=v1"
    );
}

#[tokio::test]
async fn preserves_openai_v1_endpoints() {
    let _env = AzureEnv::new().await;
    let url =
        capture_request_url("https://my-resource.cognitiveservices.azure.com/openai/v1").await;
    assert_eq!(
        url,
        "https://my-resource.cognitiveservices.azure.com/openai/v1/responses?api-version=v1"
    );
}

#[tokio::test]
async fn normalizes_openai_v1_responses_to_openai_v1() {
    let _env = AzureEnv::new().await;
    let url =
        capture_request_url("https://my-resource.services.ai.azure.com/openai/v1/responses").await;
    assert_eq!(
        url,
        "https://my-resource.services.ai.azure.com/openai/v1/responses?api-version=v1"
    );
}

#[tokio::test]
async fn preserves_explicit_non_azure_proxy_paths() {
    let _env = AzureEnv::new().await;
    let url = capture_request_url("https://my-proxy.example.com/v1").await;
    assert_eq!(
        url,
        "https://my-proxy.example.com/v1/responses?api-version=v1"
    );
}

#[tokio::test]
async fn strips_query_params_when_normalizing_azure_host_urls() {
    let _env = AzureEnv::new().await;
    let url =
        capture_request_url("https://my-resource.openai.azure.com/openai?api-version=2024-12-01")
            .await;
    assert_eq!(
        url,
        "https://my-resource.openai.azure.com/openai/v1/responses?api-version=v1"
    );
}

#[tokio::test]
async fn preserves_query_params_on_non_azure_proxy_urls() {
    let _env = AzureEnv::new().await;
    // The SDK appends the path to the preserved `baseURL` string, so the
    // kept query absorbs `/responses` (as the TS SDK's `buildURL` does).
    let url = capture_request_url("https://my-proxy.example.com/v1?custom=true").await;
    assert_eq!(
        url,
        "https://my-proxy.example.com/v1?custom=true%2Fresponses&api-version=v1"
    );
}

#[tokio::test]
async fn throws_on_invalid_urls() {
    let _env = AzureEnv::new().await;
    std::env::set_var("AZURE_OPENAI_BASE_URL", "not-a-url");
    let (result, _) = run(&azure_model(), &context(), options(&json!({}))).await;
    assert_eq!(result.stop_reason, StopReason::Error);
    let message = result.error_message.expect("errorMessage");
    assert!(
        message.contains("Invalid Azure OpenAI base URL"),
        "{message}"
    );
}

#[tokio::test]
async fn clamps_prompt_cache_key_to_openai_s_64_character_limit() {
    let _env = AzureEnv::new().await;
    let params = capture_params(
        &json!({ "azureBaseUrl": "https://my-resource.openai.azure.com" }),
        Some("x".repeat(67)),
    )
    .await;
    assert_eq!(params["prompt_cache_key"], json!("x".repeat(64)));
}

#[tokio::test]
async fn disables_server_side_response_storage() {
    let _env = AzureEnv::new().await;
    let params = capture_params(
        &json!({ "azureBaseUrl": "https://my-resource.openai.azure.com" }),
        None,
    )
    .await;
    assert_eq!(params["store"], json!(false));
}

#[tokio::test]
async fn honors_supports_strict_mode_false() {
    let _env = AzureEnv::new().await;
    let mut model_value = serde_json::to_value(azure_model()).expect("model json");
    let mut compat = model_value
        .get("compat")
        .cloned()
        .unwrap_or_else(|| json!({}));
    compat["supportsStrictMode"] = json!(false);
    model_value["compat"] = compat;
    let model: Model = serde_json::from_value(model_value).expect("model");

    let context = normalize_context(context_value(&json!({
        "tools": [{
            "name": "preferred",
            "description": "Preferred constrained tool",
            "parameters": {
                "type": "object",
                "properties": { "value": { "type": "string" } },
                "required": ["value"],
            },
            "constrainedSampling": { "type": "json_schema", "strict": "prefer" },
        }],
    })));
    let (_, requests) = run(
        &model,
        &context,
        options(&json!({ "azureBaseUrl": "https://my-resource.openai.azure.com" })),
    )
    .await;

    let params = single(requests).body;
    let tool = params["tools"][0].as_object().expect("tools[0]");
    assert!(!tool.contains_key("strict"), "{tool:?}");
}

#[tokio::test]
async fn builds_correct_default_url_from_azure_openai_resource_name() {
    let _env = AzureEnv::new().await;
    std::env::set_var("AZURE_OPENAI_RESOURCE_NAME", "my-resource");
    let (_, requests) = run(&azure_model(), &context(), options(&json!({}))).await;
    assert_eq!(
        single(requests).url,
        "https://my-resource.openai.azure.com/openai/v1/responses?api-version=v1"
    );
}

// --- azure provider stream events ---

#[tokio::test]
async fn forwards_parsed_events_in_order_before_normalizing_the_response() {
    let _env = AzureEnv::new().await;
    let stream_events = vec![
        json!({ "type": "response.created", "sequence_number": 0, "response": { "id": "resp_azure" } }),
        json!({
            "type": "response.completed",
            "sequence_number": 1,
            "response": { "id": "resp_azure", "status": "completed" },
        }),
    ];
    let model = azure_model();
    let received: Arc<Mutex<Vec<(JsonValue, Model)>>> = Arc::default();
    let sink = Arc::clone(&received);
    let on_event: OnProviderStreamEvent = Arc::new(move |event, event_model| {
        let sink = Arc::clone(&sink);
        let entry = (event.clone(), event_model.clone());
        Box::pin(async move {
            tokio::task::yield_now().await;
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(entry);
            Ok(())
        })
    });
    let (fetch, _) = mock_fetch(vec![MockResponse::sse(sse_events(&stream_events))]);
    let mut options = options(&json!({ "azureBaseUrl": "https://my-resource.openai.azure.com" }));
    options.stream.request.fetch = Some(fetch);
    options.stream.on_provider_stream_event = Some(on_event);
    let result = stream(&model, &context(), options).result().await;

    let received = received
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    let (events, event_models): (Vec<JsonValue>, Vec<Model>) = received.into_iter().unzip();
    assert_eq!(events, stream_events);
    assert_eq!(event_models, vec![model.clone(), model]);
    assert_eq!(result.stop_reason, StopReason::Stop);
    assert_eq!(result.response_id.as_deref(), Some("resp_azure"));
}

// --- azure user agent ---

#[tokio::test]
async fn uses_pi_s_user_agent_by_default() {
    let _env = AzureEnv::new().await;
    let request = capture_client_headers(None).await;
    assert_eq!(
        request.header("User-Agent").as_deref(),
        Some(get_pi_user_agent())
    );
}

#[tokio::test]
async fn lets_explicit_headers_override_the_default_user_agent() {
    let _env = AzureEnv::new().await;
    let mut headers = ProviderHeaders::new();
    headers.insert("User-Agent".to_owned(), Some("custom-agent".to_owned()));
    let request = capture_client_headers(Some(headers)).await;
    assert_eq!(
        request.header("User-Agent").as_deref(),
        Some("custom-agent")
    );
}
