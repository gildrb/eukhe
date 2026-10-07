//! Port of `test/anthropic-auth-token.test.ts`: the cases that check what
//! the `anthropic-messages` module builds and sends (the provider auth
//! resolution cases live in `anthropic_auth_token.rs`).
//!
//! The TS fake SDK's constructor options (`apiKey`, `authToken`,
//! `defaultHeaders`) become assertions on the captured request headers
//! (`x-api-key`, `Authorization`, `User-Agent`); its `create` params become
//! the `onPayload` params (which still carry `betas`).

mod anthropic_support;

use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};

use anthropic_support::{minimal_sse, mock_fetch, model, requests, Captured, CapturedRequest};
use eukhe_pi_ai::api::anthropic_messages::stream;
use eukhe_pi_ai::auth::AuthContext;
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::anthropic::anthropic_provider;
use eukhe_pi_ai::types::{OnPayload, ProviderStreamOptions, SimpleStreamOptions};
use eukhe_pi_ai::utils::pi_user_agent::get_pi_user_agent;
use eukhe_types::pi_ai::{Context, JsonValue, Model, ProviderHeaders};
use futures::future::BoxFuture;
use serde_json::json;

/// `{ env: async (name) => table[name], fileExists: async () => false }`.
struct TableAuthContext {
    env: HashMap<String, String>,
}

impl AuthContext for TableAuthContext {
    fn env<'a>(&'a self, name: &'a str) -> BoxFuture<'a, Option<String>> {
        let value = self.env.get(name).cloned();
        Box::pin(async move { value })
    }
    fn file_exists<'a>(&'a self, _path: &'a str) -> BoxFuture<'a, bool> {
        Box::pin(async { false })
    }
}

fn models_with_env(name: &str, value: &str) -> eukhe_pi_ai::models::Models {
    let models = create_models(CreateModelsOptions {
        auth_context: Some(Arc::new(TableAuthContext {
            env: HashMap::from([(name.to_owned(), value.to_owned())]),
        })),
        ..CreateModelsOptions::default()
    });
    models.set_provider(anthropic_provider());
    models
}

fn raw_context() -> Context {
    serde_json::from_value(json!({
        "systemPrompt": "System prompt.",
        "messages": [{ "role": "user", "content": "Hello", "timestamp": 1 }],
    }))
    .expect("context")
}

fn anthropic_model() -> Model {
    model(&json!({}))
}

fn kimi_coding_model() -> Model {
    model(&json!({
        "id": "kimi-for-coding",
        "name": "Kimi For Coding",
        "provider": "kimi-coding",
        "baseUrl": "https://api.kimi.com/coding",
    }))
}

fn headers(entries: &[(&str, Option<&str>)]) -> ProviderHeaders {
    entries
        .iter()
        .map(|(name, value)| ((*name).to_owned(), value.map(str::to_owned)))
        .collect()
}

/// The params the fake SDK's `create` would see (TS `mockState.createParams`).
type Params = Arc<Mutex<Option<JsonValue>>>;

fn capture_params() -> (OnPayload<Model>, Params) {
    let params: Params = Arc::default();
    let sink = Arc::clone(&params);
    let on_payload: OnPayload<Model> = Arc::new(move |payload, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        Box::pin(async { Ok(None) })
    });
    (on_payload, params)
}

fn params(params: &Params) -> JsonValue {
    params
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("payload captured")
}

fn only_request(captured: &Captured) -> CapturedRequest {
    let all = requests(captured);
    assert_eq!(all.len(), 1, "{all:?}");
    all[0].clone()
}

/// `expect(createParams?.betas ?? []).not.toContain("oauth-2025-04-20")`.
fn assert_no_oauth_beta(params: &JsonValue) {
    let betas = params.get("betas").cloned().unwrap_or_else(|| json!([]));
    assert!(
        !betas
            .as_array()
            .expect("betas array")
            .contains(&json!("oauth-2025-04-20")),
        "{betas}"
    );
}

/// `expect(createParams?.system).toEqual([expect.objectContaining({ text: "System prompt." })])`.
fn assert_system_prompt(params: &JsonValue) {
    let system = params["system"].as_array().expect("system blocks");
    assert_eq!(system.len(), 1, "{system:?}");
    assert_eq!(system[0]["text"], json!("System prompt."));
}

async fn run_stream(
    model: &Model,
    mut options: ProviderStreamOptions,
) -> (CapturedRequest, JsonValue) {
    let (fetch, captured) = mock_fetch(minimal_sse());
    let (on_payload, captured_params) = capture_params();
    options.stream.request.fetch = Some(fetch);
    options.stream.request.on_payload = Some(on_payload);
    let context = eukhe_pi_ai::utils::transcript::normalize_context(raw_context());
    stream(model, &context, options).result().await;
    (only_request(&captured), params(&captured_params))
}

async fn run_models(
    models: &eukhe_pi_ai::models::Models,
    mut options: SimpleStreamOptions,
) -> (CapturedRequest, JsonValue) {
    let (fetch, captured) = mock_fetch(minimal_sse());
    let (on_payload, captured_params) = capture_params();
    options.stream.request.fetch = Some(fetch);
    options.stream.request.on_payload = Some(on_payload);
    models
        .stream_simple(&anthropic_model(), raw_context(), options.into())
        .result()
        .await;
    (only_request(&captured), params(&captured_params))
}

// --- Anthropic auth token env ---

#[tokio::test]
async fn uses_authorization_headers_without_oauth_mode_request_shaping() {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.headers =
        Some(headers(&[("Authorization", Some("Bearer gateway-token"))]));
    let (request, params) = run_stream(&anthropic_model(), options).await;

    assert_eq!(request.header("x-api-key"), None);
    assert_eq!(
        request.header("authorization").as_deref(),
        Some("Bearer gateway-token")
    );
    assert_no_oauth_beta(&params);
    assert_system_prompt(&params);
}

#[tokio::test]
async fn threads_auth_context_anthropic_auth_token_through_request_headers() {
    let models = models_with_env("ANTHROPIC_AUTH_TOKEN", "ctx-token");
    let (request, params) = run_models(&models, SimpleStreamOptions::default()).await;

    assert_eq!(request.header("x-api-key"), None);
    assert_eq!(
        request.header("authorization").as_deref(),
        Some("Bearer ctx-token")
    );
    assert_no_oauth_beta(&params);
    assert_system_prompt(&params);
}

#[tokio::test]
async fn preserves_oauth_request_shaping_for_anthropic_oauth_token() {
    let models = models_with_env("ANTHROPIC_OAUTH_TOKEN", "sk-ant-oat-test");
    let (request, params) = run_models(&models, SimpleStreamOptions::default()).await;

    // `apiKey: null`, `authToken: "sk-ant-oat-test"`.
    assert_eq!(request.header("x-api-key"), None);
    assert_eq!(
        request.header("authorization").as_deref(),
        Some("Bearer sk-ant-oat-test")
    );
    assert!(
        params["betas"]
            .as_array()
            .expect("betas")
            .contains(&json!("oauth-2025-04-20")),
        "{params}"
    );
}

#[tokio::test]
async fn lets_explicit_request_headers_override_anthropic_auth_token() {
    let models = models_with_env("ANTHROPIC_AUTH_TOKEN", "ctx-token");
    let mut options = SimpleStreamOptions::default();
    options.stream.request.headers =
        Some(headers(&[("Authorization", Some("Bearer explicit-token"))]));
    let (request, _) = run_models(&models, options).await;

    assert_eq!(
        request.header("authorization").as_deref(),
        Some("Bearer explicit-token")
    );
}

// --- Anthropic-compatible user agents ---

#[tokio::test]
async fn uses_pis_user_agent_by_default_for_anthropic_messages_requests() {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("anthropic-key".into());
    let (request, _) = run_stream(&anthropic_model(), options).await;

    assert_eq!(
        request.header("user-agent").as_deref(),
        Some(get_pi_user_agent())
    );
}

#[tokio::test]
async fn lets_explicit_headers_override_the_default_anthropic_messages_user_agent() {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("kimi-key".into());
    options.stream.request.headers = Some(headers(&[("User-Agent", Some("custom-client"))]));
    let (request, _) = run_stream(&kimi_coding_model(), options).await;

    assert_eq!(
        request.header("user-agent").as_deref(),
        Some("custom-client")
    );
}

#[tokio::test]
async fn preserves_explicit_anthropic_beta_header_replacement() {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("anthropic-key".into());
    options.stream.request.headers = Some(headers(&[("anthropic-beta", Some("custom-beta"))]));
    let (request, params) = run_stream(&anthropic_model(), options).await;

    assert_eq!(params["betas"], json!(["custom-beta"]));
    assert_eq!(
        request.header("anthropic-beta").as_deref(),
        Some("custom-beta")
    );
}

#[tokio::test]
async fn preserves_explicit_anthropic_beta_header_suppression() {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("anthropic-key".into());
    options.stream.request.headers = Some(headers(&[("anthropic-beta", None)]));
    let (request, params) = run_stream(&anthropic_model(), options).await;

    assert_eq!(params.get("betas"), None, "{params}");
    assert_eq!(request.header("anthropic-beta"), None);
}
