//! Port of `test/anthropic-federation.test.ts`
//! (<https://github.com/earendil-works/pi/issues/10177>).
//!
//! The TS cases mock the SDK constructor and assert its `apiKey`, `authToken`,
//! `config`, and `defaultHeaders`. Here the SDK's federation is part of the
//! module, so those become assertions on the captured traffic: a
//! `/v1/oauth/token` exchange whose JSON body carries the `config` fields,
//! then a `/v1/messages` request with `Authorization: Bearer <federated
//! token>` and no `x-api-key`.

mod anthropic_support;

use std::collections::HashMap;
use std::io::Write as _;
use std::sync::Arc;

use anthropic_support::{context, federation_fetch, model, requests, Captured, CapturedRequest};
use eukhe_chord::context::AbortController;
use eukhe_pi_ai::api::anthropic_messages::stream;
use eukhe_pi_ai::auth::{ApiKeyResolveInput, AuthContext};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::anthropic::anthropic_provider;
use eukhe_pi_ai::types::{ProviderStreamOptions, SimpleStreamOptions};
use eukhe_types::pi_ai::{ProviderEnv, StopReason, TranscriptContext};
use futures::future::BoxFuture;
use serde_json::{json, Value};
use tempfile::NamedTempFile;

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

/// The identity token file (`/tmp/identity.jwt` in TS, where the SDK is
/// mocked and never reads it).
fn identity_token_file() -> NamedTempFile {
    let mut file = NamedTempFile::new().expect("temp file");
    file.write_all(b"header.payload.signature")
        .expect("write identity token");
    file
}

/// TS `federationEnv`.
fn federation_env(identity_token_file: &str) -> Vec<(String, String)> {
    vec![
        ("ANTHROPIC_FEDERATION_RULE_ID".into(), "fdrl_test".into()),
        ("ANTHROPIC_ORGANIZATION_ID".into(), "org-test".into()),
        ("ANTHROPIC_SERVICE_ACCOUNT_ID".into(), "svac_test".into()),
        (
            "ANTHROPIC_IDENTITY_TOKEN_FILE".into(),
            identity_token_file.into(),
        ),
    ]
}

fn without(env: &[(String, String)], name: &str) -> Vec<(String, String)> {
    env.iter().filter(|(key, _)| key != name).cloned().collect()
}

fn with(env: &[(String, String)], name: &str, value: &str) -> Vec<(String, String)> {
    let mut env = env.to_vec();
    env.push((name.into(), value.into()));
    env
}

fn env_json(env: &[(String, String)]) -> Value {
    Value::Object(
        env.iter()
            .map(|(name, value)| (name.clone(), Value::String(value.clone())))
            .collect(),
    )
}

fn provider_env(env: &[(String, String)]) -> ProviderEnv {
    env.iter().cloned().collect()
}

/// TS `resolveWithEnv`.
async fn resolve_with_env(env: &[(String, String)]) -> Value {
    let auth = anthropic_provider()
        .auth
        .api_key
        .as_ref()
        .expect("api-key auth")
        .resolve(ApiKeyResolveInput {
            ctx: Arc::new(TableAuthContext {
                env: env.iter().cloned().collect(),
            }),
            credential: None,
            signal: AbortController::new().signal(),
        })
        .await
        .expect("resolve");
    serde_json::to_value(auth).expect("json")
}

fn test_context() -> TranscriptContext {
    context(&json!({
        "systemPrompt": "System prompt.",
        "messages": [{ "role": "user", "content": "Hello", "timestamp": 1 }],
    }))
}

/// The SDK's `config` as sent in the token exchange: TS `expectedConfig`
/// plus the jwt-bearer grant fields.
fn expected_exchange_body(service_account_id: Option<&str>) -> Value {
    let mut body = json!({
        "grant_type": "urn:ietf:params:oauth:grant-type:jwt-bearer",
        "assertion": "header.payload.signature",
        "federation_rule_id": "fdrl_test",
        "organization_id": "org-test",
    });
    if let Some(id) = service_account_id {
        body["service_account_id"] = json!(id);
    }
    body
}

fn paths(captured: &Captured) -> Vec<String> {
    requests(captured)
        .iter()
        .map(CapturedRequest::path)
        .collect()
}

/// The single token exchange and the single messages request.
fn exchange_and_message(captured: &Captured) -> (CapturedRequest, CapturedRequest) {
    let all = requests(captured);
    assert_eq!(
        paths(captured),
        ["/v1/oauth/token", "/v1/messages"],
        "{all:?}"
    );
    (all[0].clone(), all[1].clone())
}

/// TS `expect(createParams?.betas ?? []).not.toContain("oauth-2025-04-20")`.
fn assert_no_oauth_beta(request: &CapturedRequest) {
    let betas = request.header("anthropic-beta").unwrap_or_default();
    assert!(
        !betas
            .split(',')
            .any(|beta| beta.trim() == "oauth-2025-04-20"),
        "{betas}"
    );
}

/// TS `apiKey: null`, `authToken: null`, federated `Authorization`.
fn assert_federated(message: &CapturedRequest) {
    assert_eq!(message.header("x-api-key"), None);
    assert_eq!(
        message.header("authorization").as_deref(),
        Some("Bearer federated-token")
    );
}

#[tokio::test]
async fn resolves_the_federation_variables_as_provider_env_with_no_request_auth() {
    let env = federation_env("/tmp/identity.jwt");
    assert_eq!(
        resolve_with_env(&env).await,
        json!({
            "auth": {},
            "env": env_json(&env),
            "source": "workload identity federation",
        })
    );
}

#[tokio::test]
async fn passes_anthropic_workspace_id_through_when_set() {
    let env = with(
        &federation_env("/tmp/identity.jwt"),
        "ANTHROPIC_WORKSPACE_ID",
        "wrkspc_test",
    );
    let result = resolve_with_env(&env).await;
    assert_eq!(
        result["env"]["ANTHROPIC_WORKSPACE_ID"],
        json!("wrkspc_test")
    );
}

#[tokio::test]
async fn is_not_configured_when_a_federation_variable_is_missing() {
    let partial = without(
        &federation_env("/tmp/identity.jwt"),
        "ANTHROPIC_IDENTITY_TOKEN_FILE",
    );
    assert_eq!(resolve_with_env(&partial).await, Value::Null);
}

#[tokio::test]
async fn treats_anthropic_service_account_id_as_optional_like_the_sdk() {
    let token = identity_token_file();
    let path = token.path().to_str().expect("utf-8 path").to_owned();
    let partial = without(&federation_env(&path), "ANTHROPIC_SERVICE_ACCOUNT_ID");
    assert_eq!(
        resolve_with_env(&partial).await,
        json!({
            "auth": {},
            "env": env_json(&partial),
            "source": "workload identity federation",
        })
    );

    let (fetch, captured) = federation_fetch();
    let mut options = ProviderStreamOptions::default();
    options.stream.request.env = Some(provider_env(&partial));
    options.stream.request.fetch = Some(fetch);
    stream(&model(&json!({})), &test_context(), options)
        .result()
        .await;

    let (exchange, message) = exchange_and_message(&captured);
    assert_eq!(exchange.body, expected_exchange_body(None));
    assert_federated(&message);
}

#[tokio::test]
async fn keeps_api_key_and_auth_token_precedence_over_federation() {
    let env = federation_env("/tmp/identity.jwt");
    assert_eq!(
        resolve_with_env(&with(&env, "ANTHROPIC_API_KEY", "api-key")).await,
        json!({
            "auth": { "apiKey": "api-key" },
            "source": "ANTHROPIC_API_KEY",
        })
    );
    assert_eq!(
        resolve_with_env(&with(&env, "ANTHROPIC_AUTH_TOKEN", "auth-token")).await,
        json!({
            "auth": { "headers": { "Authorization": "Bearer auth-token" } },
            "source": "ANTHROPIC_AUTH_TOKEN",
        })
    );
}

#[tokio::test]
async fn hands_the_sdk_a_federation_config_instead_of_a_key() {
    let token = identity_token_file();
    let path = token.path().to_str().expect("utf-8 path").to_owned();
    let env = federation_env(&path);
    let (fetch, captured) = federation_fetch();
    let mut options = ProviderStreamOptions::default();
    options.stream.request.env = Some(provider_env(&env));
    options.stream.request.fetch = Some(fetch);
    stream(&model(&json!({})), &test_context(), options)
        .result()
        .await;

    let (exchange, message) = exchange_and_message(&captured);
    assert_eq!(exchange.body, expected_exchange_body(Some("svac_test")));
    // No auth on the exchange itself; the federated token is the only
    // Authorization of the messages request.
    assert_eq!(exchange.header("authorization"), None);
    assert_eq!(exchange.header("x-api-key"), None);
    assert_federated(&message);
    assert_no_oauth_beta(&message);
}

#[tokio::test]
async fn threads_auth_context_federation_variables_through_models() {
    let token = identity_token_file();
    let path = token.path().to_str().expect("utf-8 path").to_owned();
    let env = federation_env(&path);
    let models = create_models(CreateModelsOptions {
        auth_context: Some(Arc::new(TableAuthContext {
            env: env.iter().cloned().collect(),
        })),
        ..CreateModelsOptions::default()
    });
    models.set_provider(anthropic_provider());

    let (fetch, captured) = federation_fetch();
    let mut options = SimpleStreamOptions::default();
    options.stream.request.fetch = Some(fetch);
    let context = serde_json::from_value(json!({
        "systemPrompt": "System prompt.",
        "messages": [{ "role": "user", "content": "Hello", "timestamp": 1 }],
    }))
    .expect("context");
    models
        .stream_simple(&model(&json!({})), context, options.into())
        .result()
        .await;

    let (exchange, message) = exchange_and_message(&captured);
    assert_eq!(exchange.body, expected_exchange_body(Some("svac_test")));
    assert_federated(&message);
}

#[tokio::test]
async fn lets_an_explicit_api_key_win_over_federation_env() {
    let token = identity_token_file();
    let path = token.path().to_str().expect("utf-8 path").to_owned();
    let (fetch, captured) = federation_fetch();
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("explicit-key".into());
    options.stream.request.env = Some(provider_env(&federation_env(&path)));
    options.stream.request.fetch = Some(fetch);
    stream(&model(&json!({})), &test_context(), options)
        .result()
        .await;

    // `config` undefined: no token exchange.
    assert_eq!(paths(&captured), ["/v1/messages"]);
    let message = &requests(&captured)[0];
    assert_eq!(message.header("x-api-key").as_deref(), Some("explicit-key"));
    assert_eq!(message.header("authorization"), None);
}

#[tokio::test]
async fn does_not_federate_other_anthropic_messages_providers() {
    let token = identity_token_file();
    let path = token.path().to_str().expect("utf-8 path").to_owned();
    let kimi = model(&json!({
        "provider": "kimi-coding",
        "baseUrl": "https://api.kimi.com/coding",
    }));
    let (fetch, captured) = federation_fetch();
    let mut options = ProviderStreamOptions::default();
    options.stream.request.env = Some(provider_env(&federation_env(&path)));
    options.stream.request.fetch = Some(fetch);
    let message = stream(&kimi, &test_context(), options).result().await;

    assert_eq!(message.stop_reason, StopReason::Error);
    // The SDK client was never constructed: nothing was sent.
    assert!(requests(&captured).is_empty());
}
