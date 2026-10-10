//! Shared helpers of the `eukhe-pi-ai` integration tests (ports of the TS
//! test fixtures).

#![allow(dead_code)] // Each test binary uses a different subset of the helpers.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::api::ProviderStreams;
use eukhe_pi_ai::auth::{
    ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, AuthCheck, AuthResult, Credential,
    CredentialStore, LoginOptions, ModelAuth, OAuthAuth, OAuthCredential, ProviderAuth,
    ProviderAuthInteraction,
};
use eukhe_pi_ai::models::{GetModelsFn, Provider, RefreshModelsFn};
use eukhe_pi_ai::types::StreamOptions;
use eukhe_pi_ai::utils::diagnostics::{ErrorObject, Thrown};
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, Context, DoneReason, Message,
    Modality, Model, ModelCost, StopReason, TextContent, Usage, UserContent, UserMessage,
};
use futures::future::BoxFuture;

/// `Date.now()`.
#[must_use]
pub fn now() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|duration| duration.as_millis())
            .unwrap_or_default(),
    )
    .unwrap_or_default()
}

/// `Date.now()` as a JS number.
#[must_use]
#[allow(clippy::cast_precision_loss)] // Epoch milliseconds stay below 2^53.
pub fn now_f64() -> f64 {
    now() as f64
}

/// A thrown `Error(message)`.
#[must_use]
pub fn error(message: &str) -> Thrown {
    ErrorObject::new(message).thrown()
}

#[must_use]
pub fn test_model(provider: &str, id: &str) -> Model {
    serde_json::from_value(serde_json::json!({
        "id": id,
        "name": id,
        "api": "test-api",
        "provider": provider,
        "baseUrl": "https://example.test/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 10000,
        "maxTokens": 1000,
    }))
    .expect("test model")
}

#[must_use]
pub fn done_message(model: &Model, text: &str) -> AssistantMessage {
    AssistantMessage {
        content: vec![AssistantContentBlock::Text(TextContent::new(text))],
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: StopReason::Stop,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: now(),
        duration_ms: None,
    }
}

/// A user message with string content.
#[must_use]
pub fn user(text: &str) -> Message {
    Message::User(UserMessage {
        content: UserContent::Text(text.to_owned()),
        timestamp: now(),
    })
}

/// `{ messages: [{ role: "user", content: "hi" }] }`.
#[must_use]
pub fn context() -> Context {
    Context {
        system_prompt: None,
        messages: vec![user("hi")],
        tools: None,
    }
}

/// One recorded provider dispatch.
#[derive(Debug, Clone)]
pub struct ProviderCall {
    pub model: Model,
    pub options: StreamOptions,
}

pub type Calls = Arc<Mutex<Vec<ProviderCall>>>;

#[must_use]
pub fn calls() -> Calls {
    Arc::new(Mutex::new(Vec::new()))
}

#[must_use]
pub fn recorded(calls: &Calls) -> Vec<ProviderCall> {
    calls.lock().unwrap_or_else(PoisonError::into_inner).clone()
}

/// A stream that starts and finishes with "ok".
#[must_use]
pub fn ok_stream(model: &Model) -> AssistantMessageEventStream {
    let stream = AssistantMessageEventStream::new();
    let message = done_message(model, "ok");
    stream.push(AssistantMessageEvent::Start {
        partial: message.clone(),
    });
    stream.push(AssistantMessageEvent::Done {
        reason: DoneReason::Stop,
        message: message.clone(),
    });
    stream.end(Some(message));
    stream
}

/// Streams that never produce events.
#[must_use]
pub fn silent_streams() -> ProviderStreams {
    ProviderStreams {
        stream: Arc::new(|_, _, _| AssistantMessageEventStream::new()),
        stream_simple: Arc::new(|_, _, _| AssistantMessageEventStream::new()),
        fetch_deferred: None,
        cancel_deferred: None,
    }
}

type ResolveFn = Arc<
    dyn Fn(ApiKeyResolveInput) -> BoxFuture<'static, Result<Option<AuthResult>, Thrown>>
        + Send
        + Sync,
>;
type CheckFn = Arc<
    dyn Fn(ApiKeyResolveInput) -> BoxFuture<'static, Result<Option<AuthCheck>, Thrown>>
        + Send
        + Sync,
>;
type ApiKeyLoginFn = Arc<
    dyn Fn(ProviderAuthInteraction) -> BoxFuture<'static, Result<ApiKeyCredential, Thrown>>
        + Send
        + Sync,
>;

/// An api-key auth built from closures (the TS object literals).
#[derive(Clone)]
pub struct FnApiKeyAuth {
    pub name: String,
    pub resolve: ResolveFn,
    pub check: Option<CheckFn>,
    pub login: Option<ApiKeyLoginFn>,
}

impl FnApiKeyAuth {
    pub fn new<F, Fut>(name: &str, resolve: F) -> Self
    where
        F: Fn(ApiKeyResolveInput) -> Fut + Send + Sync + 'static,
        Fut: std::future::Future<Output = Result<Option<AuthResult>, Thrown>> + Send + 'static,
    {
        Self {
            name: name.to_owned(),
            resolve: Arc::new(move |input| Box::pin(resolve(input))),
            check: None,
            login: None,
        }
    }

    #[must_use]
    pub fn with_check<F, Fut>(mut self, check: F) -> Self
    where
        F: Fn(ApiKeyResolveInput) -> Fut + Send + Sync + 'static,
        Fut: std::future::Future<Output = Result<Option<AuthCheck>, Thrown>> + Send + 'static,
    {
        self.check = Some(Arc::new(move |input| Box::pin(check(input))));
        self
    }

    #[must_use]
    pub fn with_login<F, Fut>(mut self, login: F) -> Self
    where
        F: Fn(ProviderAuthInteraction) -> Fut + Send + Sync + 'static,
        Fut: std::future::Future<Output = Result<ApiKeyCredential, Thrown>> + Send + 'static,
    {
        self.login = Some(Arc::new(move |interaction| Box::pin(login(interaction))));
        self
    }

    #[must_use]
    pub fn arc(self) -> Arc<dyn ApiKeyAuth> {
        Arc::new(self)
    }
}

impl ApiKeyAuth for FnApiKeyAuth {
    fn name(&self) -> &str {
        &self.name
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
    ) -> Option<BoxFuture<'_, Result<ApiKeyCredential, Thrown>>> {
        self.login.as_ref().map(|login| login(interaction))
    }

    fn check(
        &self,
        input: ApiKeyResolveInput,
    ) -> Option<BoxFuture<'_, Result<Option<AuthCheck>, Thrown>>> {
        self.check.as_ref().map(|check| check(input))
    }

    fn resolve(
        &self,
        input: ApiKeyResolveInput,
    ) -> BoxFuture<'_, Result<Option<AuthResult>, Thrown>> {
        (self.resolve)(input)
    }
}

/// Ambient auth for keyless test providers: configured, no auth values.
#[must_use]
pub fn ambient_auth() -> Arc<dyn ApiKeyAuth> {
    FnApiKeyAuth::new("Ambient", |_| async { Ok(Some(AuthResult::default())) }).arc()
}

/// `credential?.key ?? key`, source "stored" / "env".
#[must_use]
pub fn env_key_auth(key: Option<&str>) -> FnApiKeyAuth {
    let key = key.map(str::to_owned);
    FnApiKeyAuth::new("Test API key", move |input| {
        let key = key.clone();
        async move {
            let stored = input
                .credential
                .as_ref()
                .and_then(|credential| credential.key.clone());
            let Some(resolved) = stored.or(key) else {
                return Ok(None);
            };
            Ok(Some(AuthResult {
                auth: ModelAuth {
                    api_key: Some(resolved),
                    ..ModelAuth::default()
                },
                env: None,
                source: Some(
                    if input.credential.is_some() {
                        "stored"
                    } else {
                        "env"
                    }
                    .to_owned(),
                ),
            }))
        }
    })
}

type RefreshFn = Arc<
    dyn Fn(OAuthCredential) -> BoxFuture<'static, Result<OAuthCredential, Thrown>> + Send + Sync,
>;

/// TS `testOAuth()`: refresh returns the credential; auth uses `access`.
#[derive(Clone)]
pub struct TestOAuth {
    pub refresh: RefreshFn,
}

impl TestOAuth {
    #[must_use]
    pub fn new() -> Self {
        Self {
            refresh: Arc::new(|credential| Box::pin(async move { Ok(credential) })),
        }
    }

    pub fn with_refresh<F, Fut>(refresh: F) -> Self
    where
        F: Fn(OAuthCredential) -> Fut + Send + Sync + 'static,
        Fut: std::future::Future<Output = Result<OAuthCredential, Thrown>> + Send + 'static,
    {
        Self {
            refresh: Arc::new(move |credential| Box::pin(refresh(credential))),
        }
    }

    #[must_use]
    pub fn arc(self) -> Arc<dyn OAuthAuth> {
        Arc::new(self)
    }
}

impl Default for TestOAuth {
    fn default() -> Self {
        Self::new()
    }
}

impl OAuthAuth for TestOAuth {
    // The trait returns a borrowed name; this one is a literal.
    #[allow(clippy::unnecessary_literal_bound)]
    fn name(&self) -> &str {
        "Test OAuth"
    }

    fn login(
        &self,
        _interaction: ProviderAuthInteraction,
        _options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async { Err(error("not used")) })
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        _signal: eukhe_chord::context::AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        (self.refresh)(credential)
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move {
            Ok(ModelAuth {
                api_key: Some(credential.access.clone()),
                ..ModelAuth::default()
            })
        })
    }
}

/// Input of [`test_provider`].
#[derive(Default)]
pub struct TestProvider {
    pub id: String,
    pub models: Option<Vec<Model>>,
    pub auth: Option<ProviderAuth>,
    pub get_models: Option<GetModelsFn>,
    pub refresh_models: Option<RefreshModelsFn>,
    pub calls: Option<Calls>,
}

/// TS `testProvider()`: a handwritten provider answering "ok".
#[must_use]
pub fn test_provider(input: TestProvider) -> Provider {
    let models = input
        .models
        .unwrap_or_else(|| vec![test_model(&input.id, "model-a")]);
    let stream_calls = input.calls.clone();
    let simple_calls = input.calls;
    Provider {
        id: input.id.clone(),
        name: input.id,
        base_url: None,
        headers: None,
        auth: input.auth.unwrap_or_else(|| ProviderAuth {
            api_key: Some(ambient_auth()),
            oauth: None,
        }),
        get_models: input
            .get_models
            .unwrap_or_else(|| Arc::new(move || Ok(models.clone()))),
        get_all_models: None,
        refresh_models: input.refresh_models,
        filter_models: None,
        filter_all_models: None,
        stream: Arc::new(move |model, _context, options| {
            if let Some(calls) = &stream_calls {
                calls
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(ProviderCall {
                        model: model.clone(),
                        options: options.stream,
                    });
            }
            ok_stream(model)
        }),
        stream_simple: Arc::new(move |model, _context, options| {
            if let Some(calls) = &simple_calls {
                calls
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(ProviderCall {
                        model: model.clone(),
                        options: options.stream,
                    });
            }
            ok_stream(model)
        }),
        fetch_deferred: None,
        cancel_deferred: None,
        generate_images: None,
        classify: None,
    }
}

/// Persists `credential` through the single write path.
pub async fn store(credentials: &dyn CredentialStore, provider_id: &str, credential: Credential) {
    credentials
        .modify(
            provider_id,
            Box::new(move |_| Box::pin(async move { Ok(Some(credential)) })),
            eukhe_pi_ai::auth::AuthOperationOptions::default(),
        )
        .await
        .expect("store credential");
}

/// `{ type: "oauth", access, refresh, expires }`.
#[must_use]
pub fn oauth(access: &str, refresh: &str, expires: f64) -> Credential {
    Credential::OAuth(OAuthCredential::new(refresh, access, expires))
}

/// `{ type: "api_key", key }`.
#[must_use]
pub fn api_key(key: &str) -> Credential {
    Credential::ApiKey(ApiKeyCredential::with_key(key))
}

/// Zero-cost text-only test model cost.
#[must_use]
pub fn zero_cost() -> ModelCost {
    ModelCost::default()
}

/// `["text"]`.
#[must_use]
pub fn text_input() -> Vec<Modality> {
    vec![Modality::Text]
}

/// How [`json_matches`] compares objects.
#[derive(Clone, Copy)]
enum JsonMatch {
    /// vitest `toEqual`: same keys.
    Exact,
    /// vitest `toMatchObject`: `expected` keys only.
    Subset,
}

/// JS-number-aware recursive comparison (`1` equals `1.0`).
fn json_matches(actual: &serde_json::Value, expected: &serde_json::Value, mode: JsonMatch) -> bool {
    use serde_json::Value;
    match (actual, expected) {
        (Value::Number(a), Value::Number(e)) => a.as_f64() == e.as_f64(),
        (Value::Array(a), Value::Array(e)) => {
            a.len() == e.len() && a.iter().zip(e).all(|(a, e)| json_matches(a, e, mode))
        }
        (Value::Object(a), Value::Object(e)) => {
            let same_keys = match mode {
                JsonMatch::Exact => a.len() == e.len(),
                JsonMatch::Subset => true,
            };
            same_keys
                && e.iter()
                    .all(|(key, e)| a.get(key).is_some_and(|a| json_matches(a, e, mode)))
        }
        _ => actual == expected,
    }
}

/// vitest `expect(actual).toEqual(expected)` on serialized values.
#[track_caller]
pub fn assert_json_eq<T: serde::Serialize>(actual: &T, expected: &serde_json::Value) {
    let actual = serde_json::to_value(actual).expect("serialize");
    assert!(
        json_matches(&actual, expected, JsonMatch::Exact),
        "expected {actual:#} to equal {expected:#}"
    );
}

/// vitest `expect(actual).toMatchObject(expected)` on serialized values.
#[track_caller]
pub fn assert_match_object<T: serde::Serialize>(actual: &T, expected: &serde_json::Value) {
    let actual = serde_json::to_value(actual).expect("serialize");
    assert!(
        json_matches(&actual, expected, JsonMatch::Subset),
        "expected {actual:#} to match {expected:#}"
    );
}
