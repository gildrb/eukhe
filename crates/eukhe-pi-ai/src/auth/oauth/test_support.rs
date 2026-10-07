//! Shared test helpers for the OAuth flow tests: closure-backed
//! interactions (the TS object literals) and a real `fetch` for hitting the
//! loopback server (`nativeFetch`).

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{AbortController, AbortSignal};
use futures::future::BoxFuture;

use crate::auth::types::{AuthEvent, AuthInteraction, AuthPrompt, ProviderAuthInteraction};
use crate::utils::diagnostics::Thrown;

type PromptFn = Box<dyn Fn(AuthPrompt) -> BoxFuture<'static, Result<String, Thrown>> + Send + Sync>;
type NotifyFn = Box<dyn Fn(AuthEvent) + Send + Sync>;

/// An interaction built from closures.
pub(crate) struct TestInteraction {
    signal: AbortSignal,
    prompt: PromptFn,
    notify: NotifyFn,
}

impl TestInteraction {
    pub(crate) fn provider(
        signal: AbortSignal,
        prompt: impl Fn(AuthPrompt) -> BoxFuture<'static, Result<String, Thrown>>
            + Send
            + Sync
            + 'static,
        notify: impl Fn(AuthEvent) + Send + Sync + 'static,
    ) -> ProviderAuthInteraction {
        let interaction = Arc::new(Self {
            signal: signal.clone(),
            prompt: Box::new(prompt),
            notify: Box::new(notify),
        });
        ProviderAuthInteraction::new(interaction, signal)
    }
}

impl AuthInteraction for TestInteraction {
    fn signal(&self) -> Option<AbortSignal> {
        Some(self.signal.clone())
    }

    fn prompt(&self, prompt: AuthPrompt) -> BoxFuture<'_, Result<String, Thrown>> {
        (self.prompt)(prompt)
    }

    fn notify(&self, event: AuthEvent) {
        (self.notify)(event);
    }
}

/// `new AbortController().signal`.
pub(crate) fn never_aborted_signal() -> AbortSignal {
    AbortController::new().signal()
}

/// Collects notified events.
#[derive(Clone, Default)]
pub(crate) struct Events(Arc<Mutex<Vec<AuthEvent>>>);

impl Events {
    pub(crate) fn push(&self, event: AuthEvent) {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(event);
    }

    pub(crate) fn all(&self) -> Vec<AuthEvent> {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    /// The last `auth_url` event's url, or "".
    pub(crate) fn auth_url(&self) -> String {
        self.all()
            .into_iter()
            .rev()
            .find_map(|event| match event {
                AuthEvent::AuthUrl { url, .. } => Some(url),
                AuthEvent::Info { .. }
                | AuthEvent::DeviceCode { .. }
                | AuthEvent::Progress { .. } => None,
            })
            .unwrap_or_default()
    }
}

/// `new URL(url).searchParams.get(name)`.
pub(crate) fn url_param(url: &str, name: &str) -> Option<String> {
    url::Url::parse(url)
        .ok()?
        .query_pairs()
        .find(|(key, _)| key == name)
        .map(|(_, value)| value.into_owned())
}

/// The parts of a response the tests inspect.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Page {
    pub(crate) status: u16,
    pub(crate) content_type: Option<String>,
    pub(crate) body: String,
}

/// A real HTTP request (`nativeFetch`).
pub(crate) async fn native_request(method: &str, url: &str) -> Page {
    let client = reqwest::Client::new();
    let method = reqwest::Method::from_bytes(method.as_bytes()).expect("method");
    let response = client
        .request(method, url)
        .send()
        .await
        .expect("native fetch");
    let status = response.status().as_u16();
    let content_type = response
        .headers()
        .get("content-type")
        .and_then(|value| value.to_str().ok())
        .map(str::to_owned);
    let body = response.text().await.expect("body");
    Page {
        status,
        content_type,
        body,
    }
}

/// `nativeFetch(url)`.
pub(crate) async fn native_get(url: &str) -> Page {
    native_request("GET", url).await
}
