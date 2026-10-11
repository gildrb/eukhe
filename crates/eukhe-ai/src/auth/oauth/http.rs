//! The `fetch` the OAuth flows use: a buffered request/response over
//! `reqwest`, cancelled by an [`AbortSignal`] like the WHATWG `fetch`.
//! Tests replace it with a mock, the Rust form of `vi.stubGlobal("fetch")`.

use std::sync::LazyLock;

use eukhe_chord::context::AbortSignal;

use crate::auth::errors::named_error;
use crate::utils::diagnostics::Thrown;

/// A buffered HTTP request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FetchRequest {
    pub(crate) method: &'static str,
    pub(crate) url: String,
    pub(crate) headers: Vec<(String, String)>,
    pub(crate) body: Option<String>,
}

impl FetchRequest {
    pub(crate) fn get(url: impl Into<String>) -> Self {
        Self {
            method: "GET",
            url: url.into(),
            headers: Vec::new(),
            body: None,
        }
    }

    pub(crate) fn post(url: impl Into<String>) -> Self {
        Self {
            method: "POST",
            ..Self::get(url)
        }
    }

    pub(crate) fn header(mut self, name: &str, value: impl Into<String>) -> Self {
        self.headers.push((name.to_owned(), value.into()));
        self
    }

    pub(crate) fn body(mut self, body: impl Into<String>) -> Self {
        self.body = Some(body.into());
        self
    }

    /// `new URLSearchParams(fields).toString()` as the body.
    pub(crate) fn form(self, fields: &[(&str, &str)]) -> Self {
        let body = form_urlencode(fields);
        self.body(body)
    }

    /// A request header, case-insensitively.
    #[cfg(test)]
    pub(crate) fn header_value(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(key, _)| key.eq_ignore_ascii_case(name))
            .map(|(_, value)| value.as_str())
    }

    /// The body parsed as `application/x-www-form-urlencoded`.
    #[cfg(test)]
    pub(crate) fn form_fields(&self) -> Vec<(String, String)> {
        url::form_urlencoded::parse(self.body.as_deref().unwrap_or_default().as_bytes())
            .into_owned()
            .collect()
    }

    /// The body parsed as JSON.
    #[cfg(test)]
    pub(crate) fn json_body(&self) -> serde_json::Value {
        serde_json::from_str(self.body.as_deref().unwrap_or_default())
            .unwrap_or(serde_json::Value::Null)
    }
}

/// `URLSearchParams` serialization.
pub(crate) fn form_urlencode(fields: &[(&str, &str)]) -> String {
    let mut serializer = url::form_urlencoded::Serializer::new(String::new());
    for (name, value) in fields {
        serializer.append_pair(name, value);
    }
    serializer.finish()
}

/// A buffered HTTP response.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FetchResponse {
    pub(crate) status: u16,
    pub(crate) status_text: String,
    pub(crate) headers: Vec<(String, String)>,
    pub(crate) body: String,
}

impl FetchResponse {
    /// `response.ok`.
    pub(crate) fn ok(&self) -> bool {
        (200..=299).contains(&self.status)
    }

    /// `response.headers.get(name)`.
    pub(crate) fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(key, _)| key.eq_ignore_ascii_case(name))
            .map(|(_, value)| value.as_str())
    }

    /// `response.json()`.
    pub(crate) fn json(&self) -> Result<serde_json::Value, Thrown> {
        serde_json::from_str(&self.body)
            .map_err(|error| named_error("SyntaxError", error.to_string()))
    }

    /// A JSON response, the test helper `jsonResponse(body, status)`.
    #[cfg(test)]
    pub(crate) fn json_response(body: &serde_json::Value, status: u16) -> Self {
        Self {
            status,
            status_text: String::new(),
            headers: vec![("content-type".to_owned(), "application/json".to_owned())],
            body: body.to_string(),
        }
    }
}

static CLIENT: LazyLock<reqwest::Client> = LazyLock::new(reqwest::Client::new);

/// `fetch(request, { signal })`. Fails with the signal's reason when it
/// aborts first, and with `TypeError: fetch failed` on network errors.
pub(crate) async fn fetch(
    request: FetchRequest,
    signal: Option<&AbortSignal>,
) -> Result<FetchResponse, Thrown> {
    if let Some(signal) = signal {
        signal.throw_if_aborted()?;
    }
    let exchange = async {
        #[cfg(test)]
        if let Some(mock) = mock::current() {
            return mock(request).await;
        }
        send(request).await
    };
    match signal {
        Some(signal) => tokio::select! {
            reason = signal.cancelled() => Err(reason),
            response = exchange => response,
        },
        None => exchange.await,
    }
}

async fn send(request: FetchRequest) -> Result<FetchResponse, Thrown> {
    let method = reqwest::Method::from_bytes(request.method.as_bytes())
        .map_err(|error| named_error("TypeError", error.to_string()))?;
    let mut builder = CLIENT.request(method, &request.url);
    for (name, value) in &request.headers {
        builder = builder.header(name, value);
    }
    if let Some(body) = request.body {
        builder = builder.body(body);
    }
    let response = builder.send().await.map_err(network_error)?;
    let status = response.status();
    let headers = response
        .headers()
        .iter()
        .map(|(name, value)| {
            (
                name.as_str().to_owned(),
                String::from_utf8_lossy(value.as_bytes()).into_owned(),
            )
        })
        .collect();
    let body = response.text().await.map_err(network_error)?;
    Ok(FetchResponse {
        status: status.as_u16(),
        status_text: status.canonical_reason().unwrap_or_default().to_owned(),
        headers,
        body,
    })
}

#[allow(clippy::needless_pass_by_value)] // used as `map_err(network_error)`
fn network_error(error: reqwest::Error) -> Thrown {
    named_error("TypeError", format!("fetch failed: {error}"))
}

#[cfg(test)]
pub(crate) mod mock {
    //! The stubbed global `fetch`. Installing a mock takes a process-wide
    //! test lock, so mock-using tests run one at a time (`describe.sequential`).

    use std::future::Future;
    use std::sync::{Arc, LazyLock, Mutex, PoisonError};

    use futures::future::BoxFuture;

    use super::{FetchRequest, FetchResponse};
    use crate::utils::diagnostics::Thrown;

    pub(crate) type FetchMock = Arc<
        dyn Fn(FetchRequest) -> BoxFuture<'static, Result<FetchResponse, Thrown>> + Send + Sync,
    >;

    static MOCK: Mutex<Option<FetchMock>> = Mutex::new(None);
    static SERIAL: LazyLock<Arc<tokio::sync::Mutex<()>>> =
        LazyLock::new(|| Arc::new(tokio::sync::Mutex::new(())));

    pub(super) fn current() -> Option<FetchMock> {
        MOCK.lock().unwrap_or_else(PoisonError::into_inner).clone()
    }

    /// Holds the test lock; removes the mock when dropped (`vi.unstubAllGlobals`).
    pub(crate) struct FetchMockGuard {
        _serial: tokio::sync::OwnedMutexGuard<()>,
    }

    impl Drop for FetchMockGuard {
        fn drop(&mut self) {
            *MOCK.lock().unwrap_or_else(PoisonError::into_inner) = None;
        }
    }

    /// Take the test lock without stubbing `fetch` (tests that bind the
    /// fixed callback ports).
    pub(crate) async fn serial() -> FetchMockGuard {
        let serial = Arc::clone(&SERIAL).lock_owned().await;
        *MOCK.lock().unwrap_or_else(PoisonError::into_inner) = None;
        FetchMockGuard { _serial: serial }
    }

    /// Stub `fetch` with `mock` until the guard drops.
    pub(crate) async fn install<F, Fut>(mock: F) -> FetchMockGuard
    where
        F: Fn(FetchRequest) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<FetchResponse, Thrown>> + Send + 'static,
    {
        let guard = serial().await;
        let mock: FetchMock = Arc::new(move |request| Box::pin(mock(request)));
        *MOCK.lock().unwrap_or_else(PoisonError::into_inner) = Some(mock);
        guard
    }
}
