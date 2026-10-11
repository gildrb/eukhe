//! Test-only mock `fetch` for the classifier and image API tests: records
//! each request and answers it from a handler (TS `vi.fn(async (input, init) => …)`).

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::pi_ai::JsonValue;
use reqwest::header::HeaderMap;

use crate::types::FetchFunction;

/// One request the mock received.
#[derive(Debug, Clone)]
pub(crate) struct Recorded {
    pub(crate) url: String,
    pub(crate) method: String,
    pub(crate) headers: HeaderMap,
    pub(crate) body: String,
}

impl Recorded {
    pub(crate) fn json(&self) -> JsonValue {
        serde_json::from_str(&self.body).expect("JSON request body")
    }

    pub(crate) fn header(&self, name: &str) -> Option<&str> {
        self.headers.get(name).and_then(|value| value.to_str().ok())
    }
}

/// `Response.json(body, { status })`.
pub(crate) fn json_response(status: u16, body: &JsonValue) -> reqwest::Response {
    response(
        status,
        &[("content-type", "application/json")],
        serde_json::to_string(body).expect("serialize"),
    )
}

/// `new Response(body, { status, headers })`.
pub(crate) fn response(status: u16, headers: &[(&str, &str)], body: String) -> reqwest::Response {
    let mut builder = http::Response::builder().status(status);
    for (name, value) in headers {
        builder = builder.header(*name, *value);
    }
    reqwest::Response::from(builder.body(body).expect("response"))
}

pub(crate) type Requests = Arc<Mutex<Vec<Recorded>>>;

pub(crate) fn recorded(requests: &Requests) -> Vec<Recorded> {
    requests
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
}

/// A `fetch` that records each request and answers with `handler`.
pub(crate) fn mock_fetch(
    handler: impl Fn(&Recorded) -> reqwest::Response + Send + Sync + 'static,
) -> (FetchFunction, Requests) {
    let requests: Requests = Arc::default();
    let sink = Arc::clone(&requests);
    let handler = Arc::new(handler);
    let fetch: FetchFunction = Arc::new(move |request: reqwest::Request| {
        let recorded = Recorded {
            url: request.url().to_string(),
            method: request.method().to_string(),
            headers: request.headers().clone(),
            body: request
                .body()
                .and_then(reqwest::Body::as_bytes)
                .map(|bytes| String::from_utf8_lossy(bytes).into_owned())
                .unwrap_or_default(),
        };
        let response = handler(&recorded);
        sink.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(recorded);
        Box::pin(async move { Ok(response) })
    });
    (fetch, requests)
}
