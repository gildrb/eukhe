//! Test helpers for the `OpenAI` Responses API tests: a `fetch` mock that
//! records requests and answers with canned SSE bodies (the TS tests'
//! `vi.spyOn(globalThis, "fetch")`).

#![allow(dead_code)] // Each test binary uses a subset.

pub mod azure;

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::types::{AssistantMessage, AssistantMessageEvent, FetchFunction, JsonValue};
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use futures::StreamExt;

/// One captured request.
#[derive(Debug, Clone)]
pub struct CapturedRequest {
    pub url: String,
    pub headers: reqwest::header::HeaderMap,
    pub body: JsonValue,
}

impl CapturedRequest {
    /// A header value by case-insensitive name.
    pub fn header(&self, name: &str) -> Option<String> {
        self.headers
            .get(name)
            .and_then(|value| value.to_str().ok())
            .map(str::to_owned)
    }
}

/// A canned response.
#[derive(Debug, Clone)]
pub struct MockResponse {
    pub status: u16,
    pub content_type: String,
    pub body: String,
}

impl MockResponse {
    pub fn sse(body: impl Into<String>) -> Self {
        Self {
            status: 200,
            content_type: "text/event-stream".to_owned(),
            body: body.into(),
        }
    }

    pub fn json(status: u16, body: impl Into<String>) -> Self {
        Self {
            status,
            content_type: "application/json".to_owned(),
            body: body.into(),
        }
    }
}

/// SSE body of JSON events (`data: <json>\n\n` each).
pub fn sse_events(events: &[JsonValue]) -> String {
    events.iter().fold(String::new(), |mut body, event| {
        use std::fmt::Write as _;
        let _ = write!(body, "data: {event}\n\n"); // Writing to a String cannot fail.
        body
    })
}

/// A fetch mock answering every request with `responses` in turn (the last
/// one repeats) and recording the requests.
pub fn mock_fetch(
    responses: Vec<MockResponse>,
) -> (FetchFunction, Arc<Mutex<Vec<CapturedRequest>>>) {
    let captured: Arc<Mutex<Vec<CapturedRequest>>> = Arc::default();
    let sink = Arc::clone(&captured);
    let fetch: FetchFunction = Arc::new(move |request: reqwest::Request| {
        let body = request
            .body()
            .and_then(reqwest::Body::as_bytes)
            .map_or(JsonValue::Null, |bytes| {
                serde_json::from_slice(bytes).unwrap_or(JsonValue::Null)
            });
        let mut requests = sink.lock().unwrap_or_else(PoisonError::into_inner);
        let index = requests.len();
        requests.push(CapturedRequest {
            url: request.url().to_string(),
            headers: request.headers().clone(),
            body,
        });
        drop(requests);
        let response = responses
            .get(index)
            .or_else(|| responses.last())
            .cloned()
            .expect("at least one mock response");
        Box::pin(async move {
            let http = http::Response::builder()
                .status(response.status)
                .header("content-type", response.content_type)
                .body(response.body)
                .expect("mock response");
            Ok(reqwest::Response::from(http))
        })
    });
    (fetch, captured)
}

/// All events of a stream and its final message.
pub async fn collect(
    stream: AssistantMessageEventStream,
) -> (Vec<AssistantMessageEvent>, AssistantMessage) {
    let events: Vec<AssistantMessageEvent> = stream.events().collect().await;
    let result = stream.result().await;
    (events, result)
}
