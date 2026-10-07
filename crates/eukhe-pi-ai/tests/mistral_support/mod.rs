//! Test helpers of the Mistral API tests: a scripted local HTTP server
//! behind a capturing `fetch` (the TS tests' mocked `fetch` returning a
//! `Response`).

#![allow(dead_code)] // Each test binary uses a different subset of the helpers.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::types::{FetchFunction, OnPayload};
use eukhe_types::pi_ai::{JsonValue, Model};
use reqwest::header::HeaderMap;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

/// One scripted HTTP response.
#[derive(Clone)]
pub struct MockResponse {
    pub status: u16,
    pub reason: &'static str,
    /// Response headers, written in order.
    pub headers: Vec<(String, String)>,
    /// Body pieces, each flushed separately.
    pub chunks: Vec<Vec<u8>>,
    /// Keep the connection open after the chunks (a body that never ends).
    pub hang: bool,
}

impl MockResponse {
    /// `new Response(body, { headers: { "content-type": "text/event-stream", ...headers } })`.
    pub fn sse(body: String, headers: &[(&str, &str)]) -> Self {
        let mut all = vec![("content-type".to_owned(), "text/event-stream".to_owned())];
        all.extend(
            headers
                .iter()
                .map(|(name, value)| ((*name).to_owned(), (*value).to_owned())),
        );
        Self {
            status: 200,
            reason: "OK",
            headers: all,
            chunks: vec![body.into_bytes()],
            hang: false,
        }
    }
}

/// TS `createSseResponse(events, headers)`.
pub fn create_sse_response(events: &[JsonValue], headers: &[(&str, &str)]) -> MockResponse {
    let body = format!(
        "{}\r\n\r\ndata: [DONE]\r\n\r\n",
        events
            .iter()
            .map(|event| format!("data: {event}"))
            .collect::<Vec<_>>()
            .join("\r\n\r\n")
    );
    MockResponse::sse(body, headers)
}

/// TS `createTerminalEvent(finishReason)`.
pub fn create_terminal_event(finish_reason: &str) -> JsonValue {
    serde_json::json!({
        "id": "mistral-response-id",
        "model": "mistral-large-latest",
        "choices": [{ "index": 0, "finish_reason": finish_reason, "delta": {} }],
        "usage": { "prompt_tokens": 1, "completion_tokens": 1, "total_tokens": 2 },
    })
}

/// What the `fetch` saw.
#[derive(Debug, Clone)]
pub struct CapturedRequest {
    pub url: String,
    pub headers: HeaderMap,
    pub body: String,
}

pub type Captured = Arc<Mutex<Option<CapturedRequest>>>;

pub fn captured(capture: &Captured) -> CapturedRequest {
    capture
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("fetch was called")
}

async fn serve(listener: TcpListener, response: MockResponse) {
    let Ok((mut socket, _)) = listener.accept().await else {
        return;
    };
    // Read the request head and its content-length body.
    let mut buffer = Vec::new();
    let mut chunk = [0u8; 4096];
    let head_end = loop {
        let read = socket.read(&mut chunk).await.unwrap_or(0);
        if read == 0 {
            return;
        }
        buffer.extend_from_slice(&chunk[..read]);
        if let Some(index) = buffer.windows(4).position(|window| window == b"\r\n\r\n") {
            break index + 4;
        }
    };
    let head = String::from_utf8_lossy(&buffer[..head_end]).to_lowercase();
    let length: usize = head
        .lines()
        .find_map(|line| line.strip_prefix("content-length:"))
        .and_then(|value| value.trim().parse().ok())
        .unwrap_or(0);
    while buffer.len() < head_end + length {
        let read = socket.read(&mut chunk).await.unwrap_or(0);
        if read == 0 {
            break;
        }
        buffer.extend_from_slice(&chunk[..read]);
    }

    let mut head = format!("HTTP/1.1 {} {}\r\n", response.status, response.reason);
    for (name, value) in &response.headers {
        head.push_str(name);
        head.push_str(": ");
        head.push_str(value);
        head.push_str("\r\n");
    }
    head.push_str("\r\n");
    if socket.write_all(head.as_bytes()).await.is_err() {
        return;
    }
    let _ = socket.flush().await;
    for piece in &response.chunks {
        if socket.write_all(piece).await.is_err() {
            return;
        }
        let _ = socket.flush().await;
    }
    if response.hang {
        // Hold the connection until the client goes away.
        let _ = socket.read(&mut chunk).await;
    }
}

/// A `fetch` that records the request and answers with `response` from a
/// local server (the request goes to the server under the same path).
pub async fn mock_fetch(response: MockResponse) -> (FetchFunction, Captured) {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let address = listener.local_addr().expect("address");
    tokio::spawn(serve(listener, response));
    let capture: Captured = Arc::new(Mutex::new(None));
    let sink = Arc::clone(&capture);
    let client = reqwest::Client::builder()
        .no_proxy()
        .build()
        .expect("client");
    let fetch: FetchFunction = Arc::new(move |mut request: reqwest::Request| {
        let body = request
            .body()
            .and_then(reqwest::Body::as_bytes)
            .map(|bytes| String::from_utf8_lossy(bytes).into_owned())
            .unwrap_or_default();
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(CapturedRequest {
            url: request.url().to_string(),
            headers: request.headers().clone(),
            body,
        });
        let url = request.url_mut();
        url.set_scheme("http").expect("scheme");
        url.set_host(Some("127.0.0.1")).expect("host");
        url.set_port(Some(address.port())).expect("port");
        let client = client.clone();
        Box::pin(async move {
            client.execute(request).await.map_err(|error| {
                eukhe_pi_ai::utils::diagnostics::ErrorObject::new(error.to_string()).thrown()
            })
        })
    });
    (fetch, capture)
}

/// An `onPayload` that records the payload and returns `replace(payload)`.
pub fn capture_payload(
    replace: impl Fn(&JsonValue) -> Option<JsonValue> + Send + Sync + 'static,
) -> (OnPayload<Model>, Arc<Mutex<Option<JsonValue>>>) {
    let store: Arc<Mutex<Option<JsonValue>>> = Arc::new(Mutex::new(None));
    let sink = Arc::clone(&store);
    let on_payload: OnPayload<Model> = Arc::new(move |payload: JsonValue, _model: &Model| {
        let next = replace(&payload);
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        Box::pin(async move { Ok(next) })
    });
    (on_payload, store)
}

pub fn payload_of(store: &Arc<Mutex<Option<JsonValue>>>) -> JsonValue {
    store
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("Expected payload to be captured before request failure")
}
