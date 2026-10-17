//! A local HTTP server for the capability tests: it answers scripted
//! replies in order, one connection each, and records every request.

use std::collections::BTreeMap;

use eukhe_types::pi_ai::JsonValue;
use serde_json::json;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;
use tokio::task::JoinHandle;

use crate::types::{Model, ProviderRequestOptions};

/// One scripted reply.
#[derive(Debug, Clone)]
pub(crate) struct Reply {
    pub(crate) status: u16,
    pub(crate) body: JsonValue,
}

impl Reply {
    pub(crate) fn ok(body: JsonValue) -> Self {
        Self { status: 200, body }
    }
}

/// One request the server received. `headers` has lowercase names and
/// leaves out `host` (its port changes per run) and `content-length` (the
/// body pins it).
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Recorded {
    pub(crate) method: String,
    /// Path and query.
    pub(crate) path: String,
    pub(crate) headers: BTreeMap<String, String>,
    /// The JSON body; `None` without a body.
    pub(crate) body: Option<JsonValue>,
}

/// Headers of the form `[(name, value)]`.
pub(crate) fn headers<const N: usize>(pairs: [(&str, &str); N]) -> BTreeMap<String, String> {
    pairs
        .into_iter()
        .map(|(name, value)| (name.to_owned(), value.to_owned()))
        .collect()
}

/// Serves `replies` in order on a local port. Returns the server root
/// (`http://127.0.0.1:<port>`) and the requests, once every reply went out.
pub(crate) async fn serve(replies: Vec<Reply>) -> (String, JoinHandle<Vec<Recorded>>) {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let address = listener.local_addr().expect("address");
    let handle = tokio::spawn(async move {
        let mut recorded = Vec::new();
        for reply in replies {
            let (mut socket, _) = listener.accept().await.expect("accept");
            let mut received = Vec::new();
            let mut buffer = [0_u8; 8192];
            let (head_end, content_length) = loop {
                let read = socket.read(&mut buffer).await.expect("read");
                assert!(read > 0, "the client closed before the request head");
                received.extend_from_slice(&buffer[..read]);
                if let Some(end) = received.windows(4).position(|window| window == b"\r\n\r\n") {
                    let head = String::from_utf8_lossy(&received[..end]).to_lowercase();
                    let length = head
                        .lines()
                        .find_map(|line| line.strip_prefix("content-length:"))
                        .and_then(|value| value.trim().parse::<usize>().ok())
                        .unwrap_or(0);
                    break (end + 4, length);
                }
            };
            while received.len() < head_end + content_length {
                let read = socket.read(&mut buffer).await.expect("read");
                assert!(read > 0, "the client closed before the request body");
                received.extend_from_slice(&buffer[..read]);
            }
            let head = String::from_utf8_lossy(&received[..head_end - 4]).into_owned();
            let mut lines = head.lines();
            let mut request_line = lines.next().unwrap_or_default().split(' ');
            let method = request_line.next().unwrap_or_default().to_owned();
            let path = request_line.next().unwrap_or_default().to_owned();
            let headers = lines
                .filter_map(|line| line.split_once(':'))
                .map(|(name, value)| (name.trim().to_lowercase(), value.trim().to_owned()))
                .filter(|(name, _)| name != "host" && name != "content-length")
                .collect();
            let body_bytes = &received[head_end..head_end + content_length];
            let body = (!body_bytes.is_empty())
                .then(|| serde_json::from_slice(body_bytes).expect("a JSON request body"));
            recorded.push(Recorded {
                method,
                path,
                headers,
                body,
            });
            let text = reply.body.to_string();
            let response = format!(
                "HTTP/1.1 {} X\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n\r\n{text}",
                reply.status,
                text.len()
            );
            socket.write_all(response.as_bytes()).await.expect("write");
            socket.shutdown().await.ok();
        }
        recorded
    });
    (format!("http://{address}"), handle)
}

/// A chat model of `provider` on `api` at `base_url`.
pub(crate) fn model(provider: &str, api: &str, id: &str, base_url: &str) -> Model {
    serde_json::from_value(json!({
        "id": id,
        "name": id,
        "api": api,
        "provider": provider,
        "baseUrl": base_url,
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 8_192,
    }))
    .expect("a chat model")
}

/// Request options with `api_key` and no retries.
pub(crate) fn options(api_key: &str) -> ProviderRequestOptions {
    ProviderRequestOptions {
        api_key: Some(api_key.to_owned()),
        max_retries: Some(0),
        ..ProviderRequestOptions::default()
    }
}
