//! Port of `test/fetch-option.test.ts`.
//!
//! TS stubs `globalThis.fetch` with a `fallback` that must never run and
//! passes a `custom` fetch through the stream options. Rust has no ambient
//! `fetch` to stub: an adapter that bypasses the `fetch` option sends the
//! request with its built-in HTTP client to `model.baseUrl`. The `fallback`
//! is therefore a local HTTP server the test models point at, counting the
//! requests that reach it ("`fallback` not called" = zero requests), and the
//! `custom` fetch is a [`FetchFunction`] that counts its calls and answers
//! the TS 401 response. TS `expect(globalThis.fetch).toBe(fallback)` (the
//! adapters do not replace the global) has no Rust counterpart: there is no
//! global to replace.
//!
//! "allows Google adapters to receive globalThis.fetch explicitly": passing
//! the ambient fetch explicitly is, in Rust, passing no `fetch` (the
//! built-in client is the ambient transport). The ambient stub is the local
//! server answering the TS 401, and the case asserts it received exactly one
//! request and that the adapter did not reject the call as a custom fetch.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use base64::Engine as _;
use eukhe_pi_ai::api::{
    anthropic_messages, azure_openai_responses, google_generative_ai, google_vertex,
    mistral_conversations, openai_codex_responses, openai_completions, openai_responses,
    openrouter_images, pi_messages,
};
use eukhe_pi_ai::types::{FetchFunction, ImagesOptions, SimpleStreamOptions};
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{Context, ImageModel, ImagesContext, Model, TranscriptContext, Transport};
use serde_json::json;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};

const REJECTED_BODY: &str = r#"{"error":{"message":"upstream rejected request"}}"#;

fn context() -> TranscriptContext {
    let context: Context = serde_json::from_value(json!({
        "messages": [{ "role": "user", "content": "hello", "timestamp": 1 }],
    }))
    .expect("context");
    normalize_context(context)
}

/// TS `createModel(api)`, with `baseUrl` on the fallback server.
fn create_model(api: &str, fallback: &Fallback) -> Model {
    serde_json::from_value(json!({
        "id": "test-model",
        "name": "Test Model",
        "api": api,
        "provider": "test-provider",
        "baseUrl": fallback.base_url(),
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 10_000,
        "maxTokens": 1_000,
    }))
    .expect("model")
}

/// The TS `vi.fn` custom fetch: answers 401 `upstream rejected request`.
struct CustomFetch {
    fetch: FetchFunction,
    calls: Arc<AtomicUsize>,
}

impl CustomFetch {
    fn new() -> Self {
        let calls = Arc::new(AtomicUsize::new(0));
        let counter = Arc::clone(&calls);
        let fetch: FetchFunction = Arc::new(move |_request: reqwest::Request| {
            counter.fetch_add(1, Ordering::SeqCst);
            Box::pin(async {
                let response = http::Response::builder()
                    .status(401)
                    .header("content-type", "application/json")
                    .body(REJECTED_BODY)
                    .expect("mock response");
                Ok(reqwest::Response::from(response))
            })
        });
        Self { fetch, calls }
    }

    fn calls(&self) -> usize {
        self.calls.load(Ordering::SeqCst)
    }
}

/// The stand-in for the stubbed `globalThis.fetch`: a local server that
/// counts requests and answers the same 401.
struct Fallback {
    url: String,
    requests: Arc<AtomicUsize>,
}

impl Fallback {
    async fn start() -> Self {
        let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let url = format!("http://{}", listener.local_addr().expect("address"));
        let requests = Arc::new(AtomicUsize::new(0));
        let counter = Arc::clone(&requests);
        tokio::spawn(async move {
            while let Ok((socket, _)) = listener.accept().await {
                tokio::spawn(answer_rejected(socket, Arc::clone(&counter)));
            }
        });
        Self { url, requests }
    }

    fn base_url(&self) -> String {
        format!("{}/v1", self.url)
    }

    fn requests(&self) -> usize {
        self.requests.load(Ordering::SeqCst)
    }
}

/// Reads one HTTP/1.1 request (headers and body) and answers the 401.
async fn answer_rejected(mut socket: TcpStream, requests: Arc<AtomicUsize>) {
    let mut buffer = Vec::new();
    let mut chunk = [0_u8; 4096];
    let header_end = loop {
        if let Some(position) = buffer.windows(4).position(|window| window == b"\r\n\r\n") {
            break position + 4;
        }
        match socket.read(&mut chunk).await {
            Ok(0) | Err(_) => return,
            Ok(read) => buffer.extend_from_slice(&chunk[..read]),
        }
    };
    let head = String::from_utf8_lossy(&buffer[..header_end]).to_ascii_lowercase();
    let content_length = head
        .lines()
        .find_map(|line| line.strip_prefix("content-length:"))
        .and_then(|value| value.trim().parse::<usize>().ok());
    let chunked = head.contains("transfer-encoding: chunked");
    loop {
        let body = &buffer[header_end..];
        let complete = match content_length {
            Some(length) => body.len() >= length,
            None => !chunked || body.ends_with(b"0\r\n\r\n"),
        };
        if complete {
            break;
        }
        match socket.read(&mut chunk).await {
            Ok(0) | Err(_) => break,
            Ok(read) => buffer.extend_from_slice(&chunk[..read]),
        }
    }
    requests.fetch_add(1, Ordering::SeqCst);
    let response = format!(
        "HTTP/1.1 401 Unauthorized\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n\r\n{REJECTED_BODY}",
        REJECTED_BODY.len()
    );
    let _ = socket.write_all(response.as_bytes()).await;
    let _ = socket.shutdown().await;
}

/// TS `mockFetches()`.
async fn mock_fetches() -> (CustomFetch, Fallback) {
    (CustomFetch::new(), Fallback::start().await)
}

/// `{ apiKey, fetch, maxRetries? }`.
fn options(
    api_key: &str,
    fetch: Option<&FetchFunction>,
    max_retries: Option<u32>,
) -> SimpleStreamOptions {
    let mut options = SimpleStreamOptions::default();
    options.stream.request.api_key = Some(api_key.to_owned());
    options.stream.request.fetch = fetch.cloned();
    options.stream.request.max_retries = max_retries;
    options
}

/// TS `expectOnlyCustomFetch(custom, fallback)`.
#[track_caller]
fn expect_only_custom_fetch(custom: &CustomFetch, fallback: &Fallback) {
    assert!(custom.calls() > 0, "custom fetch was not called");
    assert_eq!(fallback.requests(), 0, "ambient transport was called");
}

#[tokio::test]
async fn passes_fetch_through_stream_simple_to_the_anthropic_sdk() {
    let (custom, fallback) = mock_fetches().await;
    anthropic_messages::stream_simple(
        &create_model("anthropic-messages", &fallback),
        &context(),
        &options("test-key", Some(&custom.fetch), Some(0)),
    )
    .result()
    .await;
    expect_only_custom_fetch(&custom, &fallback);
}

#[tokio::test]
async fn passes_fetch_through_stream_simple_to_openai_sdk_adapters() {
    let (custom, fallback) = mock_fetches().await;
    let adapter_options = || options("test-key", Some(&custom.fetch), Some(0));
    openai_completions::stream_simple(
        &create_model("openai-completions", &fallback),
        &context(),
        adapter_options(),
    )
    .result()
    .await;
    openai_responses::stream_simple(
        &create_model("openai-responses", &fallback),
        &context(),
        adapter_options(),
    )
    .result()
    .await;
    azure_openai_responses::stream_simple(
        &create_model("azure-openai-responses", &fallback),
        &context(),
        adapter_options(),
    )
    .result()
    .await;

    assert_eq!(custom.calls(), 3);
    assert_eq!(fallback.requests(), 0);
}

#[tokio::test]
async fn uses_fetch_for_mistral_codex_sse_and_pi_messages_http_requests() {
    let (custom, fallback) = mock_fetches().await;
    mistral_conversations::stream_simple(
        &create_model("mistral-conversations", &fallback),
        &context(),
        options("test-key", Some(&custom.fetch), None),
    )
    .result()
    .await;
    let claims = json!({ "https://api.openai.com/auth": { "chatgpt_account_id": "account" } });
    let token = format!(
        "header.{}.signature",
        base64::engine::general_purpose::STANDARD.encode(claims.to_string())
    );
    let mut codex_options = options(&token, Some(&custom.fetch), Some(0));
    codex_options.stream.transport = Some(Transport::Sse);
    openai_codex_responses::stream_simple(
        &create_model("openai-codex-responses", &fallback),
        &context(),
        codex_options,
    )
    .result()
    .await;
    pi_messages::stream_simple(
        &create_model("pi-messages", &fallback),
        &context(),
        options("test-key", Some(&custom.fetch), None),
    )
    .result()
    .await;

    assert_eq!(custom.calls(), 3);
    assert_eq!(fallback.requests(), 0);
}

#[tokio::test]
async fn rejects_custom_fetch_for_google_adapters_instead_of_silently_bypassing_it() {
    let (custom, fallback) = mock_fetches().await;
    let google = google_generative_ai::stream_simple(
        &create_model("google-generative-ai", &fallback),
        &context(),
        options("test-key", Some(&custom.fetch), None),
    )
    .result()
    .await;
    let vertex = google_vertex::stream_simple(
        &create_model("google-vertex", &fallback),
        &context(),
        options("test-key", Some(&custom.fetch), None),
    )
    .result()
    .await;

    assert!(
        google
            .error_message
            .as_deref()
            .is_some_and(|message| message
                .contains("Custom fetch is not supported by the Google Generative AI adapter")),
        "{:?}",
        google.error_message
    );
    assert!(
        vertex
            .error_message
            .as_deref()
            .is_some_and(|message| message
                .contains("Custom fetch is not supported by the Google Vertex adapter")),
        "{:?}",
        vertex.error_message
    );
    assert_eq!(custom.calls(), 0);
    assert_eq!(fallback.requests(), 0);
}

#[tokio::test]
async fn allows_google_adapters_to_receive_global_this_fetch_explicitly() {
    let ambient = Fallback::start().await;
    let result = google_generative_ai::stream_simple(
        &create_model("google-generative-ai", &ambient),
        &context(),
        options("test-key", None, None),
    )
    .result()
    .await;

    assert_eq!(ambient.requests(), 1);
    assert!(
        !result
            .error_message
            .as_deref()
            .unwrap_or_default()
            .contains("Custom fetch is not supported"),
        "{:?}",
        result.error_message
    );
}

#[tokio::test]
async fn uses_fetch_for_image_generation() {
    let (custom, fallback) = mock_fetches().await;
    let model: ImageModel = serde_json::from_value(json!({
        "type": "image",
        "id": "test-model",
        "name": "Test Model",
        "api": "openrouter-images",
        "provider": "openrouter",
        "baseUrl": fallback.base_url(),
        "input": ["text"],
        "output": ["image"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
    }))
    .expect("image model");
    let images_context: ImagesContext =
        serde_json::from_value(json!({ "input": [{ "type": "text", "text": "draw" }] }))
            .expect("images context");
    let mut images_options = ImagesOptions::default();
    images_options.request.api_key = Some("test-key".to_owned());
    images_options.request.fetch = Some(Arc::clone(&custom.fetch));
    images_options.request.max_retries = Some(0);

    openrouter_images::generate_images(model, images_context, images_options).await;

    expect_only_custom_fetch(&custom, &fallback);
}
