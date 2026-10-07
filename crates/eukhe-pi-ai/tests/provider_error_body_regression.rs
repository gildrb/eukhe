//! Port of `test/provider-error-body-regression.test.ts`: per-tier provider
//! regression for provider-error-body passthrough. A 403-with-body error runs
//! through the real provider catch path of a body-blind text provider
//! (`openai-completions`), a status-only provider (`openai-responses`), and
//! a body-blind Bedrock provider.
//!
//! TS mocks the SDK clients with `vi.mock`; here the failures are produced
//! at the HTTP layer, where the SDKs build those errors:
//!
//! - `openai` (`FakeAPIError(403, parsedBody)`): the `fetch` option answers
//!   HTTP 403 with the JSON body `{ "error": parsedBody }`, which the SDK
//!   port parses into the same status and parsed body (`error.error`).
//! - `@aws-sdk/client-bedrock-runtime` (`send()` rejects with a service
//!   exception carrying `$metadata.httpStatusCode` and `$response`): a local
//!   HTTP server answers the `ConverseStream` request with that status and
//!   body, and the Bedrock client port builds the service exception from
//!   it. The request is signed with static credentials from the scoped `env`
//!   option (the TS mock client needs none). The 400 case answers with
//!   `x-amzn-errortype: ValidationException`, the error name of the TS mock;
//!   its unread stream body (`_readableState`) is the SDK's consumed response
//!   body, which the port never exposes.
//!
//! The Bedrock 403 mock (`name`/`message` `UnknownError` with a string
//! `$response.body`) is not a shape the real SDK produces from any HTTP
//! response, so that case asserts what a real 403 JSON body yields (checked
//! against TS v1.0.4 with the real SDK); the normalization of the mock error
//! itself is covered in `src/utils/error_body.rs`.

use std::sync::Arc;

use eukhe_pi_ai::api::{bedrock_converse_stream, openai_completions, openai_responses};
use eukhe_pi_ai::providers::all::get_builtin_model;
use eukhe_pi_ai::types::{FetchFunction, ProviderStreamOptions, SimpleStreamOptions};
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{
    AssistantMessage, Context, JsonValue, Model, ProviderEnv, StopReason, TranscriptContext,
};
use serde_json::json;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

fn raw_context() -> Context {
    serde_json::from_value(json!({
        "systemPrompt": "",
        "messages": [{ "role": "user", "content": [{ "type": "text", "text": "hi" }], "timestamp": 0 }],
        "tools": [],
    }))
    .expect("context")
}

/// The shared `normalizeContext({ systemPrompt: "", messages, tools: [] })`.
fn context() -> TranscriptContext {
    normalize_context(raw_context())
}

/// `normalizeContext({ messages: context.messages })`.
fn messages_only_context() -> TranscriptContext {
    let messages = context().into_messages();
    normalize_context(Context {
        system_prompt: None,
        messages,
        tools: None,
    })
}

fn completions_model() -> Model {
    serde_json::from_value(json!({
        "id": "test-model",
        "name": "Test Model",
        "api": "openai-completions",
        "provider": "openrouter",
        "baseUrl": "https://openrouter.ai/api/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 1000,
        "maxTokens": 100,
    }))
    .expect("model")
}

fn responses_model() -> Model {
    serde_json::from_value(json!({
        "id": "gpt-test",
        "name": "GPT Test",
        "api": "openai-responses",
        "provider": "openai",
        "baseUrl": "https://api.openai.com/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 1000,
        "maxTokens": 100,
    }))
    .expect("model")
}

/// The default `openaiMock.parsedBody`.
fn default_parsed_body() -> JsonValue {
    json!({ "error": "blocked by gateway WAF" })
}

/// The mocked `openai` client: every request fails with HTTP 403 carrying
/// `parsed_body` as the error body.
fn openai_forbidden_fetch(parsed_body: &JsonValue) -> FetchFunction {
    let body = json!({ "error": parsed_body }).to_string();
    Arc::new(move |_request: reqwest::Request| {
        let body = body.clone();
        Box::pin(async move {
            let response = http::Response::builder()
                .status(403)
                .header("content-type", "application/json")
                .body(body)
                .expect("mock response");
            Ok(reqwest::Response::from(response))
        })
    })
}

/// `{ apiKey: "test" }` with the mocked `openai` client.
fn openai_options(parsed_body: &JsonValue) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test".to_owned());
    options.stream.request.fetch = Some(openai_forbidden_fetch(parsed_body));
    options
}

fn error_message(output: &AssistantMessage) -> &str {
    output.error_message.as_deref().unwrap_or_default()
}

#[tokio::test]
async fn openai_completions_body_blind_text_surfaces_status_and_body() {
    let output = openai_completions::stream(
        &completions_model(),
        &context(),
        openai_options(&default_parsed_body()),
    )
    .result()
    .await;

    assert_eq!(output.stop_reason, StopReason::Error);
    let message = error_message(&output);
    assert!(message.contains("403"), "{message}");
    assert!(message.contains("blocked by gateway WAF"), "{message}");
    assert_ne!(message, "403 status code (no body)");
}

#[tokio::test]
async fn openai_completions_does_not_double_print_the_openrouter_metadata_raw_extra() {
    // OpenRouter returns the extra reason under error.error.metadata.raw,
    // which is part of the parsed body the normalizer already surfaces. The
    // manual append must not duplicate it.
    let parsed_body = json!({
        "message": "Provider returned error",
        "code": 403,
        "metadata": { "raw": "upstream WAF blocked policy XYZ" },
    });

    let output = openai_completions::stream(
        &completions_model(),
        &context(),
        openai_options(&parsed_body),
    )
    .result()
    .await;

    let message = error_message(&output);
    assert!(
        message.contains("upstream WAF blocked policy XYZ"),
        "{message}"
    );
    assert_eq!(
        message.matches("upstream WAF blocked policy XYZ").count(),
        1,
        "{message}"
    );
}

#[tokio::test]
async fn openai_responses_status_only_keeps_the_prefix_and_surfaces_the_body() {
    let output = openai_responses::stream(
        &responses_model(),
        &context(),
        openai_options(&default_parsed_body()),
    )
    .result()
    .await;

    assert_eq!(output.stop_reason, StopReason::Error);
    let message = error_message(&output);
    assert!(message.contains("OpenAI API error (403)"), "{message}");
    assert!(message.contains("blocked by gateway WAF"), "{message}");
}

/// The Bedrock `send()` failure: one HTTP answer of the local server.
struct BedrockReply {
    status: u16,
    reason: &'static str,
    headers: &'static [(&'static str, &'static str)],
    body: JsonValue,
}

/// Starts a local server answering every request with `reply`; returns its
/// base URL.
async fn start_bedrock_server(reply: BedrockReply) -> String {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let url = format!("http://{}", listener.local_addr().expect("address"));
    let body = reply.body.to_string();
    let mut response = format!(
        "HTTP/1.1 {} {}\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n",
        reply.status,
        reply.reason,
        body.len()
    );
    for (name, value) in reply.headers {
        for part in [*name, ": ", *value, "\r\n"] {
            response.push_str(part);
        }
    }
    response.push_str("\r\n");
    response.push_str(&body);
    tokio::spawn(async move {
        while let Ok((mut socket, _)) = listener.accept().await {
            let response = response.clone();
            tokio::spawn(async move {
                read_request(&mut socket).await;
                let _ = socket.write_all(response.as_bytes()).await;
                let _ = socket.shutdown().await;
            });
        }
    });
    url
}

/// Reads one HTTP/1.1 request with a `content-length` body.
async fn read_request(socket: &mut tokio::net::TcpStream) {
    let mut buffer = Vec::new();
    let mut chunk = [0_u8; 4096];
    loop {
        if let Some(header_end) = buffer
            .windows(4)
            .position(|window| window == b"\r\n\r\n")
            .map(|position| position + 4)
        {
            let head = String::from_utf8_lossy(&buffer[..header_end]).to_ascii_lowercase();
            let content_length = head
                .lines()
                .find_map(|line| line.strip_prefix("content-length:"))
                .and_then(|value| value.trim().parse::<usize>().ok())
                .unwrap_or(0);
            if buffer.len() - header_end >= content_length {
                return;
            }
        }
        match socket.read(&mut chunk).await {
            Ok(0) | Err(_) => return,
            Ok(read) => buffer.extend_from_slice(&chunk[..read]),
        }
    }
}

/// `streamSimple(getModel("amazon-bedrock", id), normalizeContext({ messages }), {})`
/// against the local server.
async fn run_bedrock(model_id: &str, reply: BedrockReply) -> AssistantMessage {
    let url = start_bedrock_server(reply).await;
    let mut model = get_builtin_model("amazon-bedrock", model_id)
        .unwrap_or_else(|| panic!("no built-in model amazon-bedrock/{model_id}"));
    model.base_url = url;
    let mut options = SimpleStreamOptions::default();
    options.stream.request.env = Some(ProviderEnv::from([
        ("AWS_ACCESS_KEY_ID".to_owned(), "AKIDEXAMPLE".to_owned()),
        ("AWS_SECRET_ACCESS_KEY".to_owned(), "secret".to_owned()),
    ]));
    bedrock_converse_stream::stream_simple(&model, &messages_only_context(), options)
        .result()
        .await
}

#[tokio::test]
async fn bedrock_body_blind_surfaces_the_gateway_body_instead_of_unknown_unknown_error() {
    let output = run_bedrock(
        "us.anthropic.claude-opus-4-8",
        BedrockReply {
            status: 403,
            reason: "Forbidden",
            headers: &[],
            body: json!({ "message": "blocked by gateway WAF" }),
        },
    )
    .await;

    assert_eq!(output.stop_reason, StopReason::Error);
    let message = error_message(&output);
    // TS also expects "403": its mock error keeps the body as a string on
    // `$response.body`, so `formatBedrockError` prints `${status}: ${body}`.
    // A real response never produces that error: the SDK parses the JSON
    // body into the message and leaves `$response.body` a consumed stream.
    // TS v1.0.4 with the real SDK (HTTP/1, this server and body) yields
    // exactly the message below, which still surfaces the gateway reason
    // instead of `Unknown: UnknownError`.
    assert_eq!(message, "Unknown: blocked by gateway WAF");
    assert!(message.contains("blocked by gateway WAF"), "{message}");
    assert!(!message.contains("Unknown: UnknownError"), "{message}");
}

#[tokio::test]
async fn bedrock_preserves_the_sdk_validation_message_when_the_response_body_is_a_stream() {
    let output = run_bedrock(
        "global.anthropic.claude-opus-5",
        BedrockReply {
            status: 400,
            reason: "Bad Request",
            headers: &[("x-amzn-errortype", "ValidationException")],
            body: json!({
                "message": "Invocation of model ID anthropic.claude-opus-5 with on-demand throughput isn't supported. Retry with an inference profile.",
            }),
        },
    )
    .await;

    assert_eq!(output.stop_reason, StopReason::Error);
    let message = error_message(&output);
    assert!(
        message.contains("on-demand throughput isn't supported"),
        "{message}"
    );
    assert!(message.contains("inference profile"), "{message}");
    assert!(!message.contains("_readableState"), "{message}");
}
