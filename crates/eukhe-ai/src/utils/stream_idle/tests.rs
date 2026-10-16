//! The stream-idle deadline of `Models` against a local Anthropic-messages
//! endpoint: silence after the response headers fails the stream as a
//! retryable stall and drops the connection; provider events that carry no
//! content still hold it open.

use std::sync::Arc;
use std::time::Duration;

use eukhe_types::pi_ai::{AnyModel, AssistantContentBlock, Context, Model, StopReason};
use futures::future::BoxFuture;
use serde_json::json;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::oneshot;

use crate::api::builtin::anthropic_messages_api;
use crate::auth::{ApiKeyAuth, ApiKeyResolveInput, AuthResult, ModelAuth, ProviderAuth};
use crate::models::{
    create_models, create_provider, CreateModelsOptions, CreateProviderOptions, Models,
    ModelsSimpleStreamOptions, ProviderApi,
};
use crate::types::SimpleStreamOptions;
use crate::utils::diagnostics::Thrown;
use crate::utils::retry::is_retryable_assistant_error;

/// One SSE event of the fake endpoint, sent after `delay`.
struct Paced {
    delay: Duration,
    event: serde_json::Value,
}

fn now(event: serde_json::Value) -> Paced {
    Paced {
        delay: Duration::ZERO,
        event,
    }
}

async fn read_request_head(socket: &mut TcpStream) {
    let mut head = Vec::new();
    let mut byte = [0_u8; 1];
    while !head.ends_with(b"\r\n\r\n") {
        let read = socket.read(&mut byte).await.expect("request bytes");
        assert_ne!(read, 0, "the client closed before its request head");
        head.push(byte[0]);
    }
}

/// Serves one request: SSE headers, then `events`; with `stall`, the
/// connection then stays silent and `closed` fires once the client drops
/// it, otherwise the response ends. Returns the base URL.
async fn serve_once(events: Vec<Paced>, stall: Option<oneshot::Sender<()>>) -> String {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let base_url = format!("http://{}", listener.local_addr().expect("address"));
    tokio::spawn(async move {
        let (mut socket, _) = listener.accept().await.expect("accept");
        read_request_head(&mut socket).await;
        socket
            .write_all(
                b"HTTP/1.1 200 OK\r\ncontent-type: text/event-stream\r\ntransfer-encoding: chunked\r\n\r\n",
            )
            .await
            .expect("response head");
        for Paced { delay, event } in events {
            // The pacing is the stimulus: gaps between wire events.
            tokio::time::sleep(delay).await;
            let name = event["type"].as_str().expect("event type");
            let data = format!("event: {name}\ndata: {event}\n\n");
            let chunk = format!("{:x}\r\n{data}\r\n", data.len());
            socket.write_all(chunk.as_bytes()).await.expect("chunk");
        }
        match stall {
            Some(closed) => {
                let mut rest = [0_u8; 1024];
                while socket.read(&mut rest).await.is_ok_and(|read| read > 0) {}
                closed.send(()).expect("test receiver");
            }
            None => socket.write_all(b"0\r\n\r\n").await.expect("last chunk"),
        }
    });
    base_url
}

struct TestKey;

impl ApiKeyAuth for TestKey {
    #[allow(clippy::unnecessary_literal_bound)] // The trait returns a borrowed name.
    fn name(&self) -> &str {
        "test key"
    }

    fn resolve(
        &self,
        _input: ApiKeyResolveInput,
    ) -> BoxFuture<'_, Result<Option<AuthResult>, Thrown>> {
        Box::pin(async {
            Ok(Some(AuthResult {
                auth: ModelAuth {
                    api_key: Some("test-key".to_owned()),
                    ..ModelAuth::default()
                },
                ..AuthResult::default()
            }))
        })
    }
}

fn models_at(base_url: &str) -> (Models, Model) {
    let model: Model = serde_json::from_value(json!({
        "id": "claude-test",
        "name": "Claude Test",
        "api": "anthropic-messages",
        "provider": "local",
        "baseUrl": base_url,
        "reasoning": false,
        "input": ["text"],
        "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0},
        "contextWindow": 100_000,
        "maxTokens": 4096,
    }))
    .expect("model");
    let provider = create_provider(CreateProviderOptions {
        id: "local".to_owned(),
        auth: ProviderAuth {
            api_key: Some(Arc::new(TestKey)),
            oauth: None,
        },
        models: vec![AnyModel::Chat(model.clone())].into(),
        api: Some(ProviderApi::Single(anthropic_messages_api())),
        ..CreateProviderOptions::default()
    })
    .expect("provider");
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(provider);
    (models, model)
}

fn options(idle_ms: f64) -> ModelsSimpleStreamOptions {
    let mut options = SimpleStreamOptions::default();
    options.stream.request.stream_idle_timeout_ms = Some(idle_ms);
    options.into()
}

fn hello() -> Context {
    serde_json::from_value(json!({
        "messages": [{ "role": "user", "content": "hi", "timestamp": 0 }],
    }))
    .expect("context")
}

fn message_start() -> serde_json::Value {
    json!({"type": "message_start", "message": {"id": "msg_test", "usage": {"input_tokens": 3, "output_tokens": 0}}})
}

#[tokio::test(flavor = "multi_thread")]
async fn a_stream_silent_after_its_headers_fails_as_a_retryable_stall_and_drops_the_connection() {
    let (closed, connection_closed) = oneshot::channel();
    let base_url = serve_once(vec![now(message_start())], Some(closed)).await;
    let (models, model) = models_at(&base_url);
    // Without the deadline the stream never ends; the guard turns that hang
    // into a failure.
    let message = tokio::time::timeout(
        Duration::from_secs(60),
        models.complete_simple(&model, hello(), options(200.0)),
    )
    .await
    .expect("the stalled stream ends");
    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(
        message.error_message.as_deref(),
        Some("Provider stream stalled: no stream event for 200ms")
    );
    let diagnostics = serde_json::to_value(message.diagnostics.as_ref().expect("diagnostics"))
        .expect("diagnostics JSON");
    assert_eq!(diagnostics[0]["type"], "provider_stream_failure");
    assert_eq!(diagnostics[0]["details"]["kind"], "stream_stalled");
    assert!(is_retryable_assistant_error(&message));
    connection_closed
        .await
        .expect("the stalled request's connection is closed");
}

#[tokio::test(flavor = "multi_thread")]
async fn provider_events_without_content_hold_a_stream_open_past_the_deadline() {
    // A usage-only `message_delta` is a provider event with no stream
    // event of its own (like a Responses `response.in_progress`).
    let usage = || Paced {
        delay: Duration::from_millis(100),
        event: json!({"type": "message_delta", "delta": {}, "usage": {"output_tokens": 0}}),
    };
    // Six of them 100 ms apart: 600 ms without a stream event, three times
    // the 200 ms deadline, but never 200 ms without a provider event.
    let mut events = vec![now(message_start())];
    events.extend((0..6).map(|_| usage()));
    events.extend([
        now(json!({"type": "content_block_start", "index": 0, "content_block": {"type": "text", "text": ""}})),
        now(json!({"type": "content_block_delta", "index": 0, "delta": {"type": "text_delta", "text": "Hello"}})),
        now(json!({"type": "content_block_stop", "index": 0})),
        now(json!({"type": "message_delta", "delta": {"stop_reason": "end_turn"}, "usage": {"output_tokens": 1}})),
        now(json!({"type": "message_stop"})),
    ]);
    let base_url = serve_once(events, None).await;
    let (models, model) = models_at(&base_url);
    let message = models
        .complete_simple(&model, hello(), options(200.0))
        .await;
    assert_eq!(
        message.stop_reason,
        StopReason::Stop,
        "{:?}",
        message.error_message
    );
    let [AssistantContentBlock::Text(text)] = message.content.as_slice() else {
        panic!("one text block, got {:?}", message.content);
    };
    assert_eq!(text.text, "Hello");
}
