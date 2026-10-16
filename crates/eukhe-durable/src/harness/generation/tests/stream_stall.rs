//! A provider stream that goes silent after its response headers: the
//! stream-idle deadline fails the attempt as a retryable `stream_stalled`
//! error, the generation's retry policy re-issues the request, and the turn
//! answers instead of holding the run until someone aborts it.

use std::sync::Arc;
use std::time::Duration;

use eukhe_ai::api::builtin::anthropic_messages_api;
use eukhe_ai::auth::{ApiKeyAuth, ApiKeyResolveInput, AuthResult, ModelAuth, ProviderAuth};
use eukhe_ai::models::{
    create_models, create_provider, CreateModelsOptions, CreateProviderOptions, Models, ProviderApi,
};
use eukhe_ai::providers::faux::RegisterFauxProviderOptions;
use eukhe_ai::utils::diagnostics::Thrown;
use eukhe_ai::utils::retry::is_retryable_assistant_error;
use eukhe_types::pi_ai::{AnyModel, AssistantMessage, Message, Model, StopReason};
use futures::future::BoxFuture;
use serde_json::json;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::mpsc;

use crate::harness::tests::chat_support::{all_entries, chat_setup, open_chat, text_of, OpenChat};
use crate::harness::tests::support::context;
use crate::harness::types::{ConversationStreamOptions, InputSubmissionDraft, PartialRetryPolicy};
use crate::storage::MemoryStorage;
use crate::types::{InputSubmission, SubmissionState};

/// What the fake provider does after the response headers of one request.
enum Exchange {
    /// Send these SSE events, then hold the connection open without another
    /// byte (a half-open upstream).
    Stall(Vec<serde_json::Value>),
    /// Send these SSE events and end the response.
    Answer(Vec<serde_json::Value>),
}

/// Reads one request head; the body (if any) is left on the socket.
async fn read_request_head(socket: &mut TcpStream) {
    let mut head = Vec::new();
    let mut byte = [0_u8; 1];
    while !head.ends_with(b"\r\n\r\n") {
        let read = socket.read(&mut byte).await.expect("request bytes");
        assert_ne!(read, 0, "the client closed before its request head");
        head.push(byte[0]);
    }
}

async fn write_chunk(socket: &mut TcpStream, data: &str) {
    let chunk = format!("{:x}\r\n{data}\r\n", data.len());
    socket.write_all(chunk.as_bytes()).await.expect("chunk");
}

/// A local Anthropic-messages endpoint serving `exchanges` in order, one
/// per connection. Returns its base URL and a receiver of the indexes of
/// stalled exchanges whose connection the client closed.
async fn sse_server(exchanges: Vec<Exchange>) -> (String, mpsc::UnboundedReceiver<usize>) {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let base_url = format!("http://{}", listener.local_addr().expect("address"));
    let (closed_sender, closed) = mpsc::unbounded_channel();
    tokio::spawn(async move {
        for (index, exchange) in exchanges.into_iter().enumerate() {
            let (mut socket, _) = listener.accept().await.expect("accept");
            let closed_sender = closed_sender.clone();
            tokio::spawn(async move {
                read_request_head(&mut socket).await;
                socket
                    .write_all(
                        b"HTTP/1.1 200 OK\r\ncontent-type: text/event-stream\r\ntransfer-encoding: chunked\r\n\r\n",
                    )
                    .await
                    .expect("response head");
                let (events, stall) = match exchange {
                    Exchange::Stall(events) => (events, true),
                    Exchange::Answer(events) => (events, false),
                };
                for event in events {
                    let name = event["type"].as_str().expect("event type").to_owned();
                    write_chunk(&mut socket, &format!("event: {name}\ndata: {event}\n\n")).await;
                }
                if stall {
                    // Silent until the client gives up on the connection.
                    let mut rest = [0_u8; 1024];
                    while socket.read(&mut rest).await.is_ok_and(|read| read > 0) {}
                    closed_sender.send(index).expect("test receiver");
                } else {
                    socket.write_all(b"0\r\n\r\n").await.expect("last chunk");
                }
            });
        }
    });
    (base_url, closed)
}

fn message_start() -> serde_json::Value {
    json!({"type": "message_start", "message": {"id": "msg_test", "usage": {"input_tokens": 3, "output_tokens": 0}}})
}

fn text_events(text: &str) -> Vec<serde_json::Value> {
    vec![
        json!({"type": "content_block_start", "index": 0, "content_block": {"type": "text", "text": ""}}),
        json!({"type": "content_block_delta", "index": 0, "delta": {"type": "text_delta", "text": text}}),
    ]
}

fn answer(text: &str) -> Exchange {
    let mut events = vec![message_start()];
    events.extend(text_events(text));
    events.extend([
        json!({"type": "content_block_stop", "index": 0}),
        json!({"type": "message_delta", "delta": {"stop_reason": "end_turn"}, "usage": {"output_tokens": 2}}),
        json!({"type": "message_stop"}),
    ]);
    Exchange::Answer(events)
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

/// Models whose `faux/faux-1` (the chat's model) is an Anthropic-messages
/// model served at `base_url`.
fn anthropic_models_at(base_url: &str) -> Models {
    let model: Model = serde_json::from_value(json!({
        "id": "faux-1",
        "name": "Stalling Claude",
        "api": "anthropic-messages",
        "provider": "faux",
        "baseUrl": base_url,
        "reasoning": false,
        "input": ["text"],
        "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0},
        "contextWindow": 100_000,
        "maxTokens": 4096,
    }))
    .expect("model");
    let provider = create_provider(CreateProviderOptions {
        id: "faux".to_owned(),
        auth: ProviderAuth {
            api_key: Some(Arc::new(TestKey)),
            oauth: None,
        },
        models: vec![AnyModel::Chat(model)].into(),
        api: Some(ProviderApi::Single(anthropic_messages_api())),
        ..CreateProviderOptions::default()
    })
    .expect("provider");
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(provider);
    models
}

fn assistant(message: &Message) -> &AssistantMessage {
    let Message::Assistant(message) = message else {
        panic!("not an assistant message: {message:?}");
    };
    message
}

#[tokio::test(flavor = "multi_thread")]
async fn a_stream_that_stalls_after_its_headers_is_retried_instead_of_holding_the_turn() {
    let mut stalled = vec![message_start()];
    stalled.extend(text_events("half an ans"));
    let (base_url, mut closed) =
        sse_server(vec![Exchange::Stall(stalled), answer("recovered")]).await;
    let setup = chat_setup(RegisterFauxProviderOptions::default())
        .with_models(anthropic_models_at(&base_url));
    setup.settings.update(|settings| {
        settings.stream = Some(ConversationStreamOptions {
            stream_idle_timeout_ms: Some(200.0),
            ..ConversationStreamOptions::default()
        });
        settings.retry = Some(PartialRetryPolicy {
            enabled: Some(true),
            max_retries: Some(1),
            base_delay_ms: Some(1.0),
            ..PartialRetryPolicy::default()
        });
    });
    let OpenChat { harness, root } = open_chat(Arc::new(MemoryStorage::new()), &setup, None)
        .await
        .unwrap();
    harness.resume().unwrap();
    let submission = root
        .submit(InputSubmissionDraft::new("hi"), context())
        .await
        .unwrap();
    // Without the deadline the first attempt never ends; the guard turns
    // that hang into a failure.
    let settled = tokio::time::timeout(Duration::from_secs(60), submission.wait(context()))
        .await
        .expect("the stalled attempt ends and the turn settles")
        .unwrap();
    assert!(
        matches!(
            settled.state,
            SubmissionState::Input(InputSubmission::Done { .. })
        ),
        "{:?}",
        settled.state
    );
    let entries = all_entries(&root, context()).await.unwrap();
    let assistants: Vec<&AssistantMessage> = entries
        .iter()
        .filter(|entry| entry.kind == "pi.assistant")
        .map(|entry| assistant(&entry.model.as_ref().expect("model messages")[0]))
        .collect();
    let [stalled, recovered] = assistants.as_slice() else {
        panic!("two attempts, got {assistants:?}");
    };
    assert_eq!(stalled.stop_reason, StopReason::Error);
    assert_eq!(
        stalled.error_message.as_deref(),
        Some("Provider stream stalled: no stream event for 200ms")
    );
    let failure = serde_json::to_value(stalled.diagnostics.as_ref().expect("diagnostics"))
        .expect("diagnostics JSON");
    assert_eq!(failure[0]["type"], "provider_stream_failure");
    assert_eq!(failure[0]["details"]["kind"], "stream_stalled");
    assert!(is_retryable_assistant_error(stalled));
    assert_eq!(recovered.stop_reason, StopReason::Stop);
    assert_eq!(
        text_of(Some(&Message::Assistant((*recovered).clone()))).as_deref(),
        Some("recovered")
    );
    // The stalled request was aborted: its connection is gone.
    assert_eq!(closed.recv().await, Some(0));
    harness.close(context()).await.unwrap();
}
