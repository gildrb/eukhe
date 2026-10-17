//! "provider token count": with [`ThresholdTokens::Provider`] the threshold
//! check uses the provider's own count of the request; without it, or when
//! the provider has no counter, the local estimate.

use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use eukhe_ai::models::Models;
use eukhe_ai::providers::faux::{FauxModelDefinition, RegisterFauxProviderOptions};
use eukhe_types::pi_ai::{AnyModel, CacheRetention, IndexMap, Model};
use serde_json::{json, Value};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};

use super::{
    history, kinds, open, open_scripted, set_policy, set_retry, summary, text, turn, Chat,
    OpenOptions, BLOCKING, MANUAL,
};
use crate::harness::tests::chat_support::chat_setup;
use crate::harness::tests::support::{context, create_models};
use crate::harness::types::{
    AgentChange, CompactionPolicy, ConversationStreamOptions, FieldChange, ModelRef,
    ThresholdTokens,
};
use crate::storage::MemoryStorage;

/// The window of the test model: [`BLOCKING`] blocks above 1700 tokens.
const WINDOW: u64 = 2000;

/// The count the mock `llama-server` reports: above the blocking threshold.
const PROVIDER_COUNT: usize = 1800;

/// The prompt the mock renders from any chat template request.
const RENDERED: &str = "<|user|>rendered";

/// The header the header-checking mock requires, and its value.
const KEY_HEADER: &str = "x-count-key";
const KEY: &str = "secret";

/// One request the mock server received.
#[derive(Debug, Clone, PartialEq)]
struct Received {
    path: String,
    /// The value of [`KEY_HEADER`], when the request sent it.
    key: Option<String>,
    body: Value,
}

type Log = Arc<Mutex<Vec<Received>>>;

/// How the mock `llama-server` answers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Serve {
    /// Every request.
    Open,
    /// Only requests with [`KEY_HEADER`] set to [`KEY`]; others get 401.
    Keyed,
    /// Never: the connection stays open without a reply.
    Stall,
}

/// Reads one request (head and `content-length` body); `None` at the end of
/// the connection.
async fn read_request(socket: &mut TcpStream) -> Option<Received> {
    let mut head = Vec::new();
    let mut byte = [0_u8; 1];
    while !head.ends_with(b"\r\n\r\n") {
        if socket.read(&mut byte).await.ok()? == 0 {
            return None;
        }
        head.push(byte[0]);
    }
    let head = String::from_utf8(head).expect("ASCII request head");
    let path = head
        .split_whitespace()
        .nth(1)
        .expect("request target")
        .to_owned();
    let header = |wanted: &str| {
        head.lines().find_map(|line| {
            let (name, value) = line.split_once(':')?;
            name.eq_ignore_ascii_case(wanted)
                .then(|| value.trim().to_owned())
        })
    };
    let length =
        header("content-length").map_or(0, |value| value.parse::<usize>().expect("content length"));
    let key = header(KEY_HEADER);
    let mut body = vec![0_u8; length];
    socket.read_exact(&mut body).await.ok()?;
    Some(Received {
        path,
        key,
        body: serde_json::from_slice(&body).expect("JSON body"),
    })
}

/// A local `llama-server` with `/apply-template` and `/tokenize` that
/// answers as `serve` says; logs every request. Returns its root URL.
async fn llama_server(log: Log, serve: Serve) -> String {
    let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
    let root = format!("http://{}", listener.local_addr().expect("address"));
    tokio::spawn(async move {
        loop {
            let (mut socket, _) = listener.accept().await.expect("accept");
            let log = Arc::clone(&log);
            tokio::spawn(async move {
                while let Some(request) = read_request(&mut socket).await {
                    let reply = match request.path.as_str() {
                        "/apply-template" => json!({ "prompt": RENDERED }),
                        "/tokenize" => json!({ "tokens": vec![1; PROVIDER_COUNT] }),
                        other => panic!("unexpected request to {other}"),
                    };
                    let status = match serve {
                        Serve::Open => "200 OK",
                        Serve::Keyed if request.key.as_deref() == Some(KEY) => "200 OK",
                        Serve::Keyed => "401 Unauthorized",
                        Serve::Stall => {
                            log.lock()
                                .unwrap_or_else(PoisonError::into_inner)
                                .push(request);
                            std::future::pending::<()>().await;
                            return;
                        }
                    };
                    log.lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .push(request);
                    let body = reply.to_string();
                    let response = format!(
                        "HTTP/1.1 {status}\r\ncontent-type: application/json\r\ncontent-length: {}\r\n\r\n{body}",
                        body.len()
                    );
                    socket
                        .write_all(response.as_bytes())
                        .await
                        .expect("response");
                }
            });
        }
    });
    root
}

/// Stream settings without request limits beyond the test's own.
fn plain_stream() -> ConversationStreamOptions {
    ConversationStreamOptions {
        cache_retention: Some(CacheRetention::None),
        ..ConversationStreamOptions::default()
    }
}

/// The chat model as a `llama-cpp` provider model served at `root`, so the
/// rulebook gives it the llama.cpp token counter; its answers stay scripted.
/// `stream` is the session's stream settings.
async fn llama_chat(root: &str, stream: ConversationStreamOptions) -> Chat {
    let setup = chat_setup(RegisterFauxProviderOptions {
        provider: Some("llama-cpp".to_owned()),
        models: Some(vec![FauxModelDefinition {
            context_window: Some(WINDOW),
            max_tokens: Some(900),
            ..FauxModelDefinition::new("faux-1")
        }]),
        ..RegisterFauxProviderOptions::default()
    });
    let base_url = format!("{root}/v1");
    let served: Arc<[AnyModel]> = setup
        .faux
        .models()
        .iter()
        .map(|model| {
            AnyModel::Chat(Model {
                base_url: base_url.clone(),
                ..model.clone()
            })
        })
        .collect();
    let mut provider = setup.faux.provider.clone();
    provider.get_models = Arc::new(move || Ok(Arc::clone(&served)));
    let models: Models = create_models();
    models.set_provider(provider);
    let chat = open_scripted(
        setup.with_models(models),
        Arc::new(MemoryStorage::new()),
        |setup| {
            setup.settings.update(|settings| {
                settings.stream = Some(stream);
            });
            set_policy(setup, MANUAL);
            set_retry(setup, 2, 1.0);
        },
    )
    .await;
    chat.root
        .configure(
            AgentChange {
                model: FieldChange::Set(ModelRef {
                    provider: "llama-cpp".to_owned(),
                    model_id: "faux-1".to_owned(),
                }),
                ..AgentChange::default()
            },
            context(),
        )
        .await
        .unwrap();
    chat
}

async fn compactions(chat: &Chat) -> usize {
    kinds(&chat.root)
        .await
        .iter()
        .filter(|kind| *kind == "pi.compaction")
        .count()
}

fn requests(log: &Log) -> Vec<Received> {
    log.lock().unwrap_or_else(PoisonError::into_inner).clone()
}

#[tokio::test]
async fn blocks_on_the_provider_count_when_the_local_estimate_is_below_the_threshold() {
    let log = Log::default();
    let chat = llama_chat(
        &llama_server(Arc::clone(&log), Serve::Open).await,
        plain_stream(),
    )
    .await;
    history(&chat).await;
    chat.set_policy(CompactionPolicy {
        token_count: ThresholdTokens::Provider,
        ..BLOCKING
    });
    chat.faux.summary(summary("SUMMARY"));
    turn(&chat, &text("u4", 20), "a4").await;
    // One count, for the first preparation; the one after the compaction
    // checks no threshold.
    let received = requests(&log);
    assert_eq!(
        received
            .iter()
            .map(|request| request.path.as_str())
            .collect::<Vec<_>>(),
        ["/apply-template", "/tokenize"]
    );
    assert_eq!(
        received[1],
        Received {
            path: "/tokenize".to_owned(),
            key: None,
            body: json!({
                "model": "faux-1",
                "content": RENDERED,
                "add_special": true,
                "parse_special": true,
            }),
        }
    );
    assert_eq!(chat.faux.summary_requests().len(), 1);
    assert_eq!(compactions(&chat).await, 1);
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn sends_no_count_request_when_the_setting_is_off() {
    let log = Log::default();
    let chat = llama_chat(
        &llama_server(Arc::clone(&log), Serve::Open).await,
        plain_stream(),
    )
    .await;
    history(&chat).await;
    chat.set_policy(BLOCKING);
    turn(&chat, &text("u4", 20), "a4").await;
    assert_eq!(requests(&log), []);
    assert_eq!(chat.faux.summary_requests().len(), 0);
    assert_eq!(compactions(&chat).await, 0);
    chat.harness.close(context()).await.unwrap();
}

/// The count request sends the headers of the stream settings: the mock
/// answers only with them, so its count (above the threshold) blocks.
/// Without them it answers 401 and the estimate (below) does not.
#[tokio::test]
async fn the_count_request_sends_the_stream_headers() {
    let log = Log::default();
    let mut headers = IndexMap::new();
    headers.insert(KEY_HEADER.to_owned(), KEY.to_owned());
    let chat = llama_chat(
        &llama_server(Arc::clone(&log), Serve::Keyed).await,
        ConversationStreamOptions {
            headers: Some(headers),
            ..plain_stream()
        },
    )
    .await;
    history(&chat).await;
    chat.set_policy(CompactionPolicy {
        token_count: ThresholdTokens::Provider,
        ..BLOCKING
    });
    chat.faux.summary(summary("SUMMARY"));
    turn(&chat, &text("u4", 20), "a4").await;
    assert_eq!(
        requests(&log)
            .iter()
            .map(|request| (request.path.as_str(), request.key.as_deref()))
            .collect::<Vec<_>>(),
        [("/apply-template", Some(KEY)), ("/tokenize", Some(KEY))]
    );
    assert_eq!(compactions(&chat).await, 1);
    chat.harness.close(context()).await.unwrap();
}

/// A count endpoint that never answers fails at the stream settings'
/// `timeoutMs`: the turn goes on with the local estimate (below the
/// threshold, so no compaction) instead of waiting forever. The outer
/// timeout only turns a hang into a failure.
#[tokio::test]
async fn a_stalled_count_request_times_out_at_the_stream_timeout() {
    let log = Log::default();
    let chat = llama_chat(
        &llama_server(Arc::clone(&log), Serve::Stall).await,
        ConversationStreamOptions {
            timeout_ms: Some(200.0),
            max_retries: Some(0),
            ..plain_stream()
        },
    )
    .await;
    history(&chat).await;
    chat.set_policy(CompactionPolicy {
        token_count: ThresholdTokens::Provider,
        ..BLOCKING
    });
    tokio::time::timeout(Duration::from_secs(20), turn(&chat, &text("u4", 20), "a4"))
        .await
        .expect("the count request obeys the stream timeout");
    assert_eq!(
        requests(&log)
            .iter()
            .map(|request| request.path.as_str())
            .collect::<Vec<_>>(),
        ["/apply-template"]
    );
    assert_eq!(compactions(&chat).await, 0);
    chat.harness.close(context()).await.unwrap();
}

/// The faux provider has no token counter: the check logs it and uses the
/// local estimate, which is above the threshold here.
#[tokio::test]
async fn uses_the_local_estimate_when_the_provider_has_no_counter() {
    let chat = open(OpenOptions {
        context_window: Some(WINDOW),
        ..OpenOptions::default()
    })
    .await;
    history(&chat).await;
    chat.set_policy(CompactionPolicy {
        token_count: ThresholdTokens::Provider,
        ..BLOCKING
    });
    chat.faux.summary(summary("SUMMARY"));
    turn(&chat, &text("u4", 1200), "a4").await;
    assert_eq!(chat.faux.summary_requests().len(), 1);
    assert_eq!(compactions(&chat).await, 1);
    chat.harness.close(context()).await.unwrap();
}
