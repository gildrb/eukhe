//! Test support for the Bedrock ports: a local HTTP/1.1 server speaking the
//! Bedrock `vnd.amazon.eventstream` response encoding (the stand-in for the
//! TS tests' AWS SDK mocks), a process-env guard, and request helpers.

use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use eukhe_chord::context::{AbortController, AbortSignal};
use eukhe_pi_ai::api::bedrock_converse_stream::stream;
use eukhe_pi_ai::providers::all::get_builtin_model;
use eukhe_pi_ai::types::{OnPayload, ProviderStreamOptions};
use eukhe_pi_ai::utils::diagnostics::{ErrorObject, Thrown};
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{
    AssistantMessage, CacheRetention, Context, JsonValue, Message, Model, ProviderEnv, UserContent,
    UserMessage,
};
use serde_json::json;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpListener;

/// `Date.now()`.
pub fn now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |elapsed| {
            u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX)
        })
}

/// A user message with string content.
pub fn user(text: &str) -> Message {
    Message::User(UserMessage {
        content: UserContent::Text(text.into()),
        timestamp: now(),
    })
}

/// A catalog model.
pub fn get_model(provider: &str, id: &str) -> Model {
    get_builtin_model(provider, id).unwrap_or_else(|| panic!("no built-in model {provider}/{id}"))
}

/// A model from its TS object literal.
pub fn model_from(value: JsonValue) -> Model {
    serde_json::from_value(value).expect("valid model literal")
}

/// The base model of the convert-messages tests.
pub fn sonnet_45_model() -> Model {
    model_from(json!({
        "id": "us.anthropic.claude-sonnet-4-5-20250929-v1:0",
        "name": "Claude Sonnet 4.5 (US)",
        "api": "bedrock-converse-stream",
        "provider": "amazon-bedrock",
        "baseUrl": "https://bedrock-runtime.us-east-1.amazonaws.com",
        "reasoning": true,
        "input": ["text", "image"],
        "cost": { "input": 3, "output": 15, "cacheRead": 0.3, "cacheWrite": 3.75 },
        "contextWindow": 200_000,
        "maxTokens": 64_000,
        "compat": { "supportsStrictMode": true },
    }))
}

/// `{ ...model, baseUrl }`.
pub fn with_base_url(model: &Model, base_url: &str) -> Model {
    Model {
        base_url: base_url.to_owned(),
        ..model.clone()
    }
}

/// `{ messages }` normalized.
pub fn context_of(messages: Vec<Message>) -> eukhe_types::pi_ai::TranscriptContext {
    normalize_context(Context {
        system_prompt: None,
        messages,
        tools: None,
    })
}

/// Options with `extra` keys and a scoped env.
pub fn options(extra: JsonValue) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    if let JsonValue::Object(extra) = extra {
        options.extra = extra;
    }
    options
}

/// A provider env from pairs.
pub fn env(pairs: &[(&str, &str)]) -> ProviderEnv {
    pairs
        .iter()
        .map(|(key, value)| ((*key).to_owned(), (*value).to_owned()))
        .collect()
}

/// Env that signs requests to the mock server with static credentials.
pub fn mock_env() -> ProviderEnv {
    env(&[
        ("AWS_ACCESS_KEY_ID", "AKIDEXAMPLE"),
        ("AWS_SECRET_ACCESS_KEY", "secret"),
    ])
}

/// An already aborted signal (TS `AbortSignal.abort()`).
pub fn aborted_signal() -> AbortSignal {
    let controller = AbortController::new();
    controller.abort(None);
    controller.signal()
}

/// The thrown value of the thinking-payload tests' `PayloadCaptured`.
pub fn payload_captured() -> Thrown {
    ErrorObject::named("PayloadCaptured", "payload captured").thrown()
}

/// What an `onPayload` hook returns after recording the payload.
#[derive(Clone, Copy)]
pub enum AfterCapture {
    /// `return payload`.
    Continue,
    /// `throw new PayloadCaptured()`.
    Throw,
}

/// An `onPayload` hook recording the payload into `slot`.
pub fn capture_payload_hook(
    slot: Arc<Mutex<Option<JsonValue>>>,
    after: AfterCapture,
) -> OnPayload<Model> {
    Arc::new(move |payload, _model| {
        let slot = slot.clone();
        Box::pin(async move {
            *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload.clone());
            match after {
                AfterCapture::Continue => Ok(Some(payload)),
                AfterCapture::Throw => Err(payload_captured()),
            }
        })
    })
}

/// The convert-messages / redacted-reasoning `capturePayload`: streams with
/// `cacheRetention: "none"`, an aborted signal, and a recording `onPayload`.
pub async fn capture_payload(model: &Model, messages: Vec<Message>) -> JsonValue {
    capture_payload_context(
        model,
        Context {
            system_prompt: None,
            messages,
            tools: None,
        },
    )
    .await
}

/// [`capture_payload`] for a full context (prompt and tools).
pub async fn capture_payload_context(model: &Model, context: Context) -> JsonValue {
    let _env = EnvGuard::new(&[]).await;
    let slot = Arc::new(Mutex::new(None));
    let mut options = ProviderStreamOptions::default();
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.signal = Some(aborted_signal());
    options.stream.request.on_payload =
        Some(capture_payload_hook(slot.clone(), AfterCapture::Continue));
    let result = stream(model, &normalize_context(context), options)
        .result()
        .await;
    assert_eq!(result.stop_reason, eukhe_types::pi_ai::StopReason::Aborted);
    let payload = slot.lock().unwrap_or_else(PoisonError::into_inner).take();
    payload.expect("Expected Bedrock payload to be captured before request abort")
}

/// Encodes one event-stream message with string headers.
pub fn frame(headers: &[(&str, &str)], body: &[u8]) -> Vec<u8> {
    let mut header_bytes = Vec::new();
    for (name, value) in headers {
        header_bytes.push(u8::try_from(name.len()).expect("short header name"));
        header_bytes.extend_from_slice(name.as_bytes());
        header_bytes.push(7);
        header_bytes.extend_from_slice(
            &u16::try_from(value.len())
                .expect("short value")
                .to_be_bytes(),
        );
        header_bytes.extend_from_slice(value.as_bytes());
    }
    let length = header_bytes.len() + body.len() + 16;
    let mut out = Vec::with_capacity(length);
    out.extend_from_slice(&u32::try_from(length).expect("small frame").to_be_bytes());
    out.extend_from_slice(
        &u32::try_from(header_bytes.len())
            .expect("small headers")
            .to_be_bytes(),
    );
    let prelude_crc = crc32fast::hash(&out);
    out.extend_from_slice(&prelude_crc.to_be_bytes());
    out.extend_from_slice(&header_bytes);
    out.extend_from_slice(body);
    let message_crc = crc32fast::hash(&out);
    out.extend_from_slice(&message_crc.to_be_bytes());
    out
}

/// An `event` message for one `ConverseStreamOutput` item `{ [type]: body }`.
pub fn event_frame(item: &JsonValue) -> Vec<u8> {
    let (event_type, body) = item
        .as_object()
        .and_then(|object| object.iter().next())
        .expect("one-key item");
    frame(
        &[
            (":message-type", "event"),
            (":event-type", event_type),
            (":content-type", "application/json"),
        ],
        body.to_string().as_bytes(),
    )
}

/// An `exception` message.
pub fn exception_frame(exception_type: &str, body: &JsonValue) -> Vec<u8> {
    frame(
        &[
            (":message-type", "exception"),
            (":exception-type", exception_type),
            (":content-type", "application/json"),
        ],
        body.to_string().as_bytes(),
    )
}

/// An unmodeled `error` message.
pub fn error_frame(code: &str, message: &str) -> Vec<u8> {
    frame(
        &[
            (":message-type", "error"),
            (":error-code", code),
            (":error-message", message),
        ],
        b"",
    )
}

/// The event-stream body of `items`.
pub fn event_stream(items: &[JsonValue]) -> Vec<u8> {
    items.iter().flat_map(event_frame).collect()
}

/// One canned HTTP answer.
#[derive(Clone)]
pub enum Reply {
    /// A complete response.
    Response {
        status: u16,
        headers: Vec<(String, String)>,
        body: Vec<u8>,
    },
    /// A 200 event-stream response whose body ends early: the connection
    /// closes after `body` although more bytes were announced.
    Truncated {
        headers: Vec<(String, String)>,
        body: Vec<u8>,
    },
    /// Close the connection without answering.
    Hangup,
}

impl Reply {
    /// A 200 event-stream response.
    pub fn events(headers: &[(&str, &str)], body: Vec<u8>) -> Self {
        let mut all = vec![(
            "content-type".to_owned(),
            "application/vnd.amazon.eventstream".to_owned(),
        )];
        all.extend(
            headers
                .iter()
                .map(|(name, value)| ((*name).to_owned(), (*value).to_owned())),
        );
        Self::Response {
            status: 200,
            headers: all,
            body,
        }
    }

    /// A JSON error response.
    pub fn json(status: u16, headers: &[(&str, &str)], body: &JsonValue) -> Self {
        let mut all = vec![("content-type".to_owned(), "application/json".to_owned())];
        all.extend(
            headers
                .iter()
                .map(|(name, value)| ((*name).to_owned(), (*value).to_owned())),
        );
        Self::Response {
            status,
            headers: all,
            body: body.to_string().into_bytes(),
        }
    }
}

/// One request the server received.
#[derive(Debug, Clone)]
pub struct CapturedRequest {
    pub method: String,
    pub path: String,
    /// Lowercased names, in arrival order.
    pub headers: Vec<(String, String)>,
    pub body: String,
}

impl CapturedRequest {
    pub fn header(&self, name: &str) -> Option<&str> {
        self.headers
            .iter()
            .find(|(key, _)| key == name)
            .map(|(_, value)| value.as_str())
    }
}

/// A local Bedrock stand-in answering each request with the next reply
/// (the last reply repeats).
pub struct MockBedrock {
    pub url: String,
    requests: Arc<Mutex<Vec<CapturedRequest>>>,
}

impl MockBedrock {
    pub async fn start(replies: Vec<Reply>) -> Self {
        let listener = TcpListener::bind("127.0.0.1:0").await.expect("bind");
        let url = format!("http://{}", listener.local_addr().expect("address"));
        let requests = Arc::new(Mutex::new(Vec::new()));
        let recorded = requests.clone();
        tokio::spawn(async move {
            let mut served = 0usize;
            loop {
                let Ok((mut socket, _)) = listener.accept().await else {
                    return;
                };
                let reply = replies
                    .get(served)
                    .or_else(|| replies.last())
                    .cloned()
                    .expect("at least one reply");
                served += 1;
                let Some(request) = read_request(&mut socket).await else {
                    continue;
                };
                recorded
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(request);
                let _ = write_reply(&mut socket, reply).await;
            }
        });
        Self { url, requests }
    }

    pub fn requests(&self) -> Vec<CapturedRequest> {
        self.requests
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

async fn read_request(socket: &mut tokio::net::TcpStream) -> Option<CapturedRequest> {
    let mut buffer = Vec::new();
    let mut chunk = [0u8; 8192];
    let header_end = loop {
        let read = socket.read(&mut chunk).await.ok()?;
        if read == 0 {
            return None;
        }
        buffer.extend_from_slice(&chunk[..read]);
        if let Some(position) = buffer.windows(4).position(|window| window == b"\r\n\r\n") {
            break position;
        }
    };
    let head = String::from_utf8_lossy(&buffer[..header_end]).into_owned();
    let mut lines = head.split("\r\n");
    let mut request_line = lines.next()?.split(' ');
    let method = request_line.next()?.to_owned();
    let path = request_line.next()?.to_owned();
    let headers: Vec<(String, String)> = lines
        .filter_map(|line| line.split_once(':'))
        .map(|(name, value)| (name.trim().to_lowercase(), value.trim().to_owned()))
        .collect();
    let length: usize = headers
        .iter()
        .find(|(name, _)| name == "content-length")
        .and_then(|(_, value)| value.parse().ok())
        .unwrap_or(0);
    let mut body = buffer[header_end + 4..].to_vec();
    while body.len() < length {
        let read = socket.read(&mut chunk).await.ok()?;
        if read == 0 {
            break;
        }
        body.extend_from_slice(&chunk[..read]);
    }
    Some(CapturedRequest {
        method,
        path,
        headers,
        body: String::from_utf8_lossy(&body).into_owned(),
    })
}

async fn write_reply(socket: &mut tokio::net::TcpStream, reply: Reply) -> std::io::Result<()> {
    let (status, headers, body, announced) = match reply {
        Reply::Hangup => return socket.shutdown().await,
        Reply::Response {
            status,
            headers,
            body,
        } => {
            let length = body.len();
            (status, headers, body, length)
        }
        Reply::Truncated { headers, body } => {
            let mut all = vec![(
                "content-type".to_owned(),
                "application/vnd.amazon.eventstream".to_owned(),
            )];
            all.extend(headers);
            let length = body.len() + 64;
            (200, all, body, length)
        }
    };
    let mut head = format!("HTTP/1.1 {status} Status\r\n");
    for (name, value) in &headers {
        head.push_str(name);
        head.push_str(": ");
        head.push_str(value);
        head.push_str("\r\n");
    }
    head.push_str("content-length: ");
    head.push_str(&announced.to_string());
    head.push_str("\r\nconnection: close\r\n\r\n");
    socket.write_all(head.as_bytes()).await?;
    socket.write_all(&body).await?;
    socket.flush().await?;
    socket.shutdown().await
}

/// The AWS / proxy variables the Bedrock module reads from the process env.
const ENV_KEYS: [&str; 18] = [
    "AWS_REGION",
    "AWS_DEFAULT_REGION",
    "AWS_PROFILE",
    "AWS_ACCESS_KEY_ID",
    "AWS_SECRET_ACCESS_KEY",
    "AWS_SESSION_TOKEN",
    "AWS_BEARER_TOKEN_BEDROCK",
    "AWS_BEDROCK_SKIP_AUTH",
    "AWS_BEDROCK_FORCE_HTTP1",
    "AWS_BEDROCK_FORCE_CACHE",
    "AWS_USE_FIPS_ENDPOINT",
    "AWS_USE_DUALSTACK_ENDPOINT",
    "PI_CACHE_RETENTION",
    "HTTP_PROXY",
    "HTTPS_PROXY",
    "http_proxy",
    "https_proxy",
    "ALL_PROXY",
];

static ENV_LOCK: LazyLock<tokio::sync::Mutex<()>> = LazyLock::new(|| tokio::sync::Mutex::new(()));

/// Serializes the tests of this binary on the process env (TS
/// `vi.stubEnv`): clears the Bedrock variables, applies `values`, and
/// restores everything on drop.
pub struct EnvGuard {
    saved: Vec<(&'static str, Option<String>)>,
    _lock: tokio::sync::MutexGuard<'static, ()>,
}

impl EnvGuard {
    pub async fn new(values: &[(&str, &str)]) -> Self {
        let lock = ENV_LOCK.lock().await;
        let saved = ENV_KEYS
            .iter()
            .map(|key| (*key, std::env::var(key).ok()))
            .collect();
        for key in ENV_KEYS {
            std::env::remove_var(key);
        }
        // The SDK default chains must not reach real metadata services.
        std::env::set_var("AWS_EC2_METADATA_DISABLED", "true");
        for (key, value) in values {
            std::env::set_var(key, value);
        }
        Self { saved, _lock: lock }
    }

    /// `process.env[key] = value` while the guard holds the env.
    #[allow(clippy::unused_self)] // The guard proves the env lock is held.
    pub fn set(&self, key: &str, value: &str) {
        std::env::set_var(key, value);
    }
}

impl Drop for EnvGuard {
    fn drop(&mut self) {
        for (key, value) in &self.saved {
            match value {
                Some(value) => std::env::set_var(key, value),
                None => std::env::remove_var(key),
            }
        }
    }
}

/// `message.diagnostics?.find((d) => d.type === type)` as JSON.
pub fn find_diagnostic(message: &AssistantMessage, kind: &str) -> Option<JsonValue> {
    message
        .diagnostics
        .as_ref()?
        .iter()
        .find(|diagnostic| diagnostic.kind == kind)
        .map(|diagnostic| serde_json::to_value(diagnostic).expect("serializes"))
}
