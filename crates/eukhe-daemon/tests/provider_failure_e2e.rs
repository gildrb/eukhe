//! End-to-end verifier for interactive provider-failure handling: a daemon
//! worker session against a failing (then healing) OpenAI-compatible mock
//! must retry the turn per the shared retry policy, surface each retry
//! (`auto_retry_start`), close the loop (`auto_retry_end`), render the
//! failed assistant message, and end the turn with the error. The
//! success-after-retry path must settle the same loop with `success: true`.
// Pedantic-gate dispositions (fleet-uniform ruling; see this lane's PR for
// the full rationale).
// Stack-resident futures by design on the daemon's hot paths; boxing the
// call sites for a lint tick is a perf regression with zero correctness gain.
#![allow(clippy::large_futures)]
// 64-bit-only targets; the narrowing casts sit at OS boundaries
// (pid/fd/time/size) where the values are bounded by the kernel - the
// dead-guard expect()s would add panic paths where silent wrap was
// deliberate.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]
// The fn-length threshold is a style gate, not correctness; the structure
// campaign owns the god-fn splits as a follow-up.
#![allow(clippy::too_many_lines)]
// API-shape opinions, not defects; the surfaces are deliberate.
#![allow(
    clippy::unnecessary_wraps,
    clippy::zero_sized_map_values,
    clippy::struct_excessive_bools,
    clippy::struct_field_names
)]
use std::fmt::Write as _;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

// The durable session storage reader the CLI e2e suites share.
#[path = "../../eukhe-cli/tests/support/durable_store.rs"]
mod durable_store;

struct Supervisor {
    child: Child,
    #[allow(dead_code)]
    socket: PathBuf,
}

impl Drop for Supervisor {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// A mock OpenAI-completions provider: the first `failures` requests get a
/// 500 with an OpenAI-style error body; the rest get one fixed SSE answer.
struct FailingMock {
    requests: Arc<Mutex<usize>>,
    port: u16,
}

/// How the mock rejects its first `failures` requests.
#[derive(Clone, Copy)]
enum MockRejection {
    /// A plain 500 with an OpenAI-style server-error body.
    ServerError,
    /// The prime-inference storm shape: 429 with `Retry-After` and the
    /// "Too many concurrent requests" body.
    RateLimit { retry_after_secs: u64 },
    /// THE 402 REGRESSION (the diagnosis's variant B): a wallet-drain
    /// 402 whose body carries the prime-inference `invalid_request_error`
    /// type text — the shape that classified permanent on the first
    /// attempt and settled SILENTLY (no retry episode, so no outcome
    /// row) before the failure-scoped disclosure.
    PaymentRequired,
}

impl FailingMock {
    fn start_with_rejection(
        failures: usize,
        answer: &'static str,
        rejection: MockRejection,
    ) -> FailingMock {
        let requests = Arc::new(Mutex::new(0usize));
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind mock");
        let port = listener.local_addr().expect("mock addr").port();
        let requests_for_thread = Arc::clone(&requests);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(stream) = stream else { continue };
                let requests = Arc::clone(&requests_for_thread);
                std::thread::spawn(move || {
                    let _ = serve(stream, failures, answer, rejection, &requests);
                });
            }
        });
        FailingMock { requests, port }
    }

    fn url(&self) -> String {
        format!("http://127.0.0.1:{}/v1", self.port)
    }

    fn count(&self) -> usize {
        *self.requests.lock().expect("mock lock")
    }
}

fn chunk(delta: &Value, finish_reason: Option<&str>) -> String {
    json!({
        "id": "chatcmpl-test",
        "object": "chat.completion.chunk",
        "created": 1_750_000_000,
        "model": "mock-1",
        "choices": [{"index": 0, "delta": delta, "finish_reason": finish_reason}],
    })
    .to_string()
}

fn serve(
    mut stream: TcpStream,
    failures: usize,
    answer: &str,
    rejection: MockRejection,
    requests: &Arc<Mutex<usize>>,
) -> std::io::Result<()> {
    let mut reader = BufReader::new(stream.try_clone()?);
    let mut head = String::new();
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line)? == 0 {
            return Ok(());
        }
        head.push_str(&line);
        if line == "\r\n" {
            break;
        }
    }
    let mut content_length = 0usize;
    for line in head.lines() {
        let lower = line.to_ascii_lowercase();
        if let Some(value) = lower.strip_prefix("content-length:") {
            content_length = value.trim().parse().unwrap_or_default();
        }
    }
    let mut body_bytes = vec![0u8; content_length];
    if content_length > 0 {
        reader.read_exact(&mut body_bytes)?;
    }
    // The supervisor's chat-memory compactor runs on its own provider,
    // routed under `/memory` (`setup_with_rejection`): it always succeeds
    // and never counts, so the counter and the scripted failures stay the
    // session's provider requests.
    let memory_request = head
        .lines()
        .next()
        .and_then(|request_line| request_line.split_whitespace().nth(1))
        .is_some_and(|path| path.starts_with("/memory/"));
    if memory_request {
        return write_answer(&mut stream, "user: said hi");
    }
    let index = {
        let mut requests = requests.lock().expect("mock lock");
        *requests += 1;
        *requests
    };
    if index <= failures {
        let (status_line, headers, body) = match rejection {
            MockRejection::ServerError => (
                "HTTP/1.1 500 Internal Server Error",
                String::new(),
                json!({
                    "error": { "message": "mock provider overloaded", "type": "server_error", "code": 500 }
                })
                .to_string(),
            ),
            MockRejection::PaymentRequired => (
                "HTTP/1.1 402 Payment Required",
                String::new(),
                json!({
                    "error": {
                        "message": "402 Insufficient balance (team wallet drained)",
                        "type": "invalid_request_error",
                        "code": 402
                    }
                })
                .to_string(),
            ),
            MockRejection::RateLimit { retry_after_secs } => (
                "HTTP/1.1 429 Too Many Requests",
                format!("Retry-After: {retry_after_secs}\r\n"),
                json!({
                    "error": {
                        "message": "429 Too many concurrent requests for this model (limit: 32). Try again shortly.",
                        "type": "rate_limit_error",
                        "code": 429
                    }
                })
                .to_string(),
            ),
        };
        return stream.write_all(
            format!(
                "{status_line}\r\nContent-Type: application/json\r\n{headers}Content-Length: {}\r\nConnection: close\r\n\r\n{}",
                body.len(),
                body
            )
            .as_bytes(),
        );
    }
    write_answer(&mut stream, answer)
}

/// One successful streamed completion carrying `content`.
fn write_answer(stream: &mut TcpStream, content: &str) -> std::io::Result<()> {
    let mut payload = String::new();
    for data in [
        chunk(&json!({"role": "assistant", "content": content}), None),
        chunk(&json!({}), Some("stop")),
    ] {
        write!(payload, "data: {data}\n\n").expect("write to String");
    }
    payload.push_str("data: [DONE]\n\n");
    stream.write_all(
        format!(
            "HTTP/1.1 200 OK\r\nContent-Type: text/event-stream\r\nConnection: close\r\n\r\n{payload}"
        )
        .as_bytes(),
    )
}

#[allow(clippy::zombie_processes)]
fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Supervisor {
    std::fs::create_dir_all(agent_dir).expect("agent dir");
    let child = Command::new(env!("CARGO_BIN_EXE_eukhe-daemon"))
        .arg("supervisor")
        .arg("--socket")
        .arg(socket)
        .arg("--agent-dir")
        .arg(agent_dir)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .env_remove("PRIME_API_KEY")
        .env_remove("EUKHE_CODING_AGENT_DIR")
        // A supervisor killed at teardown must not leak its session workers
        // into later test binaries: the worker's supervisor-lost exit (TS
        // `exitIfSupervisorOrphanedForTooLong`) runs on this short window
        // instead of the 5-minute default.
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "15000",
        )
        .spawn()
        .expect("spawn eukhe-daemon supervisor");
    let deadline = Instant::now() + Duration::from_secs(10);
    while Instant::now() < deadline {
        if socket.exists() {
            return Supervisor {
                child,
                socket: socket.to_path_buf(),
            };
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    panic!("supervisor socket never appeared");
}

/// One client connection: request/response plus every session event that
/// streamed while the response was outstanding.
struct Client {
    reader: BufReader<std::os::unix::net::UnixStream>,
    writer: std::os::unix::net::UnixStream,
    events: Vec<Value>,
}

impl Client {
    fn connect(socket: &Path) -> Client {
        let stream = std::os::unix::net::UnixStream::connect(socket).expect("connect");
        let writer = stream.try_clone().expect("clone");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
            events: Vec::new(),
        };
        let hello = client.read_line();
        assert_eq!(hello["type"], "daemon_hello");
        client
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        let deadline = Instant::now() + Duration::from_mins(1);
        self.reader
            .get_mut()
            .set_read_timeout(Some(Duration::from_millis(100)))
            .expect("timeout");
        loop {
            match self.reader.read_line(&mut line) {
                Ok(0) => panic!("supervisor closed the connection"),
                Ok(_) if line.trim().is_empty() => line.clear(),
                Ok(_) => return serde_json::from_str(line.trim()).expect("parse line"),
                Err(error) => {
                    assert!(
                        Instant::now() < deadline,
                        "timed out waiting for supervisor line: {error}"
                    );
                }
            }
        }
    }

    fn send_command(&mut self, id: &str, command: &Value) {
        let envelope = json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "command": command,
        });
        let mut line = serde_json::to_string(&envelope).expect("serialize");
        line.push('\n');
        self.writer
            .write_all(line.as_bytes())
            .unwrap_or_else(|error| panic!("write command {id}: {error}"));
    }

    /// The response for `id`, with every session event observed on the way.
    fn request(&mut self, id: &str) -> Value {
        let deadline = Instant::now() + Duration::from_mins(2);
        loop {
            assert!(Instant::now() < deadline, "no response for id {id}");
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                return line;
            }
            self.collect_event(&line);
        }
    }

    fn collect_event(&mut self, line: &Value) {
        if line.get("type").and_then(Value::as_str) == Some("session_event") {
            self.events.push(line["event"].clone());
        }
    }

    /// Drain pending session events until the socket stays quiet for
    /// `quiet_ms`. The supervisor buffers a client's session events while a
    /// routed command (`prompt_and_wait`) is in flight and writes them after
    /// its response, so a caller that stops at the response would miss the
    /// whole turn.
    fn drain_events(&mut self, quiet_ms: Duration) {
        let deadline = Instant::now() + Duration::from_secs(30);
        let mut last_line = Instant::now();
        let mut line = String::new();
        loop {
            assert!(Instant::now() < deadline, "event drain timed out");
            self.reader
                .get_mut()
                .set_read_timeout(Some(Duration::from_millis(100)))
                .expect("timeout");
            match self.reader.read_line(&mut line) {
                Ok(0) => return,
                Ok(_) => {
                    let value: Value = serde_json::from_str(line.trim()).expect("parse line");
                    self.collect_event(&value);
                    last_line = Instant::now();
                    line.clear();
                }
                Err(_) => {
                    if last_line.elapsed() >= quiet_ms {
                        return;
                    }
                }
            }
        }
    }

    /// Collect session events until one matching `found` arrived (each line
    /// read is bounded by `read_line`'s own deadline).
    fn wait_for_event(&mut self, what: &str, found: impl Fn(&Value) -> bool) {
        let deadline = Instant::now() + Duration::from_mins(2);
        while !self.events.iter().any(&found) {
            assert!(Instant::now() < deadline, "never observed {what}");
            let line = self.read_line();
            self.collect_event(&line);
        }
    }
}

/// Shared harness: supervisor + models.json + fast retry settings + a
/// created, attached session. The supervisor handle must outlive the test
/// body: dropping it kills the supervisor process and closes the client
/// socket mid-turn.
fn setup(
    name: &str,
    failures: usize,
    answer: &'static str,
) -> (tempfile::TempDir, FailingMock, Supervisor, Client, String) {
    setup_with_rejection(name, failures, answer, MockRejection::ServerError)
}

/// The shared harness with a choosable mock rejection mode (the 429 storm).
#[allow(clippy::type_complexity)]
fn setup_with_rejection(
    name: &str,
    failures: usize,
    answer: &'static str,
    rejection: MockRejection,
) -> (tempfile::TempDir, FailingMock, Supervisor, Client, String) {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let mock = FailingMock::start_with_rejection(failures, answer, rejection);
    std::fs::write(
        agent_dir.join("models.json"),
        json!({
            "providers": {
                "prime-inference": {
                    "api": "openai-completions",
                    "baseUrl": mock.url(),
                    "apiKey": "sk-battery",
                    "models": [
                        {
                            "id": "mock-1",
                            "name": "Mock 1",
                            "api": "openai-completions",
                            "contextWindow": 128_000,
                            "maxTokens": 4096
                        }
                    ]
                },
                // The chat-memory compactor's provider: the supervisor
                // summarizes every logged message, and without
                // `memory.model` it runs on the default model — this
                // mock's prime-inference route — so its requests would
                // land in the session's provider accounting.
                "chat-memory": {
                    "api": "openai-completions",
                    "baseUrl": format!("http://127.0.0.1:{}/memory", mock.port),
                    "apiKey": "sk-memory",
                    "models": [
                        {
                            "id": "summarizer",
                            "name": "Summarizer",
                            "api": "openai-completions",
                            "contextWindow": 128_000,
                            "maxTokens": 4096
                        }
                    ]
                }
            }
        })
        .to_string(),
    )
    .expect("write models.json");
    // A fast retry policy so the test asserts the loop, not the delays.
    std::fs::write(
        agent_dir.join("settings.json"),
        json!({
            "retry": { "enabled": true, "maxRetries": 2, "baseDelayMs": 50 },
            "memory": { "model": "chat-memory/summarizer" }
        })
        .to_string(),
    )
    .expect("write settings.json");
    let socket = dir.path().join(format!("{name}.sock"));
    let supervisor = spawn_supervisor(&socket, &agent_dir);
    let mut client = Client::connect(&socket);
    client.send_command(
        "c1",
        &json!({
            "type": "create",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": session_dir.to_string_lossy(),
                "provider": "prime-inference",
                "model": "mock-1",
            },
        }),
    );
    let created = client.request("c1");
    assert_eq!(created["success"], true, "create failed: {created}");
    let session_id = created["data"]["id"]
        .as_str()
        .or_else(|| created["data"]["sessionId"].as_str())
        .expect("session id")
        .to_string();
    client.send_command(
        "a1",
        &json!({ "type": "attach", "activeSessionId": session_id }),
    );
    let attached = client.request("a1");
    assert_eq!(attached["success"], true, "attach failed: {attached}");
    (dir, mock, supervisor, client, session_id)
}

fn event_types(events: &[Value]) -> Vec<String> {
    events
        .iter()
        .filter_map(|event| event.get("type").and_then(Value::as_str))
        .map(str::to_string)
        .collect()
}

#[test]
fn provider_failure_is_retried_then_surfaced_to_attached_clients() {
    let (_dir, mock, _supervisor, mut client, session_id) = setup("failing", 5, "never reached");
    client.send_command(
        "p1",
        &json!({ "type": "prompt_and_wait", "activeSessionId": session_id, "message": "hi" }),
    );
    let done = client.request("p1");
    assert_eq!(done["success"], false, "prompt must fail: {done}");
    client.drain_events(Duration::from_secs(1));

    // The retry policy applied: one initial request plus two retries.
    assert_eq!(mock.count(), 3, "requests: initial + 2 retries");

    // The accepted user message is a message_start + message_end pair
    // (TS wire), and an unchanged queue projection stays silent (TS
    // `_emitQueueUpdate` dedup): no session_action_update frames here.
    let types = event_types(&client.events);
    assert!(
        !types.iter().any(|t| t == "session_action_update"),
        "an empty-to-empty queue is not an update, events: {types:?}"
    );
    let user_pairs = client
        .events
        .iter()
        .filter(|event| {
            event.get("type").and_then(Value::as_str) == Some("message_start")
                && event["message"]["role"] == "user"
        })
        .count();
    let user_ends = client
        .events
        .iter()
        .filter(|event| {
            event.get("type").and_then(Value::as_str) == Some("message_end")
                && event["message"]["role"] == "user"
        })
        .count();
    assert_eq!(user_pairs, 1, "one user message_start, events: {types:?}");
    assert_eq!(user_ends, 1, "one user message_end, events: {types:?}");

    assert!(
        types.iter().filter(|t| *t == "auto_retry_start").count() == 2,
        "two retry starts expected, events: {types:?}"
    );
    // Each retry start carries the attempt and delay (50ms then 100ms).
    let starts: Vec<&Value> = client
        .events
        .iter()
        .filter(|event| event.get("type").and_then(Value::as_str) == Some("auto_retry_start"))
        .collect();
    assert_eq!(starts[0]["attempt"], 1);
    assert_eq!(starts[0]["maxAttempts"], 2);
    assert!(starts[0]["errorMessage"]
        .as_str()
        .expect("error message")
        .contains("mock provider overloaded"));
    assert_eq!(starts[1]["attempt"], 2);
    // Each retry start's delay sits around its ladder step (50ms then
    // 100ms: [40, 70] and [80, 140]). pi-durable schedules the step exactly
    // (no jitter, unlike the old engine's ±20%); the band stays as headroom.
    let jitter_band = |base: u64| (base * 4 / 5, base * 7 / 5);
    for (start, base) in starts.iter().zip([50u64, 100u64]) {
        let delay = start["delayMs"].as_u64().expect("delayMs");
        let (low, high) = jitter_band(base);
        assert!(
            (low..=high).contains(&delay),
            "jittered delay {delay} outside [{low}, {high}]"
        );
    }

    // The loop closes with the final failure surfaced.
    let end = client
        .events
        .iter()
        .rev()
        .find(|event| event.get("type").and_then(Value::as_str) == Some("auto_retry_end"))
        .expect("auto_retry_end");
    assert_eq!(end["success"], false);
    assert_eq!(end["attempt"], 2);
    assert!(end["finalError"]
        .as_str()
        .expect("final error")
        .contains("mock provider overloaded"));

    // The failed assistant message reached the transcript: message_end with
    // stopReason error and the provider message.
    let failure = client
        .events
        .iter()
        .filter(|event| event.get("type").and_then(Value::as_str) == Some("message_end"))
        .find(|event| {
            event["message"]["role"] == "assistant" && event["message"]["stopReason"] == "error"
        })
        .expect("failed assistant message_end");
    assert!(failure["message"]["errorMessage"]
        .as_str()
        .expect("error message")
        .contains("mock provider overloaded"));

    // The turn ends with the TS `turn_end` shape: the terminal frame
    // carries the failed assistant message as its payload (no separate
    // error field on the frame — TS `turn_end` never carries one).
    let turn_end = client
        .events
        .iter()
        .rev()
        .find(|event| event.get("type").and_then(Value::as_str) == Some("turn_end"))
        .expect("turn_end");
    assert_eq!(turn_end["message"]["role"], "assistant");
    assert_eq!(turn_end["message"]["stopReason"], "error");
    assert!(turn_end["message"]["errorMessage"]
        .as_str()
        .expect("turn error")
        .contains("mock provider overloaded"));
    assert_eq!(turn_end.get("error"), None, "turn_end: {turn_end}");
    assert_eq!(
        turn_end["toolResults"].as_array().map(Vec::len),
        Some(0),
        "the failed turn ran no tools"
    );

    // The single-line retry UX (SANCTIONED DIVERGENCE, operator ruling
    // 2026-09-23): the episode leaves ONE durable outcome row — the
    // terminal line, broadcast after `auto_retry_end` as a custom-row
    // message pair — instead of only the per-attempt error rows TS keeps.
    let outcome_pair: Vec<&Value> = client
        .events
        .iter()
        .filter(|event| {
            matches!(
                event.get("type").and_then(Value::as_str),
                Some("message_start" | "message_end")
            ) && event["message"]["role"] == "custom"
                && event["message"]["customType"] == "provider_retry_outcome"
        })
        .collect();
    assert_eq!(outcome_pair.len(), 2, "one outcome row pair: {types:?}");
    let outcome = &outcome_pair[0]["message"];
    assert_eq!(outcome["details"]["success"], false);
    assert_eq!(outcome["details"]["attempts"], 2);
    assert!(
        outcome["content"]
            .as_str()
            .expect("outcome text")
            .contains("Retry failed after 2 attempts"),
        "outcome text: {outcome}"
    );
    assert!(outcome["content"]
        .as_str()
        .expect("outcome text")
        .contains("mock provider overloaded"));
}

/// The 429-storm simulation (operator ruling 2026-09-23): a provider that
/// rate-limits with `Retry-After` gets retried with bounded exponential
/// backoff — requests cap at initial + maxRetries (never spam), and the
/// episode leaves exactly ONE durable outcome row while the per-attempt
/// failures still persist and stream (full transcript fidelity; the TUI
/// collapses the rows).
///
/// pi-durable decides the waits: its generation retry schedules the
/// policy's exponential ladder (`baseDelayMs * 2^(attempt-1)`, no jitter)
/// and does not read `Retry-After`, so the old engine's honored-and-
/// jittered server wait ([800, 1400] ms here) is not the durable shape.
#[test]
fn storm_429_caps_requests_and_leaves_one_outcome_row() {
    let (_dir, mock, _supervisor, mut client, session_id) = setup_with_rejection(
        "storm429",
        2,
        "recovered answer",
        MockRejection::RateLimit {
            retry_after_secs: 1,
        },
    );
    client.send_command(
        "p1",
        &json!({ "type": "prompt_and_wait", "activeSessionId": session_id, "message": "hi" }),
    );
    let done = client.request("p1");
    assert_eq!(done["success"], true, "prompt must recover: {done}");
    client.drain_events(Duration::from_secs(1));

    // The request cap: one initial request + maxRetries (2) retries. A
    // storm can never spam the endpoint past the policy budget.
    assert_eq!(mock.count(), 3, "requests: initial + 2 retries");

    let types = event_types(&client.events);
    // Both 429 attempts stream their failures (wire parity with TS), two
    // retry starts pace the waits, and the loop closes recovered.
    let failed_attempts = client
        .events
        .iter()
        .filter(|event| {
            event.get("type").and_then(Value::as_str) == Some("message_end")
                && event["message"]["role"] == "assistant"
                && event["message"]["stopReason"] == "error"
        })
        .count();
    assert_eq!(
        failed_attempts, 2,
        "each attempt's failure streams: {types:?}"
    );
    assert!(
        types.iter().filter(|t| *t == "auto_retry_start").count() == 2,
        "two retry starts, events: {types:?}"
    );
    let starts: Vec<&Value> = client
        .events
        .iter()
        .filter(|event| event.get("type").and_then(Value::as_str) == Some("auto_retry_start"))
        .collect();
    for (start, base) in starts.iter().zip([50u64, 100]) {
        assert!(
            start["errorMessage"]
                .as_str()
                .expect("error message")
                .contains("Too many concurrent requests"),
            "the 429 text: {start}"
        );
        // The policy ladder (50 ms, then 100 ms; see the doc above), with
        // rounding headroom.
        let delay = start["delayMs"].as_u64().expect("delayMs");
        let (low, high) = (base * 4 / 5, base * 7 / 5);
        assert!(
            (low..=high).contains(&delay),
            "ladder delay {delay} outside [{low}, {high}]"
        );
    }
    let end = client
        .events
        .iter()
        .rev()
        .find(|event| event.get("type").and_then(Value::as_str) == Some("auto_retry_end"))
        .expect("auto_retry_end");
    assert_eq!(end["success"], true);

    // ONE durable outcome row: broadcast as the custom pair right after
    // the auto_retry_end frame, naming the recovered error.
    let outcome = client
        .events
        .iter()
        .find(|event| {
            event.get("type").and_then(Value::as_str) == Some("message_start")
                && event["message"]["role"] == "custom"
                && event["message"]["customType"] == "provider_retry_outcome"
        })
        .expect("the outcome row pair");
    let text = outcome["message"]["content"].as_str().expect("content");
    assert!(
        text.contains("Recovered after 2 retries") && text.contains("Too many concurrent requests"),
        "outcome text: {text}"
    );
    assert_eq!(outcome["message"]["details"]["success"], true);
    assert_eq!(outcome["message"]["details"]["attempts"], 2);

    // The transcript holds the per-attempt failures (full fidelity — the
    // collapse is a TUI presentation rule) plus exactly ONE outcome row.
    client.send_command(
        "g1",
        &json!({ "type": "get_messages", "activeSessionId": session_id }),
    );
    let messages = client.request("g1");
    let list = messages["data"]["messages"].as_array().expect("messages");
    let persisted_failures = list
        .iter()
        .filter(|message| message["role"] == "assistant" && message["stopReason"] == "error")
        .count();
    assert_eq!(persisted_failures, 2, "full per-attempt fidelity: {list:?}");
    let outcomes = list
        .iter()
        .filter(|message| {
            message["role"] == "custom" && message["customType"] == "provider_retry_outcome"
        })
        .count();
    assert_eq!(outcomes, 1, "exactly one outcome row: {list:?}");
}

/// THE 402 REGRESSION (the diagnosis's variant B — the Mac's per-turn
/// shape): a wallet-drain 402 whose body carries the
/// `invalid_request_error` type text must (1) classify by STATUS — the
/// deterministic `payment_required` kind — so it settles on the FIRST
/// attempt with no retry ladder burning 13-15s on a dead wallet, and
/// (2) still emit the failure-scoped disclosure row: the turn never
/// settles as a silent empty message.
#[test]
fn payment_402_settles_once_with_the_disclosure() {
    let (_dir, mock, _supervisor, mut client, session_id) =
        setup_with_rejection("p402", 5, "never reached", MockRejection::PaymentRequired);
    client.send_command(
        "p1",
        &json!({ "type": "prompt_and_wait", "activeSessionId": session_id, "message": "hi" }),
    );
    let done = client.request("p1");
    assert_eq!(done["success"], false, "prompt must fail: {done}");
    client.drain_events(Duration::from_secs(1));

    // The 402 is permanent on the first attempt: exactly ONE provider
    // request, no retry ladder on the dead wallet.
    assert_eq!(mock.count(), 1, "requests: the 402 settles once");

    // The failure-scoped disclosure row fired with attempt 0 (the
    // pre-fix silent arm: no episode, no row).
    let outcome_pair: Vec<&Value> = client
        .events
        .iter()
        .filter(|event| {
            matches!(
                event.get("type").and_then(Value::as_str),
                Some("message_start" | "message_end")
            ) && event["message"]["role"] == "custom"
                && event["message"]["customType"] == "provider_retry_outcome"
        })
        .collect();
    assert_eq!(
        outcome_pair.len(),
        2,
        "one outcome row pair: {:?}",
        event_types(&client.events)
    );
    let outcome = &outcome_pair[0]["message"];
    assert_eq!(outcome["details"]["success"], false);
    assert_eq!(outcome["details"]["attempts"], 0);
    let text = outcome["content"].as_str().expect("outcome text");
    assert!(
        text.contains("Insufficient balance (team wallet drained)"),
        "outcome text: {text}"
    );
    assert!(
        !text.contains("Retry failed"),
        "no retry ran, so the zero-attempt text reads as the plain failure: {text}"
    );
}

/// THE GOAL-SIDE 402 REGRESSION (the diagnosis's repro contract): a goal
/// whose continuation turn dies on the wallet-drain 402 refuses the NEXT
/// continuation and finishes the goal — the pre-fix behavior minted a
/// fresh continuation into the dead provider every boundary (the
/// operator's 64-cycle hot loop). The turn's disclosure row still fires
/// (BUG 1), and exactly ONE provider request runs: the loop is dead at
/// the first failed boundary.
#[test]
fn goal_continuation_refuses_after_the_402_corpse() {
    let (dir, mock, _supervisor, mut client, session_id) = setup_with_rejection(
        "p402goal",
        5,
        "never reached",
        MockRejection::PaymentRequired,
    );
    // Arm the goal through the session command path (no model call),
    // like the operator's live session: the initial continuation row
    // queues and drives the first turn.
    client.send_command(
        "g1",
        &json!({
            "type": "prompt_and_wait",
            "activeSessionId": session_id,
            "message": "/goal start Ship the feature end to end."
        }),
    );
    let done = client.request("g1");
    // The durable `/goal` command answers once the goal is set and its
    // continuation submitted: the goal loop runs in-run (pi-durable's
    // `on_yield` continuation), so a waited answer would only come when
    // the whole goal ends. The old engine settled the command with the
    // first turn's error; here the turn's failure is observed after it.
    assert_eq!(done["success"], true, "the goal command answers: {done}");
    let is_outcome_start = |event: &Value| {
        event.get("type").and_then(Value::as_str) == Some("message_start")
            && event["message"]["role"] == "custom"
            && event["message"]["customType"] == "provider_retry_outcome"
    };
    client.wait_for_event("the goal turn's disclosure row", is_outcome_start);
    client.drain_events(Duration::from_secs(1));
    let failure = client
        .events
        .iter()
        .find(|event| {
            event.get("type").and_then(Value::as_str) == Some("message_end")
                && event["message"]["role"] == "assistant"
                && event["message"]["stopReason"] == "error"
        })
        .expect("the goal turn's failed assistant message_end");
    assert!(
        failure["message"]["errorMessage"]
            .as_str()
            .expect("error text")
            .contains("Insufficient balance"),
        "the failure is the turn's 402: {failure}"
    );

    // The single failed continuation turn: ONE provider request (the
    // 402 is permanent), NO re-minted continuation after it.
    assert_eq!(mock.count(), 1, "no continuation loop: one request total");

    // The durable goal state: the errored turn finished the goal. The
    // durable store keeps the goal as the main conversation's `eukhe.goal`
    // document (the old `thread_goal_state` rows' payload).
    let storage = durable_store::session_dirs(&dir.path().join("agent").join("sessions"));
    assert_eq!(storage.len(), 1, "one session storage: {storage:?}");
    let latest = stored_goal(&storage[0]);
    assert_eq!(
        latest["status"], "error",
        "the goal finished on the errored turn: {latest}"
    );
    assert_eq!(latest["active"], false);
    assert!(
        latest["lastError"]
            .as_str()
            .expect("last error text")
            .contains("Insufficient balance"),
        "the goal's error is the turn's 402: {latest}"
    );

    // The failure-scoped disclosure row still fired (BUG 1).
    let outcome_rows = client
        .events
        .iter()
        .filter(|event| is_outcome_start(event))
        .count();
    assert_eq!(
        outcome_rows, 1,
        "one disclosure row: the silent arm is gone"
    );

    // The failed continuation pair left the live loop context (BUG 2
    // (c)): the transcript keeps the rows, the loop context does not.
    // Re-read the session messages: the goal_context row and the corpse
    // remain durable (the transcript's full fidelity) — the CONTEXT
    // effect is asserted by the one-request count above (a re-minted
    // continuation would have re-prompted).
}

/// The main conversation's stored `eukhe.goal` document in the durable
/// storage `dir`.
fn stored_goal(dir: &Path) -> Value {
    use eukhe_core::durable::{read_main_transcript, read_session_document, SessionLocation};
    let location = SessionLocation::Durable(dir.to_path_buf());
    let cx = &eukhe_chord::context::BACKGROUND_CONTEXT;
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("runtime");
    let goal = runtime.block_on(async {
        let main = read_main_transcript(&location, cx)
            .await
            .expect("transcript readable")
            .main;
        read_session_document(&location, &eukhe_core::durable::goals::GOAL_DOC, main, cx)
            .await
            .expect("goal document readable")
    });
    serde_json::to_value(goal).expect("goal JSON")
}

/// A direct-transport client (thin-supervisor stage 2): ticket from the: ticket from the
/// supervisor, `peer_auth` + `attach` on the worker's own socket. The turn
/// events must stream live on this path (the per-connection fan-out writes
/// while the routed command is still in flight).
struct DirectClient {
    stream: std::os::unix::net::UnixStream,
}

impl DirectClient {
    fn connect(socket: &Path, ticket: &Value, session_id: &str) -> DirectClient {
        let mut client = DirectClient {
            stream: std::os::unix::net::UnixStream::connect(socket).expect("connect worker"),
        };
        client
            .stream
            .set_read_timeout(Some(Duration::from_millis(100)))
            .expect("timeout");
        let (header, _hello) = client.read_frame();
        assert_eq!(header["outboundType"], "daemon_hello");
        let auth = client.request(
            "peer_auth",
            &json!({
                "type": "peer_auth",
                "grantId": ticket["grantId"],
                "token": ticket["token"],
                "workerInstanceId": ticket["workerInstanceId"],
                "purpose": "session_client",
            }),
        );
        assert_eq!(auth["success"], true, "peer auth failed: {auth}");
        let attach = client.request(
            "attach",
            &json!({
                "type": "attach",
                "activeSessionId": session_id,
                "capabilities": ["attach_snapshot", "event_sequence", "slim_attach"],
            }),
        );
        assert_eq!(attach["success"], true, "direct attach failed: {attach}");
        client
    }

    fn send_frame(&mut self, command_type: &str, request_id: &str, payload: &Value) {
        let header = json!({
            "kind": "command",
            "requestId": request_id,
            "commandType": command_type,
        });
        let frame = eukhe_daemon::framing::encode_private_frame(
            &header,
            &serde_json::to_vec(payload).expect("payload"),
            eukhe_daemon::framing::DEFAULT_PRIVATE_FRAME_LIMITS,
        )
        .expect("encode frame");
        self.stream.write_all(&frame).expect("write frame");
        self.stream.flush().expect("flush");
    }

    fn read_frame(&mut self) -> (Value, Value) {
        let deadline = Instant::now() + Duration::from_mins(1);
        let (header, payload) = self
            .read_frame_soft(deadline)
            .expect("worker frame read timed out");
        (header, payload)
    }

    /// One frame read that returns `None` at `deadline` instead of panicking:
    /// for bounded post-response drains whose end is "no more frames".
    fn read_frame_soft(&mut self, deadline: Instant) -> Option<(Value, Value)> {
        let mut prefix = [0u8; 8];
        read_exact_soft(&mut self.stream, &mut prefix, deadline)?;
        let header_len = u32::from_be_bytes(prefix[0..4].try_into().unwrap()) as usize;
        let payload_len = u32::from_be_bytes(prefix[4..8].try_into().unwrap()) as usize;
        let mut header = vec![0u8; header_len];
        read_exact_soft(&mut self.stream, &mut header, deadline)?;
        let mut payload = vec![0u8; payload_len];
        read_exact_soft(&mut self.stream, &mut payload, deadline)?;
        let header: Value = serde_json::from_slice(&header).expect("frame header");
        let payload: Value = serde_json::from_slice(&payload).expect("frame payload");
        Some((header, payload))
    }

    fn request(&mut self, command_type: &str, payload: &Value) -> Value {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        let request_id = format!(
            "req-{}",
            NEXT.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
        );
        self.send_frame(command_type, &request_id, payload);
        let deadline = Instant::now() + Duration::from_mins(2);
        loop {
            assert!(Instant::now() < deadline, "no response for {request_id}");
            let (header, body) = self.read_frame();
            if header["outboundType"] == "response" && header["requestId"] == request_id {
                return body;
            }
        }
    }
}

/// One frame read with a soft deadline: `None` when no complete
/// frame arrives in time (a worker close still panics mid-frame).
fn read_exact_soft(
    stream: &mut std::os::unix::net::UnixStream,
    buffer: &mut [u8],
    deadline: Instant,
) -> Option<()> {
    let mut read = 0usize;
    while read < buffer.len() {
        if Instant::now() >= deadline {
            return None;
        }
        match stream.read(&mut buffer[read..]) {
            Ok(0) => panic!("worker closed the connection mid-frame"),
            Ok(n) => read += n,
            Err(error)
                if error.kind() == std::io::ErrorKind::WouldBlock
                    || error.kind() == std::io::ErrorKind::TimedOut => {}
            Err(error) => panic!("worker read: {error}"),
        }
    }
    Some(())
}

#[test]
fn provider_failure_surfaces_on_the_direct_transport_path() {
    let (_dir, mock, _supervisor, mut client, session_id) = setup("direct", 5, "never reached");

    // Ticket -> peer_auth -> attach on the worker's own socket.
    client.send_command(
        "ticket",
        &json!({ "type": "get_direct_worker_transport", "activeSessionId": session_id }),
    );
    let ticket = client.request("ticket");
    assert_eq!(ticket["success"], true, "ticket failed: {ticket}");
    let mut direct = DirectClient::connect(
        Path::new(ticket["data"]["socketPath"].as_str().expect("socket path")),
        &ticket["data"],
        &session_id,
    );

    // The prompt rides the direct connection; the session events stream
    // live on the same socket while the command is in flight.
    direct.send_frame(
        "prompt_and_wait",
        "p-direct",
        &json!({ "type": "prompt_and_wait", "activeSessionId": session_id, "message": "hi" }),
    );
    let mut events: Vec<Value> = Vec::new();
    let mut response = None;
    let deadline = Instant::now() + Duration::from_mins(2);
    while response.is_none() {
        assert!(Instant::now() < deadline, "direct prompt never settled");
        let (header, body) = direct.read_frame();
        match header["outboundType"].as_str() {
            Some("session_event") => events.push(body["event"].clone()),
            Some("response") if header["requestId"] == "p-direct" => {
                assert_eq!(body["success"], false, "direct prompt must fail: {body}");
                assert!(
                    body["error"]
                        .as_str()
                        .expect("turn error")
                        .contains("mock provider overloaded"),
                    "unexpected error: {body}"
                );
                response = Some(body);
            }
            _ => {}
        }
    }
    // The response and the per-connection event fan-out are separate writer
    // tasks, so under load the trailing event frames can land just after the
    // response. Drain with a bounded wait until the retry loop settled; the
    // events themselves still prove live streaming (the worker has no
    // post-response replay mechanism).
    let settle = Instant::now() + Duration::from_secs(10);
    loop {
        let mut retry_starts = 0;
        let mut retry_end = false;
        let mut failed_message_end = false;
        for event in &events {
            match event.get("type").and_then(Value::as_str) {
                Some("auto_retry_start") => retry_starts += 1,
                Some("auto_retry_end") => retry_end = true,
                Some("message_end")
                    if event["message"]["role"] == "assistant"
                        && event["message"]["stopReason"] == "error" =>
                {
                    failed_message_end = true;
                }
                _ => {}
            }
        }
        if retry_starts == 2 && retry_end && failed_message_end {
            break;
        }
        match direct.read_frame_soft(settle) {
            Some((header, body)) => {
                if header["outboundType"] == "session_event" {
                    events.push(body["event"].clone());
                }
            }
            None => break,
        }
    }
    let types = event_types(&events);
    assert_eq!(
        types.iter().filter(|t| *t == "auto_retry_start").count(),
        2,
        "two retry starts expected, events: {types:?}"
    );
    let end = events
        .iter()
        .rev()
        .find(|event| event.get("type").and_then(Value::as_str) == Some("auto_retry_end"))
        .expect("auto_retry_end observed on the direct socket");
    assert_eq!(end["success"], false);
    let failure = events
        .iter()
        .filter(|event| event.get("type").and_then(Value::as_str) == Some("message_end"))
        .find(|event| {
            event["message"]["role"] == "assistant" && event["message"]["stopReason"] == "error"
        })
        .expect("failed assistant message_end");
    assert!(failure["message"]["errorMessage"]
        .as_str()
        .expect("error message")
        .contains("mock provider overloaded"));

    // The retry policy applied on this path too: initial + two retries.
    assert_eq!(mock.count(), 3, "requests: initial + 2 retries");
}

#[test]
fn provider_failure_recovered_by_retry_settles_the_turn() {
    let (_dir, mock, _supervisor, mut client, session_id) = setup("healing", 2, "recovered reply");
    client.send_command(
        "p1",
        &json!({ "type": "prompt_and_wait", "activeSessionId": session_id, "message": "hi" }),
    );
    let done = client.request("p1");
    assert_eq!(done["success"], true, "prompt must succeed: {done}");
    client.drain_events(Duration::from_secs(1));

    // Two failures then the third attempt succeeds.
    assert_eq!(mock.count(), 3);

    let types = event_types(&client.events);
    assert!(
        types.iter().filter(|t| *t == "auto_retry_start").count() == 2,
        "two retry starts expected, events: {types:?}"
    );
    let end = client
        .events
        .iter()
        .rev()
        .find(|event| event.get("type").and_then(Value::as_str) == Some("auto_retry_end"))
        .expect("auto_retry_end");
    assert_eq!(end["success"], true);
    assert_eq!(end["attempt"], 2);
    assert!(end.get("finalError").is_none(), "no final error: {end}");

    // The recovered reply is the turn's final message.
    let last_message = client
        .events
        .iter()
        .filter(|event| event.get("type").and_then(Value::as_str) == Some("message_end"))
        .rev()
        .find(|event| event["message"]["role"] == "assistant")
        .expect("final assistant message");
    assert_eq!(last_message["message"]["stopReason"], "stop");
    assert_eq!(
        last_message["message"]["content"][0]["text"],
        "recovered reply"
    );

    // One `agent_end` per agent run, carrying the run's whole message set.
    // pi-durable retries inside the run (its generation's attempt loop:
    // the failed attempts stay in the run, the next attempt starts after
    // the backoff without a run boundary), so the recovered episode is ONE
    // run — not TS's restarted run per retry with its own
    // `agent_start`/`turn_start` and `messages.slice(0, -1)` payloads.
    let agent_ends: Vec<&Value> = client
        .events
        .iter()
        .filter(|event| event.get("type").and_then(Value::as_str) == Some("agent_end"))
        .collect();
    assert_eq!(agent_ends.len(), 1, "one run for the episode: {types:?}");
    let messages = agent_ends[0]["messages"]
        .as_array()
        .expect("agent_end carries the run's messages");
    assert_eq!(
        messages.first().map(|message| &message["role"]),
        Some(&json!("user")),
        "the run opens with the prompt: {messages:?}"
    );
    // The run's attempts in order: both failed rows, then the recovered
    // answer (full fidelity: the failures stay in the run's message set).
    let attempts: Vec<&Value> = messages
        .iter()
        .filter(|message| message["role"] == "assistant")
        .collect();
    let stop_reasons: Vec<&Value> = attempts
        .iter()
        .map(|message| &message["stopReason"])
        .collect();
    assert_eq!(
        stop_reasons,
        [&json!("error"), &json!("error"), &json!("stop")],
        "the run's attempts: {messages:?}"
    );
    assert_eq!(
        attempts[2]["content"][0]["text"],
        json!("recovered reply"),
        "the recovered attempt's settled row"
    );
    assert_eq!(
        types.iter().filter(|t| *t == "agent_start").count(),
        1,
        "one agent_start for the run: {types:?}"
    );
    assert_eq!(
        types.iter().filter(|t| *t == "turn_start").count(),
        1,
        "one turn_start: the retries stay in the turn: {types:?}"
    );
}
