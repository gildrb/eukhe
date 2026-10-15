//! A scripted OpenAI-compatible provider for the daemon e2e suites that
//! must outlive a worker: it runs in the test process, so a `SIGKILL`ed
//! worker's replacement reaches the same script and the same request log.
//!
//! The test's script answers each request from its content: the request's
//! kind (a session turn, a compaction summarizer call, a chat-memory
//! compactor call), its last user text and whether a tool result follows
//! it. A reply can be held mid-stream on a named gate: the first chunk goes
//! out, then the stream waits until the test opens the gate or the client
//! hangs up (the killed worker), which the log records.

#![allow(dead_code)] // each including test binary uses its own subset

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

/// The pi compaction summarizer's fixed system prompt marker.
pub const SUMMARIZER_MARKER: &str = "context summarization assistant";

/// What a request is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RequestKind {
    /// A session's model call.
    Turn,
    /// The pi compaction summarizer.
    Summarizer,
    /// The chat-memory compactor (one tree line).
    MemoryNode,
}

/// One request as the script sees it.
#[derive(Debug, Clone)]
pub struct Request {
    pub index: usize,
    pub kind: RequestKind,
    /// The text of the last user message the harness did not add itself
    /// (on a chat-memory root, the view and then the turn's message or the
    /// compactor's task).
    pub last_user_text: String,
    /// The last line of `last_user_text`: the prompt itself (prompts of
    /// the scripts are one line).
    pub prompt: String,
    /// Whether a tool result follows that message (the call after a tool
    /// ran).
    pub after_tool: bool,
    /// The tool call ids answered so far in the request.
    pub tool_results: Vec<String>,
    /// The request's size as this provider counts it (JSON chars / 4).
    pub prompt_tokens: u64,
    pub body: Value,
}

/// What the script answers.
#[derive(Debug, Clone)]
pub enum ReplyContent {
    Text(String),
    ToolCall {
        id: String,
        name: String,
        arguments: Value,
    },
    /// A context-overflow error (HTTP 400, the `OpenAI` text).
    Overflow,
}

#[derive(Debug, Clone)]
pub struct Reply {
    pub content: ReplyContent,
    /// Hold the stream after its first chunk until this gate opens.
    pub hold: Option<String>,
}

impl Reply {
    pub fn text(text: impl Into<String>) -> Reply {
        Reply {
            content: ReplyContent::Text(text.into()),
            hold: None,
        }
    }

    pub fn tool_call(id: impl Into<String>, name: impl Into<String>, arguments: Value) -> Reply {
        Reply {
            content: ReplyContent::ToolCall {
                id: id.into(),
                name: name.into(),
                arguments,
            },
            hold: None,
        }
    }

    pub fn overflow() -> Reply {
        Reply {
            content: ReplyContent::Overflow,
            hold: None,
        }
    }

    #[must_use]
    pub fn held(mut self, gate: impl Into<String>) -> Reply {
        self.hold = Some(gate.into());
        self
    }
}

/// How one request ended on this side.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Served {
    /// Still streaming or held.
    Open,
    /// The whole reply went out.
    Complete,
    /// The client hung up first (held stream of a killed worker).
    Dropped,
    /// Answered with the context-overflow error.
    Overflowed,
}

/// One logged request.
#[derive(Debug, Clone)]
pub struct Logged {
    pub request: Request,
    pub reply: Reply,
    pub served: Served,
    /// Set while the stream waits on its gate.
    pub holding: bool,
}

type Script = dyn Fn(&Request) -> Reply + Send + Sync;

struct State {
    log: Vec<Logged>,
    open_gates: BTreeSet<String>,
    /// Requests over this many tokens get the overflow error whatever the
    /// script says (the provider's own context window).
    window: Option<u64>,
    /// Bumped on every request and stream state change.
    changes: u64,
}

struct Shared {
    state: Mutex<State>,
    changed: Condvar,
    script: Box<Script>,
}

impl Shared {
    fn lock(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Change the state under the lock and wake every waiter.
    fn update<T>(&self, change: impl FnOnce(&mut State) -> T) -> T {
        let mut state = self.lock();
        let result = change(&mut state);
        state.changes += 1;
        drop(state);
        self.changed.notify_all();
        result
    }
}

/// The running mock.
#[derive(Clone)]
pub struct MockLlm {
    shared: Arc<Shared>,
    port: u16,
}

impl MockLlm {
    /// Start serving `script`, without a context window of its own.
    pub fn start(script: impl Fn(&Request) -> Reply + Send + Sync + 'static) -> MockLlm {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind the mock provider");
        let port = listener.local_addr().expect("mock address").port();
        let shared = Arc::new(Shared {
            state: Mutex::new(State {
                log: Vec::new(),
                open_gates: BTreeSet::new(),
                window: None,
                changes: 0,
            }),
            changed: Condvar::new(),
            script: Box::new(script),
        });
        let accept = Arc::clone(&shared);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(stream) = stream else { continue };
                let shared = Arc::clone(&accept);
                std::thread::spawn(move || serve(&shared, stream));
            }
        });
        MockLlm { shared, port }
    }

    /// Enforce a context window: a request over `window` tokens gets the
    /// context-overflow error.
    pub fn set_window(&self, window: u64) {
        self.shared.update(|state| state.window = Some(window));
    }

    /// A counter that moves on every request and stream state change.
    pub fn changes(&self) -> u64 {
        self.shared.lock().changes
    }

    pub fn url(&self) -> String {
        format!("http://127.0.0.1:{}/v1", self.port)
    }

    /// A `models.json` serving `model_id` from this mock as provider
    /// `mock`.
    pub fn models_json(&self, model_id: &str, context_window: u64, max_tokens: u64) -> Value {
        json!({
            "providers": {
                "mock": {
                    "api": "openai-completions",
                    "baseUrl": self.url(),
                    "apiKey": "sk-mock",
                    "models": [{
                        "id": model_id,
                        "name": model_id,
                        "api": "openai-completions",
                        "contextWindow": context_window,
                        "maxTokens": max_tokens,
                    }]
                }
            }
        })
    }

    pub fn open_gate(&self, gate: &str) {
        self.shared
            .update(|state| state.open_gates.insert(gate.to_string()));
    }

    /// A copy of the request log.
    pub fn log(&self) -> Vec<Logged> {
        self.shared.lock().log.clone()
    }

    /// Wait until `probe` holds over the log, failing after `budget`. A
    /// request or stream state change wakes the wait at once; the probe
    /// also runs every 50 ms, for a probe that reads state outside the log
    /// (a client's responses).
    pub fn wait_for<T>(
        &self,
        budget: Duration,
        what: &str,
        probe: impl Fn(&[Logged]) -> Option<T>,
    ) -> T {
        let deadline = Instant::now() + budget;
        let mut state = self.shared.lock();
        loop {
            if let Some(found) = probe(&state.log) {
                return found;
            }
            let now = Instant::now();
            assert!(
                now < deadline,
                "{what} never happened; log: {:#?}",
                summary(&state.log)
            );
            state = self
                .shared
                .changed
                .wait_timeout(state, (deadline - now).min(Duration::from_millis(50)))
                .unwrap_or_else(PoisonError::into_inner)
                .0;
        }
    }
}

/// One line per logged request, for failure messages.
pub fn summary(log: &[Logged]) -> Vec<String> {
    log.iter()
        .map(|entry| {
            let text: String = entry.request.prompt.chars().take(60).collect();
            format!(
                "#{} {:?} after_tool={} tokens={} {:?} {:?} {text:?}",
                entry.request.index,
                entry.request.kind,
                entry.request.after_tool,
                entry.request.prompt_tokens,
                entry.served,
                entry.reply.content,
            )
        })
        .collect()
}

fn message_text(message: &Value) -> String {
    match &message["content"] {
        Value::String(text) => text.clone(),
        Value::Array(blocks) => blocks
            .iter()
            .filter_map(|block| block["text"].as_str())
            .collect::<Vec<_>>()
            .join("\n"),
        _ => String::new(),
    }
}

/// A user message the harness adds on its own (`[harness-digest]`,
/// `[python-state]`, ...): never a prompt.
fn is_harness_notice(message: &Value) -> bool {
    let text = message_text(message);
    text.starts_with('[')
        && text
            .split_once("]\n")
            .is_some_and(|(tag, _)| !tag.contains(' '))
}

fn classify(index: usize, body: Value, raw_len: usize) -> Request {
    let messages = body["messages"].as_array().cloned().unwrap_or_default();
    let prompt_at = messages
        .iter()
        .rposition(|message| message["role"] == "user" && !is_harness_notice(message));
    let last_user_text = prompt_at
        .map(|at| message_text(&messages[at]))
        .unwrap_or_default();
    let summarizer = messages
        .iter()
        .any(|message| message_text(message).contains(SUMMARIZER_MARKER));
    // A chat-memory request carries the view first, then the turn's
    // message or the compactor's task.
    let memory_node = [
        "Compaction: compress message",
        "Compaction: merge lines",
        "Too long: your line is",
    ]
    .iter()
    .any(|task| last_user_text.contains(task));
    let kind = if summarizer {
        RequestKind::Summarizer
    } else if memory_node {
        RequestKind::MemoryNode
    } else {
        RequestKind::Turn
    };
    // A tool ran after the prompt: harness notices may follow its result.
    let after_tool = messages
        .iter()
        .skip(prompt_at.map_or(0, |at| at + 1))
        .any(|message| message["role"] == "tool");
    let tool_results = messages
        .iter()
        .filter(|message| message["role"] == "tool")
        .filter_map(|message| message["tool_call_id"].as_str().map(str::to_string))
        .collect();
    Request {
        index,
        kind,
        prompt: last_user_text
            .lines()
            .last()
            .unwrap_or_default()
            .to_string(),
        last_user_text,
        after_tool,
        tool_results,
        prompt_tokens: (raw_len / 4) as u64,
        body,
    }
}

fn read_request(stream: &TcpStream) -> std::io::Result<Option<(Value, usize)>> {
    let mut reader = BufReader::new(stream.try_clone()?);
    let mut content_length = 0usize;
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line)? == 0 {
            return Ok(None);
        }
        if line == "\r\n" {
            break;
        }
        if let Some(value) = line.to_ascii_lowercase().strip_prefix("content-length:") {
            content_length = value.trim().parse().unwrap_or_default();
        }
    }
    let mut body = vec![0u8; content_length];
    reader.read_exact(&mut body)?;
    Ok(Some((
        serde_json::from_slice(&body).unwrap_or(Value::Null),
        content_length,
    )))
}

fn serve(shared: &Shared, mut stream: TcpStream) {
    let Ok(Some((body, raw_len))) = read_request(&stream) else {
        return;
    };
    let (index, reply) = shared.update(|state| {
        let index = state.log.len();
        let request = classify(index, body, raw_len);
        let over = state
            .window
            .is_some_and(|window| request.prompt_tokens > window);
        let reply = if over {
            Reply::overflow()
        } else {
            (shared.script)(&request)
        };
        state.log.push(Logged {
            request,
            reply: reply.clone(),
            served: Served::Open,
            holding: false,
        });
        (index, reply)
    });
    let served = respond(shared, index, &reply, &mut stream);
    shared.update(|state| state.log[index].served = served);
}

fn chunk(delta: &Value, finish_reason: Option<&str>, usage: Option<&Value>) -> String {
    let mut chunk = json!({
        "id": "chatcmpl-mock",
        "object": "chat.completion.chunk",
        "created": 1_750_000_000,
        "model": "mock",
        "choices": [{ "index": 0, "delta": delta, "finish_reason": finish_reason }],
    });
    if let Some(usage) = usage {
        chunk["usage"] = usage.clone();
    }
    format!("data: {chunk}\n\n")
}

fn respond(shared: &Shared, index: usize, reply: &Reply, stream: &mut TcpStream) -> Served {
    let prompt_tokens = shared.lock().log[index].request.prompt_tokens;
    let (first, rest, finish) = match &reply.content {
        ReplyContent::Overflow => {
            let body = json!({ "error": {
                "message": "Your input exceeds the context window of this model.",
                "type": "invalid_request_error",
                "code": "context_length_exceeded",
            }})
            .to_string();
            let _ = write!(
                stream,
                "HTTP/1.1 400 Bad Request\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
                body.len()
            );
            return Served::Overflowed;
        }
        ReplyContent::Text(text) => {
            // Split the text so a held stream has a partial message.
            let cut = text
                .char_indices()
                .nth(text.chars().count() / 2)
                .map_or(text.len(), |(at, _)| at);
            (
                chunk(
                    &json!({ "role": "assistant", "content": &text[..cut] }),
                    None,
                    None,
                ),
                chunk(&json!({ "content": &text[cut..] }), None, None),
                "stop",
            )
        }
        ReplyContent::ToolCall {
            id,
            name,
            arguments,
        } => (
            chunk(
                &json!({ "role": "assistant", "content": "Running the tool." }),
                None,
                None,
            ),
            chunk(
                &json!({ "tool_calls": [{
                    "index": 0,
                    "id": id,
                    "type": "function",
                    "function": { "name": name, "arguments": arguments.to_string() },
                }]}),
                None,
                None,
            ),
            "tool_calls",
        ),
    };
    let completion_tokens = 8u64;
    let usage = json!({
        "prompt_tokens": prompt_tokens,
        "completion_tokens": completion_tokens,
        "total_tokens": prompt_tokens + completion_tokens,
        "prompt_tokens_details": { "cached_tokens": 0 },
    });
    let head = "HTTP/1.1 200 OK\r\nContent-Type: text/event-stream\r\nConnection: close\r\n\r\n";
    if stream
        .write_all(format!("{head}{first}").as_bytes())
        .and_then(|()| stream.flush())
        .is_err()
    {
        return Served::Dropped;
    }
    if let Some(gate) = &reply.hold {
        if !wait_gate(shared, index, gate, stream) {
            return Served::Dropped;
        }
    }
    let mut tail = rest;
    tail.push_str(&chunk(&json!({}), Some(finish), Some(&usage)));
    let _ = write!(
        tail,
        "data: {}\n\n",
        json!({
            "id": "chatcmpl-mock",
            "object": "chat.completion.chunk",
            "created": 1_750_000_000,
            "model": "mock",
            "choices": [],
            "usage": usage,
        })
    );
    tail.push_str("data: [DONE]\n\n");
    match stream
        .write_all(tail.as_bytes())
        .and_then(|()| stream.flush())
    {
        Ok(()) => Served::Complete,
        Err(_) => Served::Dropped,
    }
}

/// Hold until `gate` opens (true) or the client hangs up (false).
fn wait_gate(shared: &Shared, index: usize, gate: &str, stream: &TcpStream) -> bool {
    shared.update(|state| state.log[index].holding = true);
    let _ = stream.set_read_timeout(Some(Duration::from_millis(20)));
    let mut probe = [0u8; 1];
    let open = loop {
        if shared.lock().open_gates.contains(gate) {
            break true;
        }
        match stream.peek(&mut probe) {
            Ok(0) => break false,
            // Bytes after the request (none expected): keep holding.
            Ok(_) => std::thread::sleep(Duration::from_millis(20)),
            Err(error)
                if matches!(
                    error.kind(),
                    std::io::ErrorKind::WouldBlock | std::io::ErrorKind::TimedOut
                ) => {}
            Err(_) => break false,
        }
    };
    shared.update(|state| state.log[index].holding = false);
    open
}
