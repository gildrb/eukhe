//! A loopback provider for the model-switch suites: one port serves
//! Anthropic Messages (`POST /v1/messages`) and `OpenAI` Responses
//! (`POST /v1/responses`) streams. A prompt gets the dialect's reasoning
//! (a signed thinking block, an encrypted reasoning item) and one `bash`
//! tool call; the request that carries the tool's result gets reasoning
//! and a text answer; a request without tools (the title) gets a text
//! answer and stays out of the log. Every logged request body carries its
//! dialect, and the checks below hold a body to its dialect's rules.

#![allow(dead_code)] // each including test binary uses its own subset

use std::fmt::Write as _;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::{Arc, Mutex, PoisonError};

use serde_json::{json, Value};

/// The wire API of one request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dialect {
    AnthropicMessages,
    OpenAiResponses,
}

#[derive(Debug, Clone)]
pub struct Logged {
    pub dialect: Dialect,
    pub body: Value,
}

pub struct ProviderMock {
    log: Arc<Mutex<Vec<Logged>>>,
    port: u16,
}

/// The answer's text of request `index` (one-based).
pub fn answer(index: usize) -> String {
    format!("Answer {index}.")
}

/// The thinking signature of request `index`.
pub fn signature(index: usize) -> String {
    format!("SIG-{index}")
}

/// The encrypted reasoning of request `index`.
pub fn encrypted(index: usize) -> String {
    format!("ENC-{index}")
}

impl ProviderMock {
    pub fn start() -> ProviderMock {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind the mock provider");
        let port = listener.local_addr().expect("mock address").port();
        let log = Arc::new(Mutex::new(Vec::new()));
        let accept = Arc::clone(&log);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(stream) = stream else { continue };
                let log = Arc::clone(&accept);
                std::thread::spawn(move || serve(&log, stream));
            }
        });
        ProviderMock { log, port }
    }

    /// A copy of the request log.
    pub fn log(&self) -> Vec<Logged> {
        self.log
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    /// A `models.json` with one thinking model per dialect:
    /// `mock-anthropic/claude-mock` and `mock-openai/gpt-mock`.
    pub fn models_json(&self) -> Value {
        let model = |id: &str| {
            json!({
                "id": id,
                "name": id,
                "reasoning": true,
                "input": ["text"],
                "contextWindow": 200_000,
                "maxTokens": 16_000,
            })
        };
        json!({
            "providers": {
                "mock-anthropic": {
                    "api": "anthropic-messages",
                    "baseUrl": format!("http://127.0.0.1:{}", self.port),
                    "apiKey": "sk-ant-api-mock",
                    "models": [model("claude-mock")],
                },
                "mock-openai": {
                    "api": "openai-responses",
                    "baseUrl": format!("http://127.0.0.1:{}/v1", self.port),
                    "apiKey": "sk-mock",
                    "models": [model("gpt-mock")],
                },
            }
        })
    }
}

/// The request line's path and the JSON body; `None` for anything that is
/// no POST with a body.
fn read_request(stream: &TcpStream) -> Option<(String, Value)> {
    let mut reader = BufReader::new(stream.try_clone().ok()?);
    let mut request_line = String::new();
    reader.read_line(&mut request_line).ok()?;
    // The path without its query (`/v1/messages?beta=true`).
    let path = request_line
        .strip_prefix("POST ")?
        .split_whitespace()
        .next()?
        .split('?')
        .next()?
        .to_owned();
    let mut content_length = 0usize;
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line).ok()? == 0 {
            return None;
        }
        if line == "\r\n" {
            break;
        }
        if let Some((name, value)) = line.split_once(':') {
            if name.eq_ignore_ascii_case("content-length") {
                content_length = value.trim().parse().unwrap_or_default();
            }
        }
    }
    let mut body = vec![0u8; content_length];
    reader.read_exact(&mut body).ok()?;
    Some((path, serde_json::from_slice(&body).ok()?))
}

fn serve(log: &Mutex<Vec<Logged>>, mut stream: TcpStream) {
    let Some((path, body)) = read_request(&stream) else {
        let _ = stream.write_all(b"HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n");
        return;
    };
    let dialect = if path.ends_with("/messages") {
        Dialect::AnthropicMessages
    } else if path.ends_with("/responses") {
        Dialect::OpenAiResponses
    } else {
        let _ = stream.write_all(b"HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\n\r\n");
        return;
    };
    // A request without tools is a side request (the conversation's title):
    // answered with text, kept out of the log and the request count.
    let side = body["tools"].as_array().is_none_or(Vec::is_empty);
    let index = if side {
        0
    } else {
        let mut log = log.lock().unwrap_or_else(PoisonError::into_inner);
        log.push(Logged {
            dialect,
            body: body.clone(),
        });
        log.len()
    };
    let after_tool = side
        || match dialect {
            Dialect::AnthropicMessages => body["messages"]
                .as_array()
                .and_then(|messages| messages.last())
                .and_then(|last| last["content"].as_array())
                .is_some_and(|blocks| blocks.iter().any(|block| block["type"] == "tool_result")),
            Dialect::OpenAiResponses => body["input"]
                .as_array()
                .and_then(|input| input.last())
                .is_some_and(|last| last["type"] == "function_call_output"),
        };
    let events = match dialect {
        Dialect::AnthropicMessages => anthropic_events(index, after_tool),
        Dialect::OpenAiResponses => responses_events(index, after_tool),
    };
    let head = "HTTP/1.1 200 OK\r\nContent-Type: text/event-stream\r\nConnection: close\r\n\r\n";
    let _ = stream
        .write_all(format!("{head}{events}").as_bytes())
        .and_then(|()| stream.flush());
}

const BASH_INPUT: &str = r#"{"script":"ls","i":"Listing files"}"#;

fn sse(events: &[Value]) -> String {
    events.iter().fold(String::new(), |mut out, event| {
        let _ = write!(
            out,
            "event: {}\ndata: {event}\n\n",
            event["type"].as_str().unwrap_or_default()
        );
        out
    })
}

fn anthropic_events(index: usize, after_tool: bool) -> String {
    let mut events = vec![
        json!({ "type": "message_start", "message": {
            "id": format!("msg_mock{index}"), "type": "message", "role": "assistant",
            "model": "claude-mock", "content": [], "stop_reason": null,
            "usage": { "input_tokens": 10, "output_tokens": 0 },
        }}),
        json!({ "type": "content_block_start", "index": 0,
            "content_block": { "type": "thinking", "thinking": "", "signature": "" } }),
        json!({ "type": "content_block_delta", "index": 0,
            "delta": { "type": "thinking_delta", "thinking": format!("Thinking {index}.") } }),
        json!({ "type": "content_block_delta", "index": 0,
            "delta": { "type": "signature_delta", "signature": signature(index) } }),
        json!({ "type": "content_block_stop", "index": 0 }),
    ];
    let stop_reason = if after_tool {
        events.extend([
            json!({ "type": "content_block_start", "index": 1,
                "content_block": { "type": "text", "text": "" } }),
            json!({ "type": "content_block_delta", "index": 1,
                "delta": { "type": "text_delta", "text": answer(index) } }),
            json!({ "type": "content_block_stop", "index": 1 }),
        ]);
        "end_turn"
    } else {
        events.extend([
            json!({ "type": "content_block_start", "index": 1, "content_block": {
                "type": "tool_use", "id": format!("toolu_mock{index}"), "name": "bash", "input": {},
            }}),
            json!({ "type": "content_block_delta", "index": 1,
                "delta": { "type": "input_json_delta", "partial_json": BASH_INPUT } }),
            json!({ "type": "content_block_stop", "index": 1 }),
        ]);
        "tool_use"
    };
    events.extend([
        json!({ "type": "message_delta", "delta": { "stop_reason": stop_reason },
            "usage": { "output_tokens": 5 } }),
        json!({ "type": "message_stop" }),
    ]);
    sse(&events)
}

fn responses_events(index: usize, after_tool: bool) -> String {
    let reasoning = json!({
        "type": "reasoning", "id": format!("rs_mock{index}"),
        "summary": [{ "type": "summary_text", "text": format!("Thinking {index}.") }],
        "encrypted_content": encrypted(index),
    });
    let item = if after_tool {
        json!({
            "type": "message", "id": format!("msg_mock{index}"), "role": "assistant",
            "status": "completed",
            "content": [{ "type": "output_text", "text": answer(index), "annotations": [] }],
        })
    } else {
        json!({
            "type": "function_call", "id": format!("fc_mock{index}"),
            "call_id": format!("call_mock{index}"), "name": "bash", "arguments": BASH_INPUT,
            "status": "completed",
        })
    };
    sse(&[
        json!({ "type": "response.created",
            "response": { "id": format!("resp_mock{index}"), "status": "in_progress" } }),
        json!({ "type": "response.output_item.done", "output_index": 0, "item": reasoning }),
        json!({ "type": "response.output_item.done", "output_index": 1, "item": item }),
        json!({ "type": "response.completed", "response": {
            "id": format!("resp_mock{index}"), "status": "completed",
            "usage": { "input_tokens": 10, "output_tokens": 5, "total_tokens": 15,
                "input_tokens_details": { "cached_tokens": 0 } },
        }}),
    ])
}

/// `^[a-zA-Z0-9_-]{1,max}$`.
fn is_plain_id(id: &str, max: usize) -> bool {
    !id.is_empty()
        && id.len() <= max
        && id
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
}

/// What a request replays of the conversation, for whole-object checks:
/// the tool call ids in order, the reasoning it replays natively (thinking
/// signatures, encrypted reasoning), and its thinking settings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Replay {
    pub dialect: Dialect,
    pub tool_ids: Vec<String>,
    pub reasoning: Vec<String>,
    pub thinking: Value,
}

fn replayed(dialect: Dialect, tool_ids: &[&str], reasoning: &[String], thinking: &Value) -> Replay {
    Replay {
        dialect,
        tool_ids: tool_ids.iter().map(|id| (*id).to_owned()).collect(),
        reasoning: reasoning.to_vec(),
        thinking: thinking.clone(),
    }
}

/// The six requests of a session at thinking level `low` that runs one
/// prompt on `mock-anthropic/claude-mock`, one on `mock-openai/gpt-mock`,
/// and one back on `mock-anthropic/claude-mock`, each prompt one tool call
/// and its result: each request replays every tool call under an id its
/// API takes, only its own model's reasoning natively, at `low`.
pub fn switched_session_replays() -> Vec<Replay> {
    let anthropic_low = json!({
        "thinking": { "type": "enabled", "budget_tokens": 2048, "display": "summarized" },
        "output_config": null,
    });
    let openai_low = json!({ "reasoning": { "effort": "low", "summary": "auto" } });
    let openai_call = "call_mock3_fc_mock3";
    vec![
        replayed(Dialect::AnthropicMessages, &[], &[], &anthropic_low),
        replayed(
            Dialect::AnthropicMessages,
            &["toolu_mock1"],
            &[signature(1)],
            &anthropic_low,
        ),
        replayed(Dialect::OpenAiResponses, &["toolu_mock1"], &[], &openai_low),
        replayed(
            Dialect::OpenAiResponses,
            &["toolu_mock1", "call_mock3"],
            &[encrypted(3)],
            &openai_low,
        ),
        replayed(
            Dialect::AnthropicMessages,
            &["toolu_mock1", openai_call],
            &[signature(1), signature(2)],
            &anthropic_low,
        ),
        replayed(
            Dialect::AnthropicMessages,
            &["toolu_mock1", openai_call, "toolu_mock5"],
            &[signature(1), signature(2), signature(5)],
            &anthropic_low,
        ),
    ]
}

/// Check `logged` against its dialect's rules and return its [`Replay`].
/// Anthropic Messages: every `tool_result` answers a `tool_use` of the
/// assistant message before it; ids match `^[a-zA-Z0-9_-]{1,64}$`.
/// Responses: every `function_call_output` answers an earlier
/// `function_call`; call ids plain, item ids `fc_…`, both at most 64.
pub fn replay(logged: &Logged) -> Replay {
    match logged.dialect {
        Dialect::AnthropicMessages => anthropic_replay(&logged.body),
        Dialect::OpenAiResponses => responses_replay(&logged.body),
    }
}

fn anthropic_replay(body: &Value) -> Replay {
    let mut tool_ids = Vec::new();
    let mut reasoning = Vec::new();
    let mut open: Vec<String> = Vec::new();
    for message in body["messages"].as_array().expect("messages") {
        for block in message["content"].as_array().cloned().unwrap_or_default() {
            match block["type"].as_str() {
                Some("tool_use") => {
                    let id = block["id"].as_str().expect("tool_use id").to_owned();
                    assert!(is_plain_id(&id, 64), "invalid tool_use id {id}");
                    open.push(id.clone());
                    tool_ids.push(id);
                }
                Some("tool_result") => {
                    let id = block["tool_use_id"].as_str().expect("tool_use_id");
                    assert!(
                        open.iter().any(|call| call == id),
                        "tool_result {id} answers no tool_use"
                    );
                }
                Some("thinking") => {
                    reasoning.push(block["signature"].as_str().unwrap_or_default().to_owned());
                }
                Some("redacted_thinking") => panic!("redacted thinking replayed: {block}"),
                _ => {}
            }
        }
        if message["role"] == "user" {
            open.clear();
        }
    }
    Replay {
        dialect: Dialect::AnthropicMessages,
        tool_ids,
        reasoning,
        thinking: json!({ "thinking": body["thinking"], "output_config": body["output_config"] }),
    }
}

fn responses_replay(body: &Value) -> Replay {
    let mut tool_ids = Vec::new();
    let mut reasoning = Vec::new();
    for item in body["input"].as_array().expect("input") {
        match item["type"].as_str() {
            Some("function_call") => {
                let call_id = item["call_id"].as_str().expect("call_id").to_owned();
                assert!(is_plain_id(&call_id, 64), "invalid call_id {call_id}");
                if let Some(id) = item.get("id").and_then(Value::as_str) {
                    assert!(
                        id.starts_with("fc_") && is_plain_id(id, 64),
                        "invalid item id {id}"
                    );
                }
                tool_ids.push(call_id);
            }
            Some("function_call_output") => {
                let call_id = item["call_id"].as_str().expect("call_id");
                assert!(
                    tool_ids.iter().any(|call| call == call_id),
                    "output {call_id} answers no call"
                );
            }
            Some("reasoning") => {
                reasoning.push(
                    item["encrypted_content"]
                        .as_str()
                        .unwrap_or_default()
                        .to_owned(),
                );
            }
            _ => {}
        }
    }
    Replay {
        dialect: Dialect::OpenAiResponses,
        tool_ids,
        reasoning,
        thinking: json!({ "reasoning": body["reasoning"] }),
    }
}
