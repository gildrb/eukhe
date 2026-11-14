//! A conversation that changes model mid-session replays one transcript to
//! each provider: Anthropic Messages turns (signed thinking, `toolu_` tool
//! ids) and Codex Responses turns (encrypted reasoning items, compound
//! `call_…|fc_…` tool ids), each with a tool call and its result. Every
//! request body is checked against the target API's rules: tool-call ids
//! in the target's charset and length, every result paired with a call of
//! the same id, the target's own thinking replayed and no foreign
//! signature or reasoning item, the thinking settings of the target model.

mod anthropic_support;

use anthropic_support::{capturing_on_payload, context, take_payload, CapturedPayload};
use base64::Engine as _;
use eukhe_ai::api::{
    anthropic_messages, openai_codex_responses, openai_completions, openai_responses,
};
use eukhe_ai::providers::all::get_builtin_model;
use eukhe_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{JsonValue, Model, ThinkingLevel, Transport};
use serde_json::json;

const HAIKU_SIGNATURES: [&str; 2] = ["SIG_HAIKU_ONE", "SIG_HAIKU_TWO"];
const CODEX_ENCRYPTED: [&str; 2] = ["ENC_CODEX_ONE", "ENC_CODEX_TWO"];
const HAIKU_CALL: &str = "toolu_01HaikuListFilesAbcdefgh";
/// A Codex Responses tool call: `call_id|item_id`, the item id 52 chars.
const CODEX_CALL: &str =
    "call_Gx7Lq2VbN9pRtY4sKmWzA1cD|fc_0123456789abcdef0123456789abcdef0123456789abcdef";

fn usage() -> JsonValue {
    json!({
        "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
    })
}

fn haiku_turn(content: &JsonValue, stop_reason: &str) -> JsonValue {
    json!({
        "role": "assistant",
        "content": content,
        "api": "anthropic-messages",
        "provider": "anthropic",
        "model": "claude-haiku-5-5",
        "usage": usage(),
        "stopReason": stop_reason,
        "timestamp": 2,
    })
}

fn codex_turn(content: &JsonValue, stop_reason: &str) -> JsonValue {
    json!({
        "role": "assistant",
        "content": content,
        "api": "openai-codex-responses",
        "provider": "openai-codex",
        "model": "gpt-5.5",
        "usage": usage(),
        "stopReason": stop_reason,
        "timestamp": 2,
    })
}

fn tool_result(id: &str) -> JsonValue {
    json!({
        "role": "toolResult",
        "toolCallId": id,
        "toolName": "bash",
        "content": [{ "type": "text", "text": "Cargo.toml\nsrc" }],
        "isError": false,
        "timestamp": 3,
    })
}

fn user(text: &str) -> JsonValue {
    json!({ "role": "user", "content": text, "timestamp": 1 })
}

fn codex_reasoning(id: &str, summary: &str, encrypted: &str) -> String {
    let summary = if summary.is_empty() {
        json!([])
    } else {
        json!([{ "type": "summary_text", "text": summary }])
    };
    json!({ "type": "reasoning", "id": id, "summary": summary, "encrypted_content": encrypted })
        .to_string()
}

/// Haiku lists the files with a tool, Codex lists them again with a tool,
/// and the user asks once more: the next request goes to whichever model
/// the session switched to.
fn switched_transcript() -> JsonValue {
    json!({
        "systemPrompt": "You are concise.",
        "tools": [{
            "name": "bash",
            "description": "Run a command",
            "parameters": {
                "type": "object",
                "properties": { "command": { "type": "string" } },
                "required": ["command"],
            },
        }],
        "messages": [
            user("List the files."),
            haiku_turn(&json!([
                { "type": "thinking", "thinking": "I will run ls.", "thinkingSignature": HAIKU_SIGNATURES[0] },
                { "type": "toolCall", "id": HAIKU_CALL, "name": "bash", "arguments": { "command": "ls" } },
            ]), "toolUse"),
            tool_result(HAIKU_CALL),
            haiku_turn(&json!([
                { "type": "thinking", "thinking": "Two entries.", "thinkingSignature": HAIKU_SIGNATURES[1] },
                { "type": "text", "text": "Cargo.toml and src." },
            ]), "stop"),
            user("List them again."),
            codex_turn(&json!([
                { "type": "thinking", "thinking": "", "thinkingSignature": codex_reasoning("rs_codex_one", "", CODEX_ENCRYPTED[0]) },
                { "type": "toolCall", "id": CODEX_CALL, "name": "bash", "arguments": { "command": "ls" } },
            ]), "toolUse"),
            tool_result(CODEX_CALL),
            codex_turn(&json!([
                { "type": "thinking", "thinking": "Same two entries.", "thinkingSignature": codex_reasoning("rs_codex_two", "Same two entries.", CODEX_ENCRYPTED[1]) },
                { "type": "text", "text": "Cargo.toml and src.", "textSignature": "{\"v\":1,\"id\":\"msg_codex_two\",\"phase\":\"final_answer\"}" },
            ]), "stop"),
            user("Once more."),
        ],
    })
}

fn options(reasoning: Option<ThinkingLevel>) -> (SimpleStreamOptions, CapturedPayload) {
    let (on_payload, captured) = capturing_on_payload();
    let mut options = SimpleStreamOptions::default();
    options.stream.request.on_payload = Some(on_payload);
    options.stream.transport = Some(Transport::Sse);
    options.reasoning = reasoning;
    options.disable_reasoning = reasoning.is_none();
    (options, captured)
}

fn loopback(mut model: Model) -> Model {
    "http://127.0.0.1:9".clone_into(&mut model.base_url);
    model
}

fn builtin(provider: &str, id: &str) -> Model {
    loopback(get_builtin_model(provider, id).expect("builtin model"))
}

/// A Codex sign-in token: the account claim is all the request reads.
fn codex_token() -> String {
    let claims = json!({ "https://api.openai.com/auth": { "chatgpt_account_id": "account" } });
    format!(
        "header.{}.signature",
        base64::engine::general_purpose::STANDARD.encode(claims.to_string())
    )
}

async fn anthropic_payload(model: &Model, reasoning: Option<ThinkingLevel>) -> JsonValue {
    let (mut options, captured) = options(reasoning);
    options.stream.request.api_key = Some("fake-key".into());
    let _ = anthropic_messages::stream_simple(model, &context(&switched_transcript()), &options)
        .result()
        .await;
    take_payload(&captured)
}

async fn codex_payload(model: &Model, reasoning: Option<ThinkingLevel>) -> JsonValue {
    let (mut options, captured) = options(reasoning);
    options.stream.request.api_key = Some(codex_token());
    let _ = openai_codex_responses::stream_simple(model, &context(&switched_transcript()), options)
        .result()
        .await;
    take_payload(&captured)
}

async fn responses_payload(model: &Model, reasoning: Option<ThinkingLevel>) -> JsonValue {
    let (mut options, captured) = options(reasoning);
    options.stream.request.api_key = Some("fake-key".into());
    let _ = openai_responses::stream_simple(model, &context(&switched_transcript()), options)
        .result()
        .await;
    take_payload(&captured)
}

async fn completions_payload(model: &Model, reasoning: Option<ThinkingLevel>) -> JsonValue {
    let (mut options, captured) = options(reasoning);
    options.stream.request.api_key = Some("fake-key".into());
    let _ = openai_completions::stream_simple(model, &context(&switched_transcript()), options)
        .result()
        .await;
    take_payload(&captured)
}

/// `^[a-zA-Z0-9_-]{1,max}$`.
fn is_plain_id(id: &str, max: usize) -> bool {
    !id.is_empty()
        && id.len() <= max
        && id
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
}

fn absent(payload: &JsonValue, needles: &[&str]) {
    let text = payload.to_string();
    for needle in needles {
        assert!(!text.contains(needle), "{needle} leaked into {text}");
    }
}

/// Anthropic Messages: every `tool_result` answers a `tool_use` of the
/// assistant message just before it; ids match `^[a-zA-Z0-9_-]{1,64}$`.
/// Returns the call ids in order.
fn anthropic_tool_ids(payload: &JsonValue) -> Vec<String> {
    let messages = payload["messages"].as_array().expect("messages");
    let mut ids = Vec::new();
    let mut open: Vec<String> = Vec::new();
    for message in messages {
        let blocks = message["content"].as_array().cloned().unwrap_or_default();
        for block in &blocks {
            match block["type"].as_str() {
                Some("tool_use") => {
                    let id = block["id"].as_str().expect("tool_use id").to_owned();
                    assert!(is_plain_id(&id, 64), "invalid Anthropic tool_use id {id}");
                    open.push(id.clone());
                    ids.push(id);
                }
                Some("tool_result") => {
                    let id = block["tool_use_id"].as_str().expect("tool_use_id");
                    assert!(
                        open.iter().any(|call| call == id),
                        "tool_result {id} answers no tool_use"
                    );
                }
                _ => {}
            }
        }
        if message["role"] == "user" {
            open.clear();
        }
    }
    ids
}

/// The thinking blocks the request replays.
fn anthropic_thinking(payload: &JsonValue) -> Vec<JsonValue> {
    payload["messages"]
        .as_array()
        .expect("messages")
        .iter()
        .flat_map(|message| message["content"].as_array().cloned().unwrap_or_default())
        .filter(|block| {
            matches!(
                block["type"].as_str(),
                Some("thinking" | "redacted_thinking")
            )
        })
        .collect()
}

/// Responses input: every `function_call_output` answers an earlier
/// `function_call` of the same `call_id`; call ids and item ids are
/// plain, at most 64 chars, item ids `fc_…`. Returns the call ids.
fn responses_tool_ids(payload: &JsonValue) -> Vec<String> {
    let input = payload["input"].as_array().expect("input");
    let mut calls = Vec::new();
    for item in input {
        match item["type"].as_str() {
            Some("function_call") => {
                let call_id = item["call_id"].as_str().expect("call_id").to_owned();
                assert!(is_plain_id(&call_id, 64), "invalid call_id {call_id}");
                if let Some(id) = item.get("id").and_then(JsonValue::as_str) {
                    assert!(
                        id.starts_with("fc_") && is_plain_id(id, 64),
                        "invalid item id {id}"
                    );
                }
                calls.push(call_id);
            }
            Some("function_call_output") => {
                let call_id = item["call_id"].as_str().expect("call_id");
                assert!(
                    calls.iter().any(|call| call == call_id),
                    "output {call_id} answers no call"
                );
            }
            _ => {}
        }
    }
    calls
}

fn responses_reasoning(payload: &JsonValue) -> Vec<JsonValue> {
    payload["input"]
        .as_array()
        .expect("input")
        .iter()
        .filter(|item| item["type"] == "reasoning")
        .cloned()
        .collect()
}

/// Chat Completions: tool call ids plain and at most 40 chars, every tool
/// message answers a call of the assistant message before it.
fn completions_tool_ids(payload: &JsonValue) -> Vec<String> {
    let messages = payload["messages"].as_array().expect("messages");
    let mut ids = Vec::new();
    let mut open: Vec<String> = Vec::new();
    for message in messages {
        match message["role"].as_str() {
            Some("assistant") => {
                open.clear();
                for call in message["tool_calls"]
                    .as_array()
                    .cloned()
                    .unwrap_or_default()
                {
                    let id = call["id"].as_str().expect("tool call id").to_owned();
                    assert!(is_plain_id(&id, 40), "invalid tool call id {id}");
                    open.push(id.clone());
                    ids.push(id);
                }
            }
            Some("tool") => {
                let id = message["tool_call_id"].as_str().expect("tool_call_id");
                assert!(
                    open.iter().any(|call| call == id),
                    "tool message {id} answers no call"
                );
            }
            _ => open.clear(),
        }
    }
    ids
}

#[tokio::test]
async fn back_on_haiku_the_request_replays_only_haiku_signatures() {
    let payload = anthropic_payload(
        &builtin("anthropic", "claude-haiku-5-5"),
        Some(ThinkingLevel::Low),
    )
    .await;

    assert_eq!(
        anthropic_tool_ids(&payload),
        vec![
            HAIKU_CALL.to_owned(),
            "call_Gx7Lq2VbN9pRtY4sKmWzA1cD_fc_0123456789abcdef0123456789abcde".to_owned()
        ]
    );
    assert_eq!(
        anthropic_thinking(&payload),
        vec![
            json!({ "type": "thinking", "thinking": "I will run ls.", "signature": HAIKU_SIGNATURES[0] }),
            json!({ "type": "thinking", "thinking": "Two entries.", "signature": HAIKU_SIGNATURES[1] }),
        ]
    );
    assert_eq!(payload["output_config"], json!({ "effort": "low" }));
    absent(&payload, &CODEX_ENCRYPTED);
    absent(&payload, &["rs_codex", "msg_codex"]);
}

#[tokio::test]
async fn on_another_anthropic_model_the_request_replays_no_haiku_signature() {
    let payload = anthropic_payload(
        &builtin("anthropic", "claude-sonnet-4-5"),
        Some(ThinkingLevel::Medium),
    )
    .await;

    assert_eq!(anthropic_tool_ids(&payload).len(), 2);
    assert_eq!(anthropic_thinking(&payload), Vec::<JsonValue>::new());
    assert_eq!(
        payload["thinking"],
        json!({ "type": "enabled", "budget_tokens": 8192, "display": "summarized" })
    );
    absent(&payload, &HAIKU_SIGNATURES);
    absent(&payload, &CODEX_ENCRYPTED);
}

#[tokio::test]
async fn back_on_codex_the_request_replays_only_codex_reasoning() {
    let payload = codex_payload(
        &builtin("openai-codex", "gpt-5.5"),
        Some(ThinkingLevel::Low),
    )
    .await;

    assert_eq!(
        responses_tool_ids(&payload),
        vec![
            HAIKU_CALL.to_owned(),
            "call_Gx7Lq2VbN9pRtY4sKmWzA1cD".to_owned()
        ]
    );
    let reasoning = |id, summary, encrypted| {
        serde_json::from_str::<JsonValue>(&codex_reasoning(id, summary, encrypted)).expect("json")
    };
    assert_eq!(
        responses_reasoning(&payload),
        vec![
            reasoning("rs_codex_one", "", CODEX_ENCRYPTED[0]),
            reasoning("rs_codex_two", "Same two entries.", CODEX_ENCRYPTED[1]),
        ]
    );
    assert_eq!(
        payload["reasoning"],
        json!({ "effort": "low", "summary": "auto" })
    );
    absent(&payload, &HAIKU_SIGNATURES);
}

#[tokio::test]
async fn on_openai_responses_the_request_replays_no_foreign_reasoning() {
    let payload =
        responses_payload(&builtin("openai", "gpt-5-mini"), Some(ThinkingLevel::Low)).await;

    assert_eq!(responses_tool_ids(&payload).len(), 2);
    assert_eq!(responses_reasoning(&payload), Vec::<JsonValue>::new());
    absent(&payload, &HAIKU_SIGNATURES);
    absent(&payload, &CODEX_ENCRYPTED);
}

#[tokio::test]
async fn on_chat_completions_the_request_replays_no_foreign_reasoning() {
    let mut model = serde_json::to_value(builtin("openai", "gpt-4o-mini")).expect("model json");
    model["api"] = json!("openai-completions");
    let model: Model = serde_json::from_value(model).expect("model");
    let payload = completions_payload(&model, None).await;

    assert_eq!(completions_tool_ids(&payload).len(), 2);
    absent(&payload, &HAIKU_SIGNATURES);
    absent(&payload, &CODEX_ENCRYPTED);
}
