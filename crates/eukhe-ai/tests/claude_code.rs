//! The `claude-code` wire API against a fake `claude`: a shell script that
//! speaks the CLI's stream-json protocol and logs what eukhe sends it.
#![cfg(unix)]

use std::os::unix::fs::PermissionsExt as _;
use std::path::{Path, PathBuf};

use eukhe_ai::api::claude_code::{stream_simple, CLAUDE_BIN_ENV};
use eukhe_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Model, ProviderEnv, StopReason, TextContent, ToolCall,
    TranscriptContext,
};
use serde_json::{json, Value};

fn model() -> Model {
    serde_json::from_value(json!({
        "id": "claude-test",
        "name": "Claude Test",
        "api": "claude-code",
        "provider": "claude-code",
        "baseUrl": "",
        "reasoning": true,
        "input": ["text", "image"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 200_000,
        "maxTokens": 8192,
    }))
    .expect("model")
}

fn usage() -> Value {
    json!({
        "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
    })
}

/// A user asked to read a file, the model called `read`, the tool answered.
fn context() -> TranscriptContext {
    let context: eukhe_types::pi_ai::Context = serde_json::from_value(json!({
        "systemPrompt": "System.",
        "tools": [{
            "name": "read",
            "description": "Read a file",
            "parameters": { "type": "object", "properties": { "path": { "type": "string" } }, "required": ["path"] },
        }],
        "messages": [
            { "role": "user", "content": "read a.txt", "timestamp": 1 },
            {
                "role": "assistant",
                "content": [{ "type": "toolCall", "id": "toolu_1", "name": "read", "arguments": { "path": "a.txt" } }],
                "api": "claude-code",
                "provider": "claude-code",
                "model": "claude-test",
                "usage": usage(),
                "stopReason": "toolUse",
                "timestamp": 2,
            },
            {
                "role": "toolResult",
                "toolCallId": "toolu_1",
                "toolName": "read",
                "content": [{ "type": "text", "text": "hello" }],
                "isError": false,
                "timestamp": 3,
            },
        ],
    }))
    .expect("context");
    eukhe_ai::utils::transcript::normalize_context(context)
}

/// A fake `claude` in `dir`: it logs its arguments and every input line,
/// answers the initialize request, asks for the tool list, reads until the
/// list's answer and the querying frame arrived, then prints `reply`.
fn fake_claude(dir: &Path, reply: &[Value]) -> PathBuf {
    let lines: String = reply
        .iter()
        .flat_map(|line| {
            [
                "printf '%s\\n' '".to_owned(),
                line.to_string(),
                "'\n".to_owned(),
            ]
        })
        .collect();
    let script = format!(
        r#"#!/bin/sh
for arg in "$@"; do printf '[%s]\n' "$arg"; done > '{dir}/args'
IFS= read -r line; printf '%s\n' "$line" >> '{dir}/stdin'
printf '%s\n' '{{"type":"control_response","response":{{"subtype":"success","request_id":"eukhe-init","response":{{}}}}}}'
printf '%s\n' '{{"type":"control_request","request_id":"m1","request":{{"subtype":"mcp_message","server_name":"eukhe","message":{{"jsonrpc":"2.0","id":1,"method":"tools/list"}}}}}}'
listed=0; queried=0
while [ $listed = 0 ] || [ $queried = 0 ]; do
  IFS= read -r line || exit 3
  printf '%s\n' "$line" >> '{dir}/stdin'
  case "$line" in
    *'"mcp_response"'*) listed=1 ;;
    *'"shouldQuery":false'*) ;;
    *'"type":"user"'*) queried=1 ;;
  esac
done
{lines}read -r line
"#,
        dir = dir.display(),
    );
    let path = dir.join("claude");
    std::fs::write(&path, script).expect("write fake claude");
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).expect("chmod");
    path
}

fn options(binary: &Path) -> SimpleStreamOptions {
    let mut options = SimpleStreamOptions::default();
    options.stream.request.env = Some(ProviderEnv::from([(
        CLAUDE_BIN_ENV.to_owned(),
        binary.display().to_string(),
    )]));
    options
}

async fn respond(binary: &Path) -> AssistantMessage {
    stream_simple(&model(), &context(), options(binary))
        .result()
        .await
}

fn logged(path: &Path) -> Vec<Value> {
    std::fs::read_to_string(path)
        .expect("log")
        .lines()
        .map(|line| serde_json::from_str(line).expect("logged JSON"))
        .collect()
}

fn event(event: &Value) -> Value {
    json!({ "type": "stream_event", "event": event })
}

#[tokio::test]
async fn a_tool_call_ends_the_response_and_the_transcript_replays_through_the_cli() {
    let dir = tempfile::tempdir().expect("tempdir");
    let binary = fake_claude(
        dir.path(),
        &[
            json!({ "type": "result", "subtype": "success", "is_error": false, "num_turns": 0, "result": "" }),
            event(
                &json!({ "type": "message_start", "message": { "id": "msg_1", "model": "claude-test", "usage": { "input_tokens": 12, "output_tokens": 0 } } }),
            ),
            event(
                &json!({ "type": "content_block_start", "index": 0, "content_block": { "type": "text", "text": "" } }),
            ),
            event(
                &json!({ "type": "content_block_delta", "index": 0, "delta": { "type": "text_delta", "text": "Reading." } }),
            ),
            event(&json!({ "type": "content_block_stop", "index": 0 })),
            event(
                &json!({ "type": "content_block_start", "index": 1, "content_block": { "type": "tool_use", "id": "toolu_2", "name": "mcp__eukhe__read", "input": {} } }),
            ),
            event(
                &json!({ "type": "content_block_delta", "index": 1, "delta": { "type": "input_json_delta", "partial_json": "{\"path\":\"b.txt\"}" } }),
            ),
            event(&json!({ "type": "content_block_stop", "index": 1 })),
            event(
                &json!({ "type": "message_delta", "delta": { "stop_reason": "tool_use" }, "usage": { "output_tokens": 7 } }),
            ),
            event(&json!({ "type": "message_stop" })),
        ],
    );

    let message = respond(&binary).await;

    assert_eq!(message.error_message, None);
    assert_eq!(message.stop_reason, StopReason::ToolUse);
    let mut arguments = serde_json::Map::new();
    arguments.insert("path".to_owned(), json!("b.txt"));
    assert_eq!(
        message.content,
        vec![
            AssistantContentBlock::Text(TextContent::new("Reading.")),
            AssistantContentBlock::ToolCall(ToolCall {
                id: "toolu_2".to_owned(),
                name: "read".to_owned(),
                arguments,
                ..ToolCall::default()
            }),
        ]
    );
    let args = std::fs::read_to_string(dir.path().join("args")).expect("args");
    assert_eq!(
        args.lines().collect::<Vec<_>>(),
        [
            "[-p]",
            "[--input-format]",
            "[stream-json]",
            "[--output-format]",
            "[stream-json]",
            "[--verbose]",
            "[--include-partial-messages]",
            "[--tools]",
            "[]",
            "[--setting-sources]",
            "[]",
            "[--strict-mcp-config]",
            "[--disable-slash-commands]",
            "[--max-turns]",
            "[1]",
            "[--permission-mode]",
            "[dontAsk]",
            "[--no-session-persistence]",
            "[--model]",
            "[claude-test]",
        ]
    );
    assert_eq!(
        logged(&dir.path().join("stdin")),
        vec![
            json!({ "type": "control_request", "request_id": "eukhe-init", "request": {
                "subtype": "initialize", "sdkMcpServers": ["eukhe"], "systemPrompt": ["System."],
            } }),
            json!({ "type": "user", "parent_tool_use_id": null, "shouldQuery": false,
                "message": { "role": "user", "content": [{ "type": "text", "text": "read a.txt" }] } }),
            json!({ "type": "assistant", "parent_tool_use_id": null, "message": { "role": "assistant", "content": [
                { "type": "tool_use", "id": "toolu_1", "name": "mcp__eukhe__read", "input": { "path": "a.txt" } },
            ] } }),
            json!({ "type": "user", "parent_tool_use_id": null, "message": { "role": "user", "content": [
                { "type": "tool_result", "tool_use_id": "toolu_1", "content": [{ "type": "text", "text": "hello" }], "is_error": false },
            ] } }),
            json!({ "type": "control_response", "response": { "subtype": "success", "request_id": "m1", "response": {
                "mcp_response": { "jsonrpc": "2.0", "id": 1, "result": { "tools": [{
                    "name": "read",
                    "description": "Read a file",
                    "inputSchema": { "type": "object", "properties": { "path": { "type": "string" } }, "required": ["path"] },
                }] } },
            } } }),
        ]
    );
}

#[tokio::test]
async fn a_missing_cli_names_its_install_and_sign_in() {
    let dir = tempfile::tempdir().expect("tempdir");

    let message = respond(&dir.path().join("claude")).await;

    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(
        message.error_message.as_deref(),
        Some(
            "`claude` not found on PATH or at EUKHE_CLAUDE_BIN: install it with \
             `npm install -g @anthropic-ai/claude-code`, then sign in with `claude auth login`"
        )
    );
}

#[tokio::test]
async fn a_signed_out_cli_names_its_sign_in() {
    let dir = tempfile::tempdir().expect("tempdir");
    // What a signed-out `claude` prints for a query.
    let binary = fake_claude(
        dir.path(),
        &[
            json!({ "type": "result", "subtype": "success", "is_error": false, "num_turns": 0, "result": "" }),
            json!({ "type": "assistant", "error": "authentication_failed", "is_api_error_message": true, "message": {
                "id": "m", "model": "<synthetic>", "role": "assistant", "stop_reason": "stop_sequence",
                "content": [{ "type": "text", "text": "Not logged in · Please run /login" }],
            } }),
            json!({ "type": "result", "subtype": "success", "is_error": true, "num_turns": 1, "result": "Not logged in · Please run /login" }),
        ],
    );

    let message = respond(&binary).await;

    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(
        message.error_message.as_deref(),
        Some("`claude` is signed out: run `claude auth login`")
    );
}
