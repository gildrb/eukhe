//! eukhe additions of the `anthropic-messages` module: explicit
//! prompt-cache breakpoints and provider stream-failure diagnostics.

mod anthropic_support;

use anthropic_support::{collect, mock_fetch, model, ok_fetch, requests, MockResponse};
use eukhe_ai::api::anthropic_messages::{stream_anthropic, AnthropicOptions};
use eukhe_ai::types::FetchFunction;
use eukhe_types::pi_ai::StopReason;
use serde_json::{json, Value};

fn options(fetch: FetchFunction) -> AnthropicOptions {
    let mut options = AnthropicOptions::default();
    options.stream.request.api_key = Some("sk-test".into());
    options.stream.request.fetch = Some(fetch);
    options
}

fn marked(text: &str) -> Value {
    json!({ "type": "text", "text": text, "cacheBreakpoint": "ephemeral" })
}

fn tools() -> Value {
    json!([{ "name": "read", "description": "Read", "parameters": { "type": "object", "properties": {} } }])
}

#[tokio::test]
async fn marked_user_blocks_carry_cache_control_and_optional_marks_fill_the_rest() {
    let (fetch, captured) = ok_fetch();
    let context = anthropic_support::context(&json!({
        "systemPrompt": "System.",
        "tools": tools(),
        "messages": [
            { "role": "user", "content": [marked("stable"), { "type": "text", "text": "tail" }], "timestamp": 1 }
        ]
    }));
    let (_, result) = collect(stream_anthropic(
        &model(&json!({})),
        &context,
        options(fetch),
    ))
    .await;
    assert_eq!(result.stop_reason, StopReason::Stop);
    let body = requests(&captured).pop().expect("request").body;
    assert_eq!(
        body["messages"],
        json!([{ "role": "user", "content": [
            { "type": "text", "text": "stable", "cache_control": { "type": "ephemeral" } },
            { "type": "text", "text": "tail", "cache_control": { "type": "ephemeral" } }
        ] }])
    );
    // Two message marks leave two slots: system first, then the last tool.
    assert_eq!(
        body["system"][0]["cache_control"],
        json!({ "type": "ephemeral" })
    );
    assert_eq!(
        body["tools"][0]["cache_control"],
        json!({ "type": "ephemeral" })
    );
}

#[tokio::test]
async fn full_mark_budget_drops_the_optional_marks() {
    let (fetch, captured) = ok_fetch();
    let context = anthropic_support::context(&json!({
        "systemPrompt": "System.",
        "tools": tools(),
        "messages": [
            { "role": "user", "content": [marked("a"), marked("b"), marked("c"), { "type": "text", "text": "tail" }], "timestamp": 1 }
        ]
    }));
    let (_, result) = collect(stream_anthropic(
        &model(&json!({})),
        &context,
        options(fetch),
    ))
    .await;
    assert_eq!(result.stop_reason, StopReason::Stop);
    let body = requests(&captured).pop().expect("request").body;
    assert!(body["system"][0].get("cache_control").is_none());
    assert!(body["tools"][0].get("cache_control").is_none());
}

#[tokio::test]
async fn a_marked_assistant_text_block_carries_cache_control() {
    let (fetch, captured) = ok_fetch();
    let context = anthropic_support::context(&json!({
        "messages": [
            { "role": "user", "content": "question", "timestamp": 1 },
            {
                "role": "assistant",
                "content": [{ "type": "text", "text": "draft" }, marked("answer")],
                "api": "anthropic-messages",
                "provider": "anthropic",
                "model": "claude-test",
                "usage": {
                    "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                    "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                },
                "stopReason": "stop",
                "timestamp": 2,
            },
            { "role": "user", "content": "review", "timestamp": 3 }
        ]
    }));
    let (_, result) = collect(stream_anthropic(
        &model(&json!({})),
        &context,
        options(fetch),
    ))
    .await;
    assert_eq!(result.stop_reason, StopReason::Stop);
    let body = requests(&captured).pop().expect("request").body;
    assert_eq!(
        body["messages"],
        json!([
            { "role": "user", "content": "question" },
            { "role": "assistant", "content": [
                { "type": "text", "text": "draft" },
                { "type": "text", "text": "answer", "cache_control": { "type": "ephemeral" } }
            ] },
            { "role": "user", "content": [
                { "type": "text", "text": "review", "cache_control": { "type": "ephemeral" } }
            ] }
        ])
    );
}

/// A transcript whose leading system message has a shared `core` section
/// and a per-session `cwd` section, then `messages`.
fn sectioned(messages: Value) -> eukhe_types::pi_ai::TranscriptContext {
    let mut all = vec![json!({
        "role": "system",
        "content": "",
        "sections": { "core": "Core.", "cwd": "Working directory: /a" },
        "toolsAdded": tools(),
        "timestamp": 0,
    })];
    let Value::Array(messages) = messages else {
        panic!("messages are an array");
    };
    all.extend(messages);
    anthropic_support::context(&json!({ "messages": all }))
}

#[tokio::test]
async fn a_cache_breakpoint_sends_the_shared_prefix_as_its_own_marked_block() {
    for (key, system) in [
        (
            "sk-test",
            json!([
                { "type": "text", "text": "Core.", "cache_control": { "type": "ephemeral" } },
                { "type": "text", "text": "Working directory: /a", "cache_control": { "type": "ephemeral" } },
            ]),
        ),
        (
            // OAuth: billing and identity lead, neither marked.
            "sk-ant-oat-x",
            json!([
                { "type": "text", "text": "x-anthropic-billing-header: cc_version=2.1.280.d7b; cc_entrypoint=cli; cch=00000;" },
                { "type": "text", "text": "You are Claude Code, Anthropic's official CLI for Claude." },
                { "type": "text", "text": "Core.", "cache_control": { "type": "ephemeral" } },
                { "type": "text", "text": "Working directory: /a", "cache_control": { "type": "ephemeral" } },
            ]),
        ),
    ] {
        let (fetch, captured) = ok_fetch();
        let mut options = options(fetch);
        options.stream.request.api_key = Some(key.into());
        options.stream.system_cache_breakpoint = Some("core".into());
        let context = sectioned(json!([{ "role": "user", "content": "hi", "timestamp": 1 }]));
        let (_, result) = collect(stream_anthropic(&model(&json!({})), &context, options)).await;
        assert_eq!(result.stop_reason, StopReason::Stop);
        let mut body = requests(&captured).pop().expect("request").body;
        // The attestation hashes the whole body; it is not under test here.
        if let Some(text) = body["system"][0]["text"].as_str() {
            if let Some((head, _)) = text.split_once("cch=") {
                body["system"][0]["text"] = json!(format!("{head}cch=00000;"));
            }
        }
        assert_eq!(body["system"], system, "{key}");
        // The end mark, the prefix, the tool, the tail: all four slots.
        assert_eq!(
            body["tools"][0]["cache_control"],
            json!({ "type": "ephemeral" })
        );
    }
}

#[tokio::test]
async fn the_shared_prefix_mark_outranks_the_tool_and_tail_marks() {
    let (fetch, captured) = ok_fetch();
    let mut options = options(fetch);
    options.stream.system_cache_breakpoint = Some("core".into());
    // Two marked blocks and the end mark leave one slot: the prefix's.
    let context = sectioned(json!([{
        "role": "user",
        "content": [marked("a"), marked("b"), { "type": "text", "text": "tail" }],
        "timestamp": 1,
    }]));
    let (_, result) = collect(stream_anthropic(&model(&json!({})), &context, options)).await;
    assert_eq!(result.stop_reason, StopReason::Stop);
    let body = requests(&captured).pop().expect("request").body;
    assert_eq!(
        body["system"],
        json!([
            { "type": "text", "text": "Core.", "cache_control": { "type": "ephemeral" } },
            { "type": "text", "text": "Working directory: /a" },
        ])
    );
    assert!(body["tools"][0].get("cache_control").is_none());
}

#[tokio::test]
async fn too_many_marked_blocks_fail_before_sending() {
    let (fetch, captured) = ok_fetch();
    let context = anthropic_support::context(&json!({
        "messages": [
            { "role": "user", "content": [marked("a"), marked("b"), marked("c"), marked("d")], "timestamp": 1 }
        ]
    }));
    let (_, result) = collect(stream_anthropic(
        &model(&json!({})),
        &context,
        options(fetch),
    ))
    .await;
    assert_eq!(result.stop_reason, StopReason::Error);
    assert_eq!(
        result.error_message.as_deref(),
        Some("Too many cache breakpoints: the request marks 4 blocks, at most 3 are allowed")
    );
    assert!(requests(&captured).is_empty());
}

#[tokio::test]
async fn http_failures_record_a_provider_stream_failure_diagnostic() {
    let (fetch, _) = mock_fetch(
        MockResponse::json(
            529,
            r#"{"type":"error","error":{"type":"overloaded_error","message":"Overloaded"}}"#,
        )
        .with_header("request-id", "req_1"),
    );
    let context = anthropic_support::context(&json!({
        "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }]
    }));
    let (_, result) = collect(stream_anthropic(
        &model(&json!({})),
        &context,
        options(fetch),
    ))
    .await;
    assert_eq!(result.stop_reason, StopReason::Error);
    // v1.0.4 message: the SDK `APIError` text.
    assert_eq!(
        result.error_message.as_deref(),
        Some(r#"529 {"type":"error","error":{"type":"overloaded_error","message":"Overloaded"}}"#)
    );
    let diagnostics = result.diagnostics.expect("diagnostics");
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].kind, "provider_stream_failure");
    let details = diagnostics[0].details.clone().expect("details");
    assert_eq!(details["kind"], json!("overloaded"));
    assert_eq!(details["status"], json!(529));
}

#[tokio::test]
async fn in_stream_error_events_are_classified() {
    let body = "event: message_start\ndata: {\"type\":\"message_start\",\"message\":{\"id\":\"m\",\"usage\":{\"input_tokens\":1}}}\n\nevent: error\ndata: {\"type\":\"error\",\"error\":{\"type\":\"overloaded_error\",\"message\":\"Overloaded\"}}\n\n";
    let (fetch, _) = mock_fetch(MockResponse::sse(body));
    let context = anthropic_support::context(&json!({
        "messages": [{ "role": "user", "content": "hi", "timestamp": 1 }]
    }));
    let (_, result) = collect(stream_anthropic(
        &model(&json!({})),
        &context,
        options(fetch),
    ))
    .await;
    assert_eq!(
        result.error_message.as_deref(),
        Some(r#"{"type":"error","error":{"type":"overloaded_error","message":"Overloaded"}}"#)
    );
    let details = result.diagnostics.expect("diagnostics")[0]
        .details
        .clone()
        .expect("details");
    assert_eq!(details["kind"], json!("overloaded"));
    assert_eq!(details["providerErrorType"], json!("overloaded_error"));
}
