//! eukhe additions of the `anthropic-messages` module: explicit
//! prompt-cache breakpoints and provider stream-failure diagnostics.

mod anthropic_support;

use anthropic_support::{collect, mock_fetch, model, ok_fetch, requests, MockResponse};
use eukhe_pi_ai::api::anthropic_messages::{stream_anthropic, AnthropicOptions};
use eukhe_pi_ai::types::FetchFunction;
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
