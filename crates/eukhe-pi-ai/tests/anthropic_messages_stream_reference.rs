//! Differential checks of stream folding: final messages the TS reference
//! (`@earendil-works/pi-ai` 1.0.4) produces for fixed SSE bodies.

mod anthropic_support;

use anthropic_support::{collect, mock_fetch, model, sse_of, MockResponse};
use eukhe_pi_ai::api::anthropic_messages::stream;
use eukhe_pi_ai::types::ProviderStreamOptions;
use serde_json::{json, Value};

async fn run(events: &Value) -> Value {
    let model = model(&json!({
        "id": "claude-x", "name": "x", "reasoning": true,
        "cost": {"input": 3, "output": 15, "cacheRead": 0.3, "cacheWrite": 3.75},
        "contextWindow": 100_000, "maxTokens": 1000
    }));
    let context = anthropic_support::context(&json!({
        "messages": [{"role": "user", "content": "hi", "timestamp": 1}],
        "tools": [{"name": "read", "description": "r", "parameters": {"type": "object", "properties": {}}}]
    }));
    let (fetch, _) = mock_fetch(MockResponse::sse(sse_of(
        events.as_array().expect("events"),
    )));
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("sk-test".to_owned());
    options.stream.request.fetch = Some(fetch);
    let (events, message) = collect(stream(&model, &context, options)).await;
    let mut message = serde_json::to_value(message).expect("message");
    let object = message.as_object_mut().expect("object");
    object.remove("timestamp");
    // Response timing (`durationMs`) is clock-dependent, like `timestamp`.
    assert!(object
        .remove("durationMs")
        .is_some_and(|value| value.is_u64()));
    // eukhe addition: the provider_stream_failure diagnostic (absent in TS).
    if let Some(Value::Array(diagnostics)) = object.get_mut("diagnostics") {
        diagnostics.retain(|diagnostic| diagnostic["type"] != "provider_stream_failure");
        for diagnostic in diagnostics.iter_mut() {
            diagnostic
                .as_object_mut()
                .expect("diagnostic")
                .remove("timestamp");
        }
        if diagnostics.is_empty() {
            object.remove("diagnostics");
        }
    }
    let types: Vec<&str> = events
        .iter()
        .map(eukhe_types::pi_ai::AssistantMessageEvent::type_name)
        .collect();
    json!({"types": types, "message": message})
}

#[tokio::test]
async fn tool_use_with_thinking_redaction_and_cache_usage() {
    let actual = run(&json!([{"type": "message_start", "message": {"id": "msg_1", "model": "claude-x", "input_transformations": [{"type": "t", "path": "p", "reason": null}], "usage": {"input_tokens": 100, "output_tokens": 1, "cache_read_input_tokens": 20, "cache_creation_input_tokens": 30, "cache_creation": {"ephemeral_1h_input_tokens": 10}}}}, {"type": "content_block_start", "index": 0, "content_block": {"type": "thinking", "thinking": ""}}, {"type": "content_block_delta", "index": 0, "delta": {"type": "thinking_delta", "thinking": "Let me"}}, {"type": "content_block_delta", "index": 0, "delta": {"type": "signature_delta", "signature": "abc"}}, {"type": "content_block_stop", "index": 0}, {"type": "content_block_start", "index": 1, "content_block": {"type": "redacted_thinking", "data": "opaque"}}, {"type": "content_block_stop", "index": 1}, {"type": "content_block_start", "index": 2, "content_block": {"type": "tool_use", "id": "toolu_1", "name": "read", "input": {}}}, {"type": "content_block_delta", "index": 2, "delta": {"type": "input_json_delta", "partial_json": "{\"pa"}}, {"type": "content_block_delta", "index": 2, "delta": {"type": "input_json_delta", "partial_json": "th\":\"x\"}"}}, {"type": "content_block_stop", "index": 2}, {"type": "message_delta", "delta": {"stop_reason": "tool_use"}, "usage": {"output_tokens": 50, "output_tokens_details": {"thinking_tokens": 20}}}, {"type": "message_stop"}])).await;
    let expected: Value = serde_json::from_str(r#"{"types":["start","thinking_start","thinking_delta","thinking_end","thinking_start","thinking_end","toolcall_start","toolcall_delta","toolcall_delta","toolcall_end","done"],"message":{"role":"assistant","content":[{"type":"thinking","thinking":"Let me","thinkingSignature":"abc"},{"type":"thinking","thinking":"[Reasoning redacted]","thinkingSignature":"opaque","redacted":true},{"type":"toolCall","id":"toolu_1","name":"read","arguments":{"path":"x"}}],"api":"anthropic-messages","provider":"anthropic","model":"claude-x","usage":{"input":100,"output":50,"cacheRead":20,"cacheWrite":30,"totalTokens":200,"cost":{"input":0.00030000000000000003,"output":0.00075,"cacheRead":0.000006,"cacheWrite":0.000135,"total":0.001191},"cacheWrite1h":10,"reasoning":20},"stopReason":"toolUse","responseId":"msg_1","rawStopReason":"tool_use","diagnostics":[{"type":"anthropic_input_transformations","details":{"transformations":[{"type":"t","path":"p"}]}}]}}"#).expect("reference");
    // Value equality: the message's key order is fixed by the `AssistantMessage`
    // struct, while TS orders keys by assignment.
    assert_eq!(actual, expected);
}

#[tokio::test]
async fn refusal_with_explanation() {
    let actual = run(&json!([{"type": "message_start", "message": {"id": "msg_2", "model": "claude-x", "usage": {"input_tokens": 5, "output_tokens": 0}}}, {"type": "content_block_start", "index": 0, "content_block": {"type": "text", "text": ""}}, {"type": "content_block_delta", "index": 0, "delta": {"type": "text_delta", "text": "no"}}, {"type": "message_delta", "delta": {"stop_reason": "refusal", "stop_details": {"explanation": "nope"}}, "usage": {"output_tokens": 3}}, {"type": "message_stop"}])).await;
    let expected: Value = serde_json::from_str(r#"{"types":["start","text_start","text_delta","error"],"message":{"role":"assistant","content":[{"type":"text","text":"no"}],"api":"anthropic-messages","provider":"anthropic","model":"claude-x","usage":{"input":5,"output":3,"cacheRead":0,"cacheWrite":0,"totalTokens":8,"cost":{"input":0.000015,"output":0.000045,"cacheRead":0,"cacheWrite":0,"total":0.00006},"cacheWrite1h":0},"stopReason":"error","responseId":"msg_2","rawStopReason":"refusal","errorMessage":"nope"}}"#).expect("reference");
    // Value equality: the message's key order is fixed by the `AssistantMessage`
    // struct, while TS orders keys by assignment.
    assert_eq!(actual, expected);
}

#[tokio::test]
async fn ended_before_message_stop() {
    let actual = run(&json!([{"type": "message_start", "message": {"id": "msg_3", "model": "claude-z", "usage": {"input_tokens": 5, "output_tokens": 0}}}, {"type": "content_block_start", "index": 0, "content_block": {"type": "text", "text": ""}}, {"type": "content_block_delta", "index": 0, "delta": {"type": "text_delta", "text": "partial"}}])).await;
    let expected: Value = serde_json::from_str(r#"{"types":["start","text_start","text_delta","error"],"message":{"role":"assistant","content":[{"type":"text","text":"partial"}],"api":"anthropic-messages","provider":"anthropic","model":"claude-x","usage":{"input":5,"output":0,"cacheRead":0,"cacheWrite":0,"totalTokens":5,"cost":{"input":0.000015,"output":0,"cacheRead":0,"cacheWrite":0,"total":0.000015},"cacheWrite1h":0},"stopReason":"error","responseId":"msg_3","responseModel":"claude-z","errorMessage":"Anthropic stream ended before message_stop"}}"#).expect("reference");
    // Value equality: the message's key order is fixed by the `AssistantMessage`
    // struct, while TS orders keys by assignment.
    assert_eq!(actual, expected);
}

#[tokio::test]
async fn unknown_stop_reason() {
    let actual = run(&json!([{"type": "message_start", "message": {"id": "msg_4", "usage": {"input_tokens": 5, "output_tokens": 0}}}, {"type": "message_delta", "delta": {"stop_reason": "weird"}, "usage": {"output_tokens": 3}}, {"type": "message_stop"}])).await;
    let expected: Value = serde_json::from_str(r#"{"types":["start","error"],"message":{"role":"assistant","content":[],"api":"anthropic-messages","provider":"anthropic","model":"claude-x","usage":{"input":5,"output":0,"cacheRead":0,"cacheWrite":0,"totalTokens":5,"cost":{"input":0.000015,"output":0,"cacheRead":0,"cacheWrite":0,"total":0.000015},"cacheWrite1h":0},"stopReason":"error","responseId":"msg_4","rawStopReason":"weird","errorMessage":"Unhandled stop reason: weird"}}"#).expect("reference");
    // Value equality: the message's key order is fixed by the `AssistantMessage`
    // struct, while TS orders keys by assignment.
    assert_eq!(actual, expected);
}
