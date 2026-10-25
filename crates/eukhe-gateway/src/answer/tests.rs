use serde_json::json;

use super::*;

fn event(value: serde_json::Value) -> SessionEvent {
    serde_json::from_value(value).expect("a wire session event")
}

/// A failed request's assistant message answers with its error; the turn
/// end that follows carries that message, so it adds no second reply. The
/// events go from their wire JSON through the compiled core
/// (`laws/gateway_answer.bend` pins every answer).
#[test]
fn a_failed_request_answers_once() {
    let message = json!({
        "role": "assistant",
        "content": [],
        "api": "anthropic-messages",
        "provider": "cloudflare-ai-gateway",
        "model": "claude-opus-5-5",
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 }
        },
        "stopReason": "error",
        "errorMessage": "No API key for provider: cloudflare-ai-gateway",
        "timestamp": 1_792_615_710_454_u64
    });
    let ended = event(json!({ "type": "message_end", "message": message }));
    let turn = event(json!({ "type": "turn_end", "message": message, "toolResults": [] }));
    let faulted = event(json!({ "type": "turn_end", "error": "worker\ncrashed" }));
    assert_eq!(
        [answer(&ended), answer(&turn), answer(&faulted)],
        [
            Some(Answer::Failed(
                "No API key for provider: cloudflare-ai-gateway".to_string()
            )),
            None,
            Some(Answer::Failed("worker crashed".to_string())),
        ]
    );
}
