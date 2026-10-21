use serde_json::json;

use super::*;

fn event(value: serde_json::Value) -> SessionEvent {
    serde_json::from_value(value).expect("a wire session event")
}

/// A run that ends before any assistant message (no model configured)
/// still answers the phone. Before the fix the gateway stayed silent.
#[test]
fn a_run_without_an_assistant_message_answers() {
    let input = json!({
        "role": "custom", "customType": "signal", "content": "hello",
        "display": true, "timestamp": 1
    });
    let ended = event(json!({ "type": "agent_end", "messages": [input] }));
    assert_eq!(
        answer(&ended),
        Some(Answer::Failed(NO_MODEL_ANSWER.to_string()))
    );
}

/// A turn that faults without an assistant message answers its error.
#[test]
fn a_faulted_turn_answers_its_error() {
    let failed = event(json!({ "type": "turn_end", "error": "worker\ncrashed" }));
    assert_eq!(
        answer(&failed),
        Some(Answer::Failed("worker crashed".to_string()))
    );
}

/// A failed request's assistant message answers with its error; the turn
/// end that follows carries that message, so it adds no second reply.
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
    assert_eq!(
        [answer(&ended), answer(&turn)],
        [
            Some(Answer::Failed(
                "No API key for provider: cloudflare-ai-gateway".to_string()
            )),
            None
        ]
    );
}
