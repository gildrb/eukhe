use eukhe_types::daemon::SessionEvent;
use serde_json::{json, Value};

use super::*;
use crate::answer::answer;

fn assistant(stop: &str, text: &str, error: Option<&str>) -> Value {
    json!({
        "role": "assistant",
        "content": [{ "type": "text", "text": text }],
        "api": "anthropic-messages",
        "provider": "anthropic",
        "model": "claude-opus-5-5",
        "usage": {
            "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 }
        },
        "stopReason": stop,
        "errorMessage": error,
        "timestamp": 1_792_615_710_454_u64
    })
}

fn event(value: Value) -> SessionEvent {
    serde_json::from_value(value).expect("a wire session event")
}

/// A run that starts a job, ends while the job runs, and finishes after
/// the job's wake (a failed request retried on the way) sends the phone
/// one message: the last text, with what the run last found left. The events
/// go from their wire JSON through both entries of the compiled core
/// (`laws/gateway_answer.bend`, `laws/gateway_report.bend`).
#[test]
fn a_run_sends_one_report_at_its_end() {
    let started = assistant("stop", "Started the build.", None);
    let failed = assistant("error", "", Some("overloaded"));
    let built = assistant("stop", "Built and pushed.", None);
    let events = [
        (
            event(json!({ "type": "message_end", "message": started })),
            End::No,
        ),
        (
            event(json!({ "type": "agent_end", "messages": [started] })),
            End::Run {
                work: Work::Running,
                left: None,
            },
        ),
        (
            event(json!({ "type": "message_end", "message": failed })),
            End::No,
        ),
        (
            event(json!({ "type": "message_end", "message": built })),
            End::No,
        ),
        (
            event(json!({ "type": "agent_end", "messages": [failed, built] })),
            End::Run {
                work: Work::Settled,
                left: Some(" the\n release  notes ".to_string()),
            },
        ),
    ];
    let mut held = None;
    let mut sent = Vec::new();
    for (event, end) in &events {
        let step = step(held.as_ref(), answer(event).as_ref(), end);
        held = step.held;
        sent.extend(step.send);
    }
    assert_eq!(
        (held, sent),
        (
            None,
            vec![Answer::Text(
                "Built and pushed.\n\nLeft: the release notes".to_string()
            )]
        )
    );
}
