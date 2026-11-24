//! The same-model stream retry budget (`model.streamRetries`): the
//! decision (decide.rs `after_reply`, `spends_stream`) and the cut
//! classification (eukhe-ai `is_stream_cut`).

use eukhe_ai::utils::retry::{is_retryable_assistant_error, is_stream_cut};
use eukhe_types::pi_ai::{AssistantMessage, StopReason};

use super::super::{decide, GenerationCheckpoint};

use super::*;

/// A failed message whose newest stream failure recorded `details`.
fn failure(error: &str, details: &serde_json::Value) -> AssistantMessage {
    let mut value = serde_json::json!({
        "role": "assistant", "content": [], "api": "openai-completions",
        "provider": "local", "model": "m", "stopReason": "error",
        "errorMessage": error, "timestamp": 0,
        "usage": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0,
                   "totalTokens": 0,
                   "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0,
                             "total": 0 } },
        "diagnostics": [{ "type": "provider_stream_failure", "timestamp": 0,
                          "details": details }],
    });
    if error.is_empty() {
        value.as_object_mut().unwrap().remove("errorMessage");
    }
    serde_json::from_value(value).expect("assistant message")
}

fn counts(attempt: u64, streams: u32) -> decide::Counts {
    decide::Counts {
        attempt,
        notes: 0,
        streams,
        waited: 0,
        compacted: false,
    }
}

fn limits(retries: u32, streams: u32) -> decide::Limits {
    decide::Limits {
        max_rounds: std::num::NonZeroU32::new(250).expect("250 rounds"),
        max_wait: 0,
        max_retries: retries,
        max_stream_retries: streams,
        max_notes: decide::MAX_NOTES,
    }
}

/// A cut inside the budget retries on the stream budget.
#[test]
fn a_cut_below_the_budget_retries() {
    let step = decide::after_reply(
        counts(2, 1),
        decide::Reply::<()>::Error {
            retryable: true,
            noted: false,
        },
        true,
        &limits(3, 5),
    );
    assert!(matches!(step, decide::Step::Retry));
    assert!(decide::spends_stream(
        &decide::Reply::<()>::Error {
            retryable: true,
            noted: false
        },
        true,
        counts(2, 1),
        &limits(3, 5),
    ));
}

/// A cut at the budget's end goes on as without the flag: with the retry
/// budget spent (the attempts grew with the stream retries) the run fails
/// on the model — today's turn-failure path.
#[test]
fn a_cut_past_the_budget_fails_like_today() {
    let step = decide::after_reply(
        counts(6, 5),
        decide::Reply::<()>::Error {
            retryable: true,
            noted: false,
        },
        true,
        &limits(3, 5),
    );
    assert!(matches!(step, decide::Step::Fail(decide::Failure::Model)));
}

/// A budget of `0` decides as without the flag from the first cut: with
/// retries left, the retry of `retry.maxRetries` (today's behavior); with
/// none, one attempt then the failure.
#[test]
fn a_budget_of_zero_is_todays_behavior() {
    let retry = decide::after_reply(
        counts(1, 0),
        decide::Reply::<()>::Error {
            retryable: true,
            noted: false,
        },
        true,
        &limits(3, 0),
    );
    assert!(matches!(retry, decide::Step::Retry));
    assert!(!decide::spends_stream(
        &decide::Reply::<()>::Error {
            retryable: true,
            noted: false
        },
        true,
        counts(1, 0),
        &limits(3, 0),
    ));
    let fail = decide::after_reply(
        counts(1, 0),
        decide::Reply::<()>::Error {
            retryable: true,
            noted: false,
        },
        true,
        &limits(0, 0),
    );
    assert!(matches!(fail, decide::Step::Fail(decide::Failure::Model)));
}

/// A status-classified failure (a 429) never spends the stream budget: it
/// retries on `retry.maxRetries` and leaves the cut counter alone.
#[test]
fn a_status_failure_spends_no_stream_retry() {
    let reply = decide::Reply::<()>::Error {
        retryable: true,
        noted: false,
    };
    let step = decide::after_reply(counts(1, 0), reply, false, &limits(3, 5));
    assert!(matches!(step, decide::Step::Retry));
    assert!(!decide::spends_stream(
        &decide::Reply::<()>::Error {
            retryable: true,
            noted: false
        },
        false,
        counts(1, 0),
        &limits(3, 5),
    ));
}

/// The checkpoint records the spent stream retries and reads them back;
/// a checkpoint from before the counter decodes without it.
#[test]
fn the_retry_checkpoint_carries_the_stream_retries() {
    use eukhe_chord::json::{from_json, to_json};

    use crate::harness::generation::GenerationCheckpoint;

    let retry = GenerationCheckpoint::Retry {
        attempt: 3,
        compacted: None,
        until: 1000.0,
        forced: 0,
        note: None,
        streams: 2,
    };
    let json = to_json(&retry).unwrap().to_string();
    assert!(json.contains("\"streams\":2"), "{json}");
    let read: GenerationCheckpoint =
        from_json(&eukhe_chord::json::JsonValue::parse(&json).unwrap()).expect("checkpoint");
    assert_eq!(read, retry);
    let old: GenerationCheckpoint = from_json(
        &eukhe_chord::json::JsonValue::parse(r#"{"phase":"retry","attempt":2,"until":1000.0}"#)
            .unwrap(),
    )
    .expect("old checkpoint");
    assert_eq!(
        old,
        GenerationCheckpoint::Retry {
            attempt: 2,
            compacted: None,
            until: 1000.0,
            forced: 0,
            note: None,
            streams: 0,
        }
    );
}

/// The cut classification: a stream the provider ended without its
/// terminal marker, and a transport word with no status ("terminated"),
/// are cuts; a status-classified failure, an auth or permission failure,
/// a stall and a repetition cut are not.
#[test]
fn the_stream_cut_classification() {
    let drop = failure("terminated", &serde_json::json!({ "kind": "stream_drop" }));
    assert!(is_stream_cut(&drop));
    assert!(is_retryable_assistant_error(&drop));

    let terminated = failure("terminated", &serde_json::json!({ "kind": "unknown" }));
    assert!(is_stream_cut(&terminated));

    let reset = failure(
        "Connection error.",
        serde_json::json!({ "kind": "unknown", "providerErrorType": "ECONNRESET" }),
    );
    assert!(is_stream_cut(&reset));

    let rate_limited = failure(
        "429 Too many concurrent requests",
        serde_json::json!({ "kind": "rate_limit", "status": 429, "retryAfterMs": 1000 }),
    );
    assert!(!is_stream_cut(&rate_limited));

    let server_error = failure(
        "500 Internal Server Error",
        serde_json::json!({ "kind": "server_error", "status": 500 }),
    );
    assert!(!is_stream_cut(&server_error));

    let auth = failure(
        "invalid api key",
        serde_json::json!({ "kind": "auth", "status": 401 }),
    );
    assert!(!is_stream_cut(&auth));

    let stalled = failure(
        "The provider stream sent no event for 10000 ms",
        serde_json::json!({ "kind": "stream_stalled", "idleTimeoutMs": 10000 }),
    );
    assert!(!is_stream_cut(&stalled));

    let repeated = failure(
        "The model repeated 1 line 64 times",
        serde_json::json!({ "kind": "stream_repeating", "repeated": { "period": 1, "line": "x" } }),
    );
    assert!(!is_stream_cut(&repeated));

    let mut not_an_error = failure("terminated", &serde_json::json!({ "kind": "stream_drop" }));
    not_an_error.stop_reason = StopReason::Stop;
    assert!(!is_stream_cut(&not_an_error));
}
