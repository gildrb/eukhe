use eukhe_types::pi_ai::AssistantMessageDiagnostic;

use super::*;
use crate::utils::test_support::{faux_stop_message, faux_text_message};

const OPENAI_EXPLICIT_RETRY_MESSAGE: &str = "An error occurred while processing your request. You can retry your request, or contact us through our help center at help.openai.com if the error persists. Please include the request ID req_******** in your message.";
const BEDROCK_EXPLICIT_RETRY_MESSAGE: &str = r#"{"message":"The system encountered an unexpected error during processing. Try your request again."}"#;
const NVIDIA_NIM_RESOURCE_EXHAUSTED_MESSAGE: &str =
    "ResourceExhausted: Worker local total request limit reached (288/48)";
const BUN_FETCH_SOCKET_CLOSED_MESSAGE: &str = "The socket connection was closed unexpectedly. For more information, pass `verbose: true` in the second argument to fetch()";
const OPENAI_RESPONSES_EARLY_EOF_MESSAGE: &str =
    "OpenAI Responses stream ended before a terminal response event";
const WRAPPED_DNS_LOOKUP_ERROR: &str =
    "The pending stream has been canceled (caused by: getaddrinfo ENOTFOUND bedrock-runtime.us-east-1.amazonaws.com)";
const AZURE_PEAK_LOAD_ERROR: &str = "The system is currently experiencing high demand and cannot process your request. Your request exceeds the maximum usage size allowed during peak load. For improved capacity reliability, consider switching to Provisioned Throughput.";
/// Anthropic's 400 for an image over its size limit (audit H2): the byte
/// count `5242880` holds the digits `524`.
const ANTHROPIC_IMAGE_TOO_LARGE: &str = "Provider rejected the request (invalid_request_error, 400): messages.0.content.1.image.source.base64: image exceeds 5 MB maximum: 7340032 bytes > 5242880 bytes";

fn retryable(error_message: &str) -> bool {
    is_retryable_assistant_error(&faux_stop_message(StopReason::Error, Some(error_message)))
}

/// A failed message whose newest stream failure recorded `details`.
fn failure(error_message: &str, details: &serde_json::Value) -> AssistantMessage {
    let mut message = faux_stop_message(StopReason::Error, Some(error_message));
    message.diagnostics = Some(vec![AssistantMessageDiagnostic {
        kind: "provider_stream_failure".to_owned(),
        timestamp: 0,
        error: None,
        details: details.as_object().cloned(),
    }]);
    message
}

#[test]
fn matches_explicit_provider_retry_guidance() {
    assert!(retryable(OPENAI_EXPLICIT_RETRY_MESSAGE));
    assert!(retryable(BEDROCK_EXPLICIT_RETRY_MESSAGE));
    assert!(retryable(NVIDIA_NIM_RESOURCE_EXHAUSTED_MESSAGE));
}

#[test]
fn matches_bun_fetch_socket_drop_wording() {
    assert!(retryable(BUN_FETCH_SOCKET_CLOSED_MESSAGE));
}

#[test]
fn matches_upstream_request_buffer_exhaustion_wording() {
    assert!(retryable(
        "Error: exceeded request buffer limit while retrying upstream"
    ));
}

#[test]
fn matches_dns_transport_failure_wording() {
    for error_message in [
        WRAPPED_DNS_LOOKUP_ERROR,
        "connect ENOTFOUND api.example.com",
        "EAI_AGAIN api.example.com",
        "getaddrinfo failed for api.example.com",
    ] {
        assert!(retryable(error_message), "{error_message}");
    }
}

#[test]
fn matches_http2_pending_stream_cancellation() {
    for error_message in [
        "The pending stream has been canceled",
        "The pending stream has been canceled (caused by: socket closed)",
    ] {
        assert!(retryable(error_message), "{error_message}");
    }
}

#[test]
fn a_full_admission_queue_is_never_retried() {
    // The queue limit in the text must not read as a 5xx status.
    assert!(!retryable(
        "provider admission queue is full for p: 500 requests already wait (providerMaxQueued)"
    ));
}

/// Regression (audit H2): a status code inside a longer number is no
/// status, and a recorded 400 is never retried, whatever its text says.
#[test]
fn a_client_error_is_never_retried_by_its_text() {
    let recorded = failure(
        ANTHROPIC_IMAGE_TOO_LARGE,
        &serde_json::json!({ "kind": "invalid_request", "status": 400 }),
    );
    let timeout_400 = failure(
        "invalid timeout parameter: 524 is out of range",
        &serde_json::json!({ "kind": "unknown", "status": 400 }),
    );
    assert_eq!(
        [
            retryable(ANTHROPIC_IMAGE_TOO_LARGE),
            is_retryable_assistant_error(&recorded),
            is_retryable_assistant_error(&timeout_400),
        ],
        [false, false, false]
    );
}

/// The recorded status decides before the text, and the typed kind
/// before the text when no status was recorded.
#[test]
fn the_status_then_the_kind_decide() {
    let cases = [
        failure("bad request", &serde_json::json!({ "status": 503 })),
        failure("terminated", &serde_json::json!({ "status": 404 })),
        failure("bad gateway", &serde_json::json!({ "status": 408 })),
        failure("anything", &serde_json::json!({ "kind": "overloaded" })),
        failure("terminated", &serde_json::json!({ "kind": "auth" })),
        failure("terminated", &serde_json::json!({ "kind": "unknown" })),
    ];
    let verdicts: Vec<bool> = cases.iter().map(is_retryable_assistant_error).collect();
    assert_eq!(verdicts, [true, false, true, true, false, true]);
}

/// Regression (audit H4): a failure the quota park ended is never
/// retried, whatever its status and text.
#[test]
fn a_parked_failure_is_never_retried() {
    let mut parked = failure(
        "Session parked until 2026-10-20T00:00:00.000Z and will resume automatically: 429 Too Many Requests",
        &serde_json::json!({ "kind": "rate_limit", "status": 429, "retryAfterMs": 3_600_000 }),
    );
    if let Some(diagnostics) = parked.diagnostics.as_mut() {
        diagnostics.push(AssistantMessageDiagnostic {
            kind: QUOTA_PARK_DIAGNOSTIC.to_owned(),
            timestamp: 0,
            error: None,
            details: None,
        });
    }
    assert_eq!(
        FailureFacts::of(&parked),
        Some(FailureFacts {
            parked: true,
            limit: false,
            status: Some(429),
            kind: Some(StreamFailureKind::RateLimit),
            transient_text: true,
        })
    );
    assert!(!is_retryable_assistant_error(&parked));
}

/// The HTTP layer's refusal of a long server wait is never retried
/// (audit H5).
#[test]
fn a_refused_server_wait_is_never_retried() {
    assert!(!retryable(&RetryWait::refusal(
        300_000.0,
        60_000.0,
        "429 Too Many Requests"
    )));
}

/// Regression (audit H5): a server wait above the cap refuses the retry
/// with the server's time; a wait under it is never cut short.
#[test]
fn the_retry_wait_never_goes_before_the_server() {
    let policy = RetryDelay {
        base_delay_ms: 100.0,
        max_agent_delay_ms: Some(4_000.0),
    };
    let wait = |retry_after_ms: u64| {
        retry_wait(
            policy,
            1,
            &failure(
                "429 Too Many Requests",
                &serde_json::json!({ "kind": "rate_limit", "retryAfterMs": retry_after_ms }),
            ),
        )
    };
    assert_eq!(
        [wait(1_500), wait(60_000)],
        [
            RetryWait::After(1_500.0),
            RetryWait::Refused {
                server_ms: 60_000.0,
                cap_ms: 4_000.0,
            },
        ]
    );
    assert_eq!(
        RetryWait::refusal(60_000.0, 4_000.0, "429 Too Many Requests"),
        "Server requested 60s retry delay (max: 4s). 429 Too Many Requests"
    );
}

#[test]
fn a_zero_cap_never_refuses_a_server_wait() {
    assert_eq!(
        RetryWait::of(10.0, Some(300_000.0), 0.0),
        RetryWait::After(300_000.0)
    );
}

#[test]
fn the_retry_wait_is_a_full_jitter_draw_under_the_step() {
    let policy = RetryDelay {
        base_delay_ms: 1_000.0,
        max_agent_delay_ms: None,
    };
    let message = faux_stop_message(StopReason::Error, Some("503 Service Unavailable"));
    let waits: Vec<f64> = (0..200)
        .map(|_| match retry_wait(policy, 3, &message) {
            RetryWait::After(ms) => ms,
            RetryWait::Refused { server_ms, .. } => -server_ms,
        })
        .collect();
    // Attempt 3's step is 4 s: every draw lands in [0, 4 s], and the
    // draws spread (a fixed ladder would repeat one value).
    assert!(
        waits.iter().all(|wait| (0.0..=4_000.0).contains(wait)),
        "{waits:?}"
    );
    assert!(
        waits.iter().any(|wait| wait.total_cmp(&waits[0]).is_ne()),
        "{waits:?}"
    );
}

#[test]
fn the_step_is_capped() {
    let policy = RetryDelay {
        base_delay_ms: 2_000.0,
        max_agent_delay_ms: Some(0.0),
    };
    let message = faux_stop_message(StopReason::Error, Some("503 Service Unavailable"));
    assert_eq!(retry_wait(policy, 5, &message), RetryWait::After(0.0));
}

#[test]
fn reads_the_idle_deadline_of_a_stall() {
    let stalled = failure(
        "stalled",
        &serde_json::json!({ "kind": "stream_stalled", "idleTimeoutMs": 300_000 }),
    );
    let dropped = failure(
        "dropped",
        &serde_json::json!({ "kind": "stream_drop", "idleTimeoutMs": 300_000 }),
    );
    assert_eq!(
        [stalled_idle_ms(&stalled), stalled_idle_ms(&dropped)],
        [Some(300_000), None]
    );
}

#[test]
fn matches_openai_responses_streams_that_end_before_terminal_events() {
    assert!(retryable(OPENAI_RESPONSES_EARLY_EOF_MESSAGE));
}

#[test]
fn matches_azure_peak_load_capacity_errors() {
    assert!(retryable(AZURE_PEAK_LOAD_ERROR));
}

#[test]
fn keeps_provider_limit_errors_non_retryable() {
    assert!(!retryable("429 quota exceeded"));
}

#[test]
fn keeps_the_chatgpt_subscription_usage_limit_non_retryable() {
    assert!(!retryable(
        r#"OpenAI API error (429): {"code":"subscription_sharing_usage_limit_exceeded","message":"Usage limit reached."}"#
    ));
}

#[test]
fn retries_temporary_chatgpt_subscription_errors() {
    for error_message in [
        "subscription_sharing_usage_unavailable: Usage cannot be checked.",
        "subscription_sharing_user_unavailable: User cannot be loaded.",
    ] {
        assert!(retryable(error_message), "{error_message}");
    }
}

#[test]
fn classifies_assistant_error_messages() {
    assert!(retryable("overloaded_error"));
    assert!(retryable("520 status code (no body)"));
    assert!(retryable("524 status code (no body)"));
    assert!(!is_retryable_assistant_error(&faux_text_message(
        "not an error"
    )));
}
