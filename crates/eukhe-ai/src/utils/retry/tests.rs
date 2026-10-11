use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::AbortController;
use eukhe_types::pi_ai::{AssistantContentBlock, TextContent};

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

fn retryable(error_message: &str) -> bool {
    is_retryable_assistant_error(&faux_stop_message(StopReason::Error, Some(error_message)))
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

#[test]
fn caps_agent_retry_delay() {
    let delay = |base_delay_ms, max_agent_delay_ms, attempt| {
        retry_delay_ms(
            RetryDelay {
                base_delay_ms,
                max_agent_delay_ms,
            },
            attempt,
        )
    };
    assert!((delay(2000.0, None, 6) - 60_000.0).abs() < f64::EPSILON);
    assert!((delay(2000.0, Some(5000.0), 5) - 5000.0).abs() < f64::EPSILON);
    assert!(delay(2000.0, Some(0.0), 5).abs() < f64::EPSILON);
}

const DISABLED: RetryPolicy = RetryPolicy {
    enabled: false,
    max_retries: 3,
    base_delay_ms: 0.0,
    max_agent_delay_ms: None,
};
const ENABLED: RetryPolicy = RetryPolicy {
    enabled: true,
    max_retries: 3,
    base_delay_ms: 0.0,
    max_agent_delay_ms: None,
};

/// Records callback invocations in order.
#[derive(Clone, Default)]
struct Recorder {
    events: Arc<Mutex<Vec<String>>>,
}

impl Recorder {
    fn push(&self, event: String) {
        self.events
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(event);
    }

    fn events(&self) -> Vec<String> {
        self.events
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    fn callbacks(&self) -> RetryCallbacks {
        let scheduled = self.clone();
        let started = self.clone();
        let finished = self.clone();
        RetryCallbacks {
            on_retry_scheduled: Some(Arc::new(move |attempt, max, delay, message| {
                scheduled.push(format!("scheduled:{attempt}:{max}:{delay}:{message}"));
                Box::pin(async { Ok(()) })
            })),
            on_retry_attempt_start: Some(Arc::new(move || {
                started.push("attempt-start".to_owned());
                Box::pin(async { Ok(()) })
            })),
            on_retry_finished: Some(Arc::new(move |success, attempt, error| {
                finished.push(format!("finished:{success}:{attempt}:{error:?}"));
                Box::pin(async { Ok(()) })
            })),
        }
    }

    fn count(&self, prefix: &str) -> usize {
        self.events()
            .iter()
            .filter(|event| event.starts_with(prefix))
            .count()
    }
}

/// A `produce` closure that returns `responses[n]` (the last one repeats) and counts calls.
fn producer(
    responses: Vec<AssistantMessage>,
    calls: Arc<AtomicU32>,
    recorder: Option<Recorder>,
) -> impl FnMut() -> std::future::Ready<Result<AssistantMessage, Thrown>> {
    move || {
        let index = calls.fetch_add(1, Ordering::SeqCst) as usize;
        if let Some(recorder) = &recorder {
            recorder.push(format!("produce:{index}"));
        }
        std::future::ready(Ok(responses[index.min(responses.len() - 1)].clone()))
    }
}

fn terminated() -> AssistantMessage {
    faux_stop_message(StopReason::Error, Some("terminated"))
}

#[tokio::test]
async fn returns_a_successful_response_immediately_without_retrying() {
    let calls = Arc::new(AtomicU32::new(0));
    let result = retry_assistant_call(
        producer(vec![faux_text_message("ok")], calls.clone(), None),
        Some(&ENABLED),
        None,
        None,
    )
    .await
    .unwrap();
    assert_eq!(
        result.content,
        vec![AssistantContentBlock::Text(TextContent::new("ok"))]
    );
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

#[tokio::test]
async fn does_not_retry_an_aborted_message() {
    let calls = Arc::new(AtomicU32::new(0));
    let recorder = Recorder::default();
    let result = retry_assistant_call(
        producer(
            vec![faux_stop_message(StopReason::Aborted, None)],
            calls.clone(),
            None,
        ),
        Some(&ENABLED),
        None,
        Some(&recorder.callbacks()),
    )
    .await
    .unwrap();
    assert_eq!(result.stop_reason, StopReason::Aborted);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(recorder.count("scheduled"), 0);
}

#[tokio::test]
async fn does_not_retry_a_non_retryable_error() {
    let calls = Arc::new(AtomicU32::new(0));
    let recorder = Recorder::default();
    let result = retry_assistant_call(
        producer(
            vec![faux_stop_message(
                StopReason::Error,
                Some("insufficient_quota"),
            )],
            calls.clone(),
            None,
        ),
        Some(&ENABLED),
        None,
        Some(&recorder.callbacks()),
    )
    .await
    .unwrap();
    assert_eq!(result.stop_reason, StopReason::Error);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(recorder.events(), Vec::<String>::new());
}

#[tokio::test]
async fn retries_a_transient_error_up_to_max_retries_then_returns_the_final_error() {
    let calls = Arc::new(AtomicU32::new(0));
    let recorder = Recorder::default();
    let result = retry_assistant_call(
        producer(vec![terminated()], calls.clone(), None),
        Some(&ENABLED),
        None,
        Some(&recorder.callbacks()),
    )
    .await
    .unwrap();
    assert_eq!(result.stop_reason, StopReason::Error);
    assert_eq!(calls.load(Ordering::SeqCst), 4);
    assert_eq!(recorder.count("scheduled"), 3);
    assert!(recorder
        .events()
        .contains(&"finished:false:3:Some(\"terminated\")".to_owned()));
}

#[tokio::test]
async fn reports_capped_retry_delays() {
    let policy = RetryPolicy {
        enabled: true,
        max_retries: 4,
        base_delay_ms: 10.0,
        max_agent_delay_ms: Some(15.0),
    };
    let calls = Arc::new(AtomicU32::new(0));
    let recorder = Recorder::default();
    let responses = vec![
        terminated(),
        terminated(),
        terminated(),
        terminated(),
        faux_text_message("recovered"),
    ];
    retry_assistant_call(
        producer(responses, calls, None),
        Some(&policy),
        None,
        Some(&recorder.callbacks()),
    )
    .await
    .unwrap();
    let delays: Vec<String> = recorder
        .events()
        .iter()
        .filter_map(|event| event.strip_prefix("scheduled:"))
        .map(|event| event.split(':').nth(2).unwrap().to_owned())
        .collect();
    assert_eq!(delays, ["10", "15", "15", "15"]);
}

#[tokio::test]
async fn stops_retrying_once_a_call_succeeds() {
    let calls = Arc::new(AtomicU32::new(0));
    let recorder = Recorder::default();
    let responses = vec![terminated(), terminated(), faux_text_message("recovered")];
    let result = retry_assistant_call(
        producer(responses, calls.clone(), None),
        Some(&ENABLED),
        None,
        Some(&recorder.callbacks()),
    )
    .await
    .unwrap();
    assert_eq!(
        result.content,
        vec![AssistantContentBlock::Text(TextContent::new("recovered"))]
    );
    assert_eq!(calls.load(Ordering::SeqCst), 3);
    assert!(recorder
        .events()
        .contains(&"finished:true:2:None".to_owned()));
}

#[tokio::test]
async fn reports_an_aborted_retried_call_as_unsuccessful() {
    let calls = Arc::new(AtomicU32::new(0));
    let recorder = Recorder::default();
    let responses = vec![terminated(), faux_stop_message(StopReason::Aborted, None)];
    let result = retry_assistant_call(
        producer(responses, calls.clone(), None),
        Some(&ENABLED),
        None,
        Some(&recorder.callbacks()),
    )
    .await
    .unwrap();
    assert_eq!(result.stop_reason, StopReason::Aborted);
    assert_eq!(calls.load(Ordering::SeqCst), 2);
    assert!(recorder
        .events()
        .contains(&"finished:false:1:None".to_owned()));
}

#[tokio::test]
async fn does_not_retry_when_policy_is_disabled() {
    let calls = Arc::new(AtomicU32::new(0));
    let recorder = Recorder::default();
    let result = retry_assistant_call(
        producer(vec![terminated()], calls.clone(), None),
        Some(&DISABLED),
        None,
        Some(&recorder.callbacks()),
    )
    .await
    .unwrap();
    assert_eq!(result.stop_reason, StopReason::Error);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(recorder.events(), Vec::<String>::new());
}

#[tokio::test]
async fn emits_on_retry_attempt_start_after_backoff_before_each_retried_call() {
    let calls = Arc::new(AtomicU32::new(0));
    let recorder = Recorder::default();
    let callbacks = RetryCallbacks {
        on_retry_finished: None,
        ..recorder.callbacks()
    };
    let responses = vec![terminated(), terminated(), faux_text_message("recovered")];
    let result = retry_assistant_call(
        producer(responses, calls, Some(recorder.clone())),
        Some(&ENABLED),
        None,
        Some(&callbacks),
    )
    .await
    .unwrap();
    assert_eq!(
        result.content,
        vec![AssistantContentBlock::Text(TextContent::new("recovered"))]
    );
    let events: Vec<String> = recorder
        .events()
        .into_iter()
        .map(|event| match event.strip_prefix("scheduled:") {
            Some(rest) => format!("retry:{}", rest.split(':').next().unwrap()),
            None => event,
        })
        .collect();
    assert_eq!(
        events,
        [
            "produce:0",
            "retry:1",
            "attempt-start",
            "produce:1",
            "retry:2",
            "attempt-start",
            "produce:2"
        ]
    );
}

#[tokio::test]
async fn aborts_backoff_sleep_via_signal_returns_an_aborted_message_and_emits_on_retry_finished_false(
) {
    let controller = AbortController::new();
    let policy = RetryPolicy {
        enabled: true,
        max_retries: 5,
        base_delay_ms: 10_000.0,
        max_agent_delay_ms: None,
    };
    let calls = Arc::new(AtomicU32::new(0));
    let recorder = Recorder::default();
    let callbacks = recorder.callbacks();
    let signal = controller.signal();
    let (scheduled_tx, scheduled_rx) = tokio::sync::oneshot::channel::<()>();
    let scheduled_tx = Arc::new(Mutex::new(Some(scheduled_tx)));
    let callbacks = RetryCallbacks {
        on_retry_scheduled: Some(Arc::new(move |_, _, _, _| {
            if let Some(sender) = scheduled_tx
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .take()
            {
                sender.send(()).unwrap();
            }
            Box::pin(async { Ok(()) })
        })),
        ..callbacks
    };
    let run = retry_assistant_call(
        producer(vec![terminated()], calls.clone(), None),
        Some(&policy),
        Some(&signal),
        Some(&callbacks),
    );
    let abort = async {
        scheduled_rx.await.unwrap();
        controller.abort(None);
    };
    let (result, ()) = tokio::join!(run, abort);
    let result = result.unwrap();
    assert_eq!(result.stop_reason, StopReason::Aborted);
    assert_eq!(result.error_message, None);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert!(recorder
        .events()
        .contains(&"finished:false:1:Some(\"terminated\")".to_owned()));
}
