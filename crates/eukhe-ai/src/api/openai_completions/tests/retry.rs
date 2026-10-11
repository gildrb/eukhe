//! Port of `openai-completions-retry.test.ts`.
//!
//! The TS fake SDK records the per-request options (`maxRetries: 0`) and
//! throws queued errors from `withResponse()`. Here the mock `fetch` answers
//! queued error responses before the success stream, and the SDK layer has
//! no retry loop of its own: "SDK retries disabled" is observed as the number
//! of HTTP requests. Fake timers become tokio paused time; the request
//! instants replace the `advanceTimersByTimeAsync` checkpoints.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use serde_json::json;

use super::support::{collect, context, model, options_with_fetch, sse_body};
use crate::api::openai_completions::{stream_with_options, OpenAICompletionsOptions};
use crate::api::system_one_shared::test_fetch::{mock_fetch, recorded, response, Requests};
use crate::types::{AssistantMessage, FetchFunction, Model, StopReason, TranscriptContext};

fn retry_model() -> Model {
    model(json!({
        "id": "test-model",
        "name": "Test Model",
        "api": "openai-completions",
        "provider": "opencode-go",
        "baseUrl": "https://opencode.ai/zen/go/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 1000,
        "maxTokens": 100,
    }))
}

fn retry_context() -> TranscriptContext {
    context(json!({
        "systemPrompt": "",
        "messages": [{ "role": "user", "content": [{ "type": "text", "text": "hi" }], "timestamp": 0 }],
        "tools": [],
    }))
}

/// One queued error response: status, headers, and message.
struct QueuedError {
    status: u16,
    headers: &'static [(&'static str, &'static str)],
    message: &'static str,
}

/// A `fetch` answering the queued errors in order, then the TS success
/// stream (`"ok"` then `finish_reason: "stop"`); records the tokio instant of
/// every request.
fn queued_fetch(
    errors: Vec<QueuedError>,
) -> (
    FetchFunction,
    Requests,
    Arc<Mutex<Vec<tokio::time::Instant>>>,
) {
    let instants: Arc<Mutex<Vec<tokio::time::Instant>>> = Arc::default();
    let sink = Arc::clone(&instants);
    let calls = AtomicUsize::new(0);
    let success = sse_body(&[
        json!({ "id": "chatcmpl-test", "choices": [{ "index": 0, "delta": { "content": "ok" } }] }),
        json!({ "id": "chatcmpl-test", "choices": [{ "index": 0, "delta": {}, "finish_reason": "stop" }] }),
    ]);
    let (fetch, requests) = mock_fetch(move |_| {
        sink.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(tokio::time::Instant::now());
        let call = calls.fetch_add(1, Ordering::SeqCst);
        match errors.get(call) {
            Some(error) => {
                let mut headers = vec![("content-type", "application/json")];
                headers.extend_from_slice(error.headers);
                response(
                    error.status,
                    &headers,
                    json!({ "error": { "message": error.message } }).to_string(),
                )
            }
            None => response(
                200,
                &[("content-type", "text/event-stream")],
                success.clone(),
            ),
        }
    });
    (fetch, requests, instants)
}

async fn consume(
    fetch: FetchFunction,
    max_retries: Option<u32>,
    max_retry_delay_ms: Option<f64>,
) -> AssistantMessage {
    let mut options: OpenAICompletionsOptions = options_with_fetch(fetch);
    options.stream.request.max_retries = max_retries;
    options.stream.request.max_retry_delay_ms = max_retry_delay_ms;
    let (_, message) = collect(stream_with_options(
        &retry_model(),
        &retry_context(),
        options,
    ))
    .await;
    message
}

#[tokio::test]
async fn disables_sdk_retries_by_default() {
    // A retryable 500 with no `max_retries`: exactly one HTTP request.
    let (fetch, requests, _) = queued_fetch(vec![QueuedError {
        status: 500,
        headers: &[("retry-after-ms", "0")],
        message: "server error",
    }]);

    let message = consume(fetch, None, None).await;

    assert_eq!(recorded(&requests).len(), 1);
    assert_eq!(message.stop_reason, StopReason::Error);
}

#[tokio::test(start_paused = true)]
async fn honors_provider_retries_while_keeping_sdk_retries_disabled() {
    let (fetch, requests, instants) = queued_fetch(vec![
        QueuedError {
            status: 429,
            headers: &[("retry-after-ms", "100")],
            message: "rate limited",
        },
        QueuedError {
            status: 500,
            headers: &[("retry-after-ms", "100")],
            message: "server error",
        },
    ]);
    let start = tokio::time::Instant::now();

    let message = consume(fetch, Some(2), Some(100.0)).await;

    // TS: 1 request at 0ms, still 1 at 99ms, 2 at 100ms, still 2 at 199ms, 3 at 200ms.
    let offsets: Vec<Duration> = instants
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .iter()
        .map(|instant| instant.duration_since(start))
        .collect();
    assert_eq!(
        offsets,
        vec![
            Duration::ZERO,
            Duration::from_millis(100),
            Duration::from_millis(200),
        ]
    );
    assert_eq!(recorded(&requests).len(), 3);
    assert_eq!(message.stop_reason, StopReason::Stop);
}

#[tokio::test]
async fn fails_immediately_when_a_provider_requested_retry_delay_exceeds_the_limit() {
    let (fetch, requests, _) = queued_fetch(vec![QueuedError {
        status: 429,
        headers: &[("retry-after", "277403")],
        message: "rate limited",
    }]);

    let result = consume(fetch, Some(2), Some(1000.0)).await;

    assert_eq!(result.stop_reason, StopReason::Error);
    let error_message = result.error_message.unwrap_or_default();
    assert!(
        error_message.contains("Server requested 277403s retry delay (max: 1s)"),
        "{error_message}"
    );
    assert!(error_message.contains("rate limited"), "{error_message}");
    assert_eq!(recorded(&requests).len(), 1);
}
