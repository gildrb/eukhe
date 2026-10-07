//! SSE transport cases of `openai-codex-stream.test.ts` and the Codex case
//! of `max-thinking.test.ts`.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use bytes::Bytes;
use eukhe_chord::context::AbortController;
use eukhe_types::pi_ai::{
    AssistantMessageEvent, CacheRetention, JsonObject, JsonValue, Model, StopReason, ThinkingLevel,
    Transport,
};
use futures::StreamExt;
use serde_json::json;

use super::super::{stream, stream_simple};
use super::support::{
    build_sse_payload, collect_events, context, first_text, isolate, mock_fetch, mock_token, model,
    model_with, open_sse_response, say_hello, sse_frames, sse_response, user, DropFlag, FetchCall,
};
use crate::providers::all::get_builtin_model;
use crate::types::{
    FetchFunction, OnPayload, OnProviderStreamEvent, ProviderStreamOptions, SimpleStreamOptions,
    StreamOptions,
};
use crate::utils::diagnostics::ErrorObject;
use crate::utils::pi_user_agent::get_pi_user_agent;

const CODEX_URL: &str = "https://chatgpt.com/backend-api/codex/responses";

fn sse_options(fetch: FetchFunction) -> StreamOptions {
    let mut options = StreamOptions {
        transport: Some(Transport::Sse),
        ..StreamOptions::default()
    };
    options.request.api_key = Some(mock_token("acc_test"));
    options.request.fetch = Some(fetch);
    options
}

fn provider_options(stream: StreamOptions, extra: JsonValue) -> ProviderStreamOptions {
    ProviderStreamOptions {
        stream,
        extra: match extra {
            JsonValue::Object(extra) => extra,
            _ => JsonObject::new(),
        },
    }
}

/// A fetch answering every call with a complete SSE body.
fn completed_fetch() -> (FetchFunction, Arc<super::support::FetchRecorder>) {
    mock_fetch(|_, _| {
        Box::pin(async { Ok(sse_response(&build_sse_payload("completed", false, None))) })
    })
}

fn capture_payload() -> (OnPayload<Model>, Arc<Mutex<Option<JsonValue>>>) {
    let captured = Arc::new(Mutex::new(None));
    let sink = Arc::clone(&captured);
    let on_payload: OnPayload<Model> = Arc::new(move |payload, _model| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(payload);
        Box::pin(async { Ok(None) })
    });
    (on_payload, captured)
}

fn last_body(calls: &[FetchCall]) -> JsonValue {
    calls
        .last()
        .and_then(FetchCall::json_body)
        .expect("request body")
}

#[tokio::test]
async fn streams_sse_responses_and_forwards_raw_provider_events() {
    let _isolation = isolate().await;
    let token = mock_token("acc_test");
    let (fetch, calls) = completed_fetch();
    let events_seen = Arc::new(Mutex::new(Vec::<(JsonValue, Model)>::new()));
    let sink = Arc::clone(&events_seen);
    let on_event: OnProviderStreamEvent = Arc::new(move |event, event_model| {
        sink.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push((event.clone(), event_model.clone()));
        Box::pin(async { Ok(()) })
    });
    let mut options = sse_options(fetch);
    options.on_provider_stream_event = Some(on_event);
    let model = model();

    let result = stream(&model, &say_hello(), provider_options(options, json!({})));
    let events = collect_events(&result).await;

    assert!(events
        .iter()
        .any(|event| matches!(event, AssistantMessageEvent::TextDelta { .. })));
    let done = events
        .iter()
        .find_map(|event| match event {
            AssistantMessageEvent::Done { message, .. } => Some(message.clone()),
            _ => None,
        })
        .expect("done event");
    assert_eq!(first_text(&done).as_deref(), Some("Hello"));

    let call = &calls.calls()[0];
    assert_eq!(call.url, CODEX_URL);
    let header = |name: &str| {
        call.headers
            .get(name)
            .map(|value| value.to_str().expect("ascii").to_owned())
    };
    assert_eq!(header("Authorization"), Some(format!("Bearer {token}")));
    assert_eq!(header("chatgpt-account-id").as_deref(), Some("acc_test"));
    assert_eq!(
        header("OpenAI-Beta").as_deref(),
        Some("responses=experimental")
    );
    assert_eq!(header("originator").as_deref(), Some("pi"));
    assert_eq!(header("User-Agent").as_deref(), Some(get_pi_user_agent()));
    assert_eq!(header("accept").as_deref(), Some("text/event-stream"));
    assert!(!call.headers.contains_key("x-api-key"));

    let seen = events_seen
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    let types: Vec<&str> = seen
        .iter()
        .map(|(event, _)| event["type"].as_str().unwrap_or(""))
        .collect();
    assert_eq!(
        types,
        [
            "response.output_item.added",
            "response.content_part.added",
            "response.output_text.delta",
            "response.output_item.done",
            "response.completed",
        ]
    );
    assert!(seen.iter().all(|(_, event_model)| *event_model == model));
}

// Regression test for https://github.com/earendil-works/pi/issues/9047
#[tokio::test]
async fn processes_a_terminal_sse_event_without_a_trailing_blank_line() {
    let _isolation = isolate().await;
    let sse = build_sse_payload("completed", false, None)
        .trim_end()
        .to_owned();
    let (fetch, _calls) = mock_fetch(move |_, _| {
        let sse = sse.clone();
        Box::pin(async move { Ok(sse_response(&sse)) })
    });

    let result = stream(
        &model(),
        &say_hello(),
        provider_options(sse_options(fetch), json!({})),
    )
    .result()
    .await;

    assert_eq!(result.stop_reason, StopReason::Stop);
    assert_eq!(first_text(&result).as_deref(), Some("Hello"));
}

#[tokio::test]
async fn completes_after_response_completed_even_when_the_sse_body_stays_open() {
    let _isolation = isolate().await;
    let (fetch, _calls) = mock_fetch(|_, _| {
        Box::pin(async {
            Ok(open_sse_response(&build_sse_payload(
                "completed",
                true,
                Some(false),
            )))
        })
    });

    let result = tokio::time::timeout(
        Duration::from_secs(1),
        stream(
            &model(),
            &say_hello(),
            provider_options(sse_options(fetch), json!({})),
        )
        .result(),
    )
    .await
    .expect("Timed out waiting for completed SSE stream");

    assert_eq!(first_text(&result).as_deref(), Some("Hello"));
    assert_eq!(result.stop_reason, StopReason::Stop);
    assert_eq!(result.end_turn, Some(false));
}

#[tokio::test]
async fn maps_response_incomplete_to_stop_reason_length_even_when_the_sse_body_stays_open() {
    let _isolation = isolate().await;
    let (fetch, _calls) = mock_fetch(|_, _| {
        Box::pin(async {
            Ok(open_sse_response(&build_sse_payload(
                "incomplete",
                false,
                None,
            )))
        })
    });

    let result = tokio::time::timeout(
        Duration::from_secs(1),
        stream(
            &model(),
            &say_hello(),
            provider_options(sse_options(fetch), json!({})),
        )
        .result(),
    )
    .await
    .expect("Timed out waiting for incomplete SSE stream");

    assert_eq!(first_text(&result).as_deref(), Some("Hello"));
    assert_eq!(result.stop_reason, StopReason::Length);
}

#[tokio::test(start_paused = true)]
async fn aborts_sse_fetch_after_the_configured_http_timeout_when_response_headers_do_not_arrive() {
    let _isolation = isolate().await;
    let (fetch, calls) = mock_fetch(|_, call| {
        assert_eq!(call.url, CODEX_URL, "Unexpected URL");
        Box::pin(std::future::pending())
    });
    let mut options = sse_options(fetch);
    options.request.timeout_ms = Some(10.0);

    let result = stream(&model(), &say_hello(), provider_options(options, json!({})))
        .result()
        .await;

    assert_eq!(calls.count(), 1);
    assert_eq!(result.stop_reason, StopReason::Error);
    assert_eq!(
        result.error_message.as_deref(),
        Some("Codex SSE response headers timed out after 10ms")
    );
}

#[tokio::test]
async fn aborts_sse_body_reads_after_response_headers_arrive() {
    let _isolation = isolate().await;
    let cancelled = Arc::new(AtomicBool::new(false));
    let body_cancelled = Arc::clone(&cancelled);
    let (fetch, _calls) = mock_fetch(move |_, _| {
        let flag = DropFlag(Arc::clone(&body_cancelled));
        let first = sse_frames(&[
            json!({
                "type": "response.output_item.added",
                "item": { "type": "message", "id": "msg_1", "role": "assistant", "status": "in_progress", "content": [] },
            }),
            json!({ "type": "response.content_part.added", "part": { "type": "output_text", "text": "" } }),
            json!({ "type": "response.output_text.delta", "delta": "one" }),
        ]);
        let second = sse_frames(&[json!({ "type": "response.output_text.delta", "delta": "two" })]);
        let last = sse_frames(&[
            json!({
                "type": "response.output_item.done",
                "item": {
                    "type": "message",
                    "id": "msg_1",
                    "role": "assistant",
                    "status": "completed",
                    "content": [{ "type": "output_text", "text": "onetwo" }],
                },
            }),
            json!({
                "type": "response.completed",
                "response": {
                    "status": "completed",
                    "usage": { "input_tokens": 5, "output_tokens": 3, "total_tokens": 8, "input_tokens_details": { "cached_tokens": 0 } },
                },
            }),
        ]);
        let chunks = futures::stream::unfold((0, flag), move |(step, flag)| {
            let (first, second, last) = (first.clone(), second.clone(), last.clone());
            async move {
                let chunk = match step {
                    0 => first,
                    1 => {
                        tokio::time::sleep(Duration::from_millis(10)).await;
                        second
                    }
                    2 => {
                        tokio::time::sleep(Duration::from_millis(10)).await;
                        last
                    }
                    _ => return None,
                };
                Some((
                    Ok::<_, std::io::Error>(Bytes::from(chunk)),
                    (step + 1, flag),
                ))
            }
        });
        Box::pin(async move {
            Ok(super::support::http_response(
                200,
                &[("content-type", "text/event-stream")],
                reqwest::Body::wrap_stream(chunks),
            ))
        })
    });
    let controller = AbortController::new();
    let mut options = sse_options(fetch);
    options.request.signal = Some(controller.signal());

    let result_stream = stream(&model(), &say_hello(), provider_options(options, json!({})));
    let mut events = Vec::new();
    let mut iter = result_stream.events();
    while let Some(event) = iter.next().await {
        if let AssistantMessageEvent::TextDelta { delta, .. } = &event {
            events.push(format!("text_delta:{delta}"));
            if delta == "one" {
                controller.abort(None);
            }
        } else {
            events.push(event.type_name().to_owned());
        }
    }

    let result = result_stream.result().await;
    assert_eq!(result.stop_reason, StopReason::Aborted);
    assert_eq!(result.error_message.as_deref(), Some("Request was aborted"));
    assert!(events.contains(&"text_delta:one".to_owned()));
    assert!(!events.contains(&"text_delta:two".to_owned()));
    assert!(cancelled.load(Ordering::SeqCst));
}

#[tokio::test]
async fn sets_session_id_x_client_request_id_headers_and_prompt_cache_key_when_session_id_is_provided(
) {
    let _isolation = isolate().await;
    let session_id = "test-session-123";
    let (fetch, calls) = completed_fetch();
    let mut options = sse_options(fetch);
    options.session_id = Some(session_id.to_owned());

    stream(&model(), &say_hello(), provider_options(options, json!({})))
        .result()
        .await;

    let call = &calls.calls()[0];
    assert_eq!(
        call.headers.get("session-id").map(|v| v.to_str().ok()),
        Some(Some(session_id))
    );
    assert!(!call.headers.contains_key("session_id"));
    assert_eq!(
        call.headers
            .get("x-client-request-id")
            .map(|v| v.to_str().ok()),
        Some(Some(session_id))
    );
    assert_eq!(
        call.json_body().expect("body")["prompt_cache_key"],
        json!(session_id)
    );
}

#[tokio::test]
async fn omits_sse_cache_affinity_when_cache_retention_is_none() {
    let _isolation = isolate().await;
    let (fetch, calls) = completed_fetch();
    let mut options = sse_options(fetch);
    options.cache_retention = Some(CacheRetention::None);
    options.session_id = Some("one-off-summary".to_owned());

    stream(&model(), &say_hello(), provider_options(options, json!({})))
        .result()
        .await;

    let call = &calls.calls()[0];
    assert!(!call.headers.contains_key("session-id"));
    assert!(!call.headers.contains_key("x-client-request-id"));
    assert!(call
        .json_body()
        .expect("body")
        .get("prompt_cache_key")
        .is_none());
}

#[tokio::test]
async fn clamps_prompt_cache_key_to_openai_s_64_character_limit() {
    let _isolation = isolate().await;
    let (fetch, _calls) = completed_fetch();
    let (on_payload, captured) = capture_payload();
    let mut options = sse_options(fetch);
    options.session_id = Some("x".repeat(67));
    options.request.on_payload = Some(on_payload);

    stream(&model(), &say_hello(), provider_options(options, json!({})))
        .result()
        .await;

    let payload = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("payload");
    assert_eq!(payload["prompt_cache_key"], json!("x".repeat(64)));
}

#[tokio::test]
async fn clamps_codex_session_id_header_to_64_characters() {
    let _isolation = isolate().await;
    let (fetch, calls) = completed_fetch();
    let mut options = sse_options(fetch);
    options.session_id = Some("x".repeat(67));

    stream(&model(), &say_hello(), provider_options(options, json!({})))
        .result()
        .await;

    let call = &calls.calls()[0];
    let expected = "x".repeat(64);
    assert_eq!(
        call.headers.get("session-id").and_then(|v| v.to_str().ok()),
        Some(expected.as_str())
    );
    assert_eq!(
        call.headers
            .get("x-client-request-id")
            .and_then(|v| v.to_str().ok()),
        Some(expected.as_str())
    );
}

#[tokio::test]
async fn preserves_gpt_5_5_xhigh_reasoning_effort_from_simple_options() {
    let _isolation = isolate().await;
    let (fetch, calls) = completed_fetch();
    let model = model_with(
        json!({ "id": "gpt-5.5", "name": "GPT-5.5", "thinkingLevelMap": { "xhigh": "xhigh" } }),
    );

    stream_simple(
        &model,
        &say_hello(),
        SimpleStreamOptions {
            stream: sse_options(fetch),
            reasoning: Some(ThinkingLevel::Xhigh),
            ..SimpleStreamOptions::default()
        },
    )
    .result()
    .await;

    assert_eq!(
        last_body(&calls.calls())["reasoning"],
        json!({ "effort": "xhigh", "summary": "auto" })
    );
}

fn ping_tool() -> JsonValue {
    json!([{
        "name": "ping",
        "description": "Ping",
        "parameters": { "type": "object", "properties": { "value": { "type": "string" } }, "required": ["value"] },
    }])
}

#[tokio::test]
async fn forwards_required_tool_choice() {
    let _isolation = isolate().await;
    let (fetch, calls) = completed_fetch();
    let model = model_with(json!({ "id": "gpt-5.5", "name": "GPT-5.5" }));
    let context = context(
        None,
        vec![user("Do not call ping. Respond with text instead.", 1)],
        Some(ping_tool()),
    );

    stream(
        &model,
        &context,
        provider_options(sse_options(fetch), json!({ "toolChoice": "required" })),
    )
    .result()
    .await;

    assert_eq!(last_body(&calls.calls())["tool_choice"], json!("required"));
}

#[tokio::test]
async fn sets_codex_strict_mode_explicitly_and_honors_constrained_sampling() {
    let _isolation = isolate().await;
    let (fetch, _calls) = completed_fetch();
    let (on_payload, captured) = capture_payload();
    let model = model_with(json!({ "id": "gpt-5.5", "name": "GPT-5.5" }));
    let context = context(
        None,
        vec![user("Use a tool", 1)],
        Some(json!([
            {
                "name": "optional",
                "description": "Optional constrained sampling",
                "parameters": { "type": "object", "properties": { "value": { "type": "string" } }, "required": ["value"] },
                "constrainedSampling": false,
            },
            {
                "name": "strict",
                "description": "Strict constrained sampling",
                "parameters": {
                    "additionalProperties": false,
                    "type": "object",
                    "properties": { "value": { "type": "string" } },
                    "required": ["value"],
                },
                "constrainedSampling": { "type": "json_schema", "strict": "prefer" },
            },
        ])),
    );
    let mut options = sse_options(fetch);
    options.request.on_payload = Some(on_payload);

    stream(&model, &context, provider_options(options, json!({})))
        .result()
        .await;

    let payload = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("payload");
    let tools = payload["tools"].as_array().expect("tools");
    assert_eq!(tools.len(), 2);
    assert_eq!(
        (&tools[0]["type"], &tools[0]["name"], &tools[0]["strict"]),
        (&json!("function"), &json!("optional"), &JsonValue::Null)
    );
    assert_eq!(
        (&tools[1]["type"], &tools[1]["name"], &tools[1]["strict"]),
        (&json!("function"), &json!("strict"), &json!(true))
    );
}

#[tokio::test]
async fn clamps_minimal_reasoning_effort_to_low() {
    for model_id in ["gpt-5.3-codex", "gpt-5.4", "gpt-5.5"] {
        let _isolation = isolate().await;
        let (fetch, calls) = completed_fetch();
        let model = model_with(
            json!({ "id": model_id, "name": model_id, "thinkingLevelMap": { "minimal": "low" } }),
        );

        stream(
            &model,
            &say_hello(),
            provider_options(sse_options(fetch), json!({ "reasoningEffort": "minimal" })),
        )
        .result()
        .await;

        assert_eq!(
            last_body(&calls.calls())["reasoning"],
            json!({ "effort": "low", "summary": "auto" }),
            "{model_id}"
        );
    }
}

#[tokio::test]
async fn uses_the_client_sent_service_tier_when_codex_echoes_default() {
    for (model_id, service_tier, multiplier) in [
        ("gpt-5.1-codex", "flex", 0.5),
        ("gpt-5.1-codex", "priority", 2.0),
        ("gpt-5.5", "flex", 0.5),
        ("gpt-5.5", "priority", 2.5),
    ] {
        let _isolation = isolate().await;
        let mut events = super::support::hello_events();
        events.push(json!({
            "type": "response.completed",
            "response": {
                "status": "completed",
                "service_tier": "default",
                "usage": {
                    "input_tokens": 1_000_000,
                    "output_tokens": 1_000_000,
                    "total_tokens": 2_000_000,
                    "input_tokens_details": { "cached_tokens": 0 },
                },
            },
        }));
        let sse = sse_frames(&events);
        let (fetch, _calls) = mock_fetch(move |_, _| {
            let sse = sse.clone();
            Box::pin(async move { Ok(sse_response(&sse)) })
        });
        let model = model_with(json!({
            "id": model_id,
            "name": if model_id == "gpt-5.5" { "GPT-5.5" } else { "GPT-5.1 Codex" },
            "cost": { "input": 1, "output": 2, "cacheRead": 0, "cacheWrite": 0 },
        }));

        let result = stream(
            &model,
            &say_hello(),
            provider_options(sse_options(fetch), json!({ "serviceTier": service_tier })),
        )
        .result()
        .await;

        let label = format!("{model_id} {service_tier}");
        assert!(
            (result.usage.cost.input - multiplier).abs() < f64::EPSILON,
            "{label}"
        );
        assert!(
            (result.usage.cost.output - 2.0 * multiplier).abs() < f64::EPSILON,
            "{label}"
        );
        assert!(
            (result.usage.cost.total - 3.0 * multiplier).abs() < f64::EPSILON,
            "{label}"
        );
    }
}

#[tokio::test]
async fn does_not_set_session_id_x_client_request_id_headers_when_session_id_is_not_provided() {
    let _isolation = isolate().await;
    let (fetch, calls) = completed_fetch();

    stream(
        &model(),
        &say_hello(),
        provider_options(sse_options(fetch), json!({})),
    )
    .result()
    .await;

    let call = &calls.calls()[0];
    assert!(!call.headers.contains_key("session-id"));
    assert!(!call.headers.contains_key("session_id"));
    assert!(!call.headers.contains_key("x-client-request-id"));
}

/// A fetch answering 429 `rate_limit_exceeded` with `headers` for the first
/// `failures` calls and a completed stream afterwards.
fn rate_limited_fetch(
    failures: usize,
    headers: Vec<(String, String)>,
) -> (FetchFunction, Arc<super::support::FetchRecorder>) {
    mock_fetch(move |index, call| {
        assert_eq!(call.url, CODEX_URL, "Unexpected URL");
        let headers = headers.clone();
        Box::pin(async move {
            if index < failures {
                let headers: Vec<(&str, &str)> = headers
                    .iter()
                    .map(|(n, v)| (n.as_str(), v.as_str()))
                    .collect();
                return Ok(super::support::http_response(
                    429,
                    &headers,
                    reqwest::Body::from(
                        json!({ "error": { "code": "rate_limit_exceeded", "message": "rate limited" } }).to_string(),
                    ),
                ));
            }
            Ok(sse_response(&build_sse_payload("completed", false, None)))
        })
    })
}

#[tokio::test(start_paused = true)]
async fn uses_retry_after_headers_for_sse_retries() {
    type RetryCase = (&'static str, Vec<(String, String)>, f64, f64);
    let http_date = {
        // `new Date(Date.now() + 45_000).toUTCString()`.
        let target = super::super::clock_ms() + 45_000.0;
        format_http_date(target)
    };
    let cases: [RetryCase; 3] = [
        (
            "retry-after-ms",
            vec![
                ("content-type".into(), "application/json".into()),
                ("retry-after-ms".into(), "1500".into()),
            ],
            1500.0,
            1500.0,
        ),
        (
            "retry-after seconds",
            vec![
                ("content-type".into(), "application/json".into()),
                ("retry-after".into(), "60".into()),
            ],
            60_000.0,
            60_000.0,
        ),
        (
            // The HTTP date has whole-second precision and the clock is real:
            // the delay lands within the second before the 45s target.
            "retry-after HTTP date",
            vec![
                ("content-type".into(), "application/json".into()),
                ("retry-after".into(), http_date),
            ],
            43_000.0,
            45_000.0,
        ),
    ];
    for (name, headers, min_delay, max_delay) in cases {
        let _isolation = isolate().await;
        let (fetch, calls) = rate_limited_fetch(1, headers);
        let mut options = sse_options(fetch);
        options.request.max_retries = Some(1);

        let result = stream(&model(), &say_hello(), provider_options(options, json!({})))
            .result()
            .await;

        assert_eq!(first_text(&result).as_deref(), Some("Hello"), "{name}");
        let calls = calls.calls();
        assert_eq!(calls.len(), 2, "{name}");
        // TS asserts `setTimeout(_, expectedDelay)`; paused time measures the wait.
        let waited = calls[1].at.duration_since(calls[0].at).as_secs_f64() * 1000.0;
        assert!(
            waited >= min_delay && waited <= max_delay,
            "{name}: waited {waited}ms"
        );
    }
}

/// `Date.prototype.toUTCString()` of a Unix-ms timestamp.
fn format_http_date(ms: f64) -> String {
    const DAYS: [&str; 7] = ["Thu", "Fri", "Sat", "Sun", "Mon", "Tue", "Wed"];
    const MONTHS: [&str; 12] = [
        "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    ];
    // Test timestamps are positive and far below 2^63 ms.
    #[allow(clippy::cast_possible_truncation)]
    let seconds = (ms / 1000.0).floor() as i64;
    let days = seconds.div_euclid(86_400);
    let secs_of_day = seconds.rem_euclid(86_400);
    // Howard Hinnant's civil_from_days.
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    let weekday = DAYS[usize::try_from(days.rem_euclid(7)).unwrap_or_default()];
    let month_name = MONTHS[usize::try_from(month - 1).unwrap_or_default()];
    format!(
        "{weekday}, {day:02} {month_name} {year} {:02}:{:02}:{:02} GMT",
        secs_of_day / 3600,
        secs_of_day % 3600 / 60,
        secs_of_day % 60
    )
}

#[tokio::test]
async fn fails_immediately_when_a_retry_delay_exceeds_the_limit() {
    for status in [429, 503] {
        let _isolation = isolate().await;
        let (fetch, calls) = mock_fetch(move |_, _| {
            Box::pin(async move {
                Ok(super::support::http_response(
                    status,
                    &[("content-type", "application/json"), ("retry-after", "2")],
                    reqwest::Body::from(
                        json!({ "error": { "code": "temporarily_unavailable", "message": "retry later" } }).to_string(),
                    ),
                ))
            })
        });
        let mut options = sse_options(fetch);
        options.request.max_retries = Some(3);
        options.request.max_retry_delay_ms = Some(1000.0);

        let result = stream(&model(), &say_hello(), provider_options(options, json!({})))
            .result()
            .await;

        assert_eq!(result.stop_reason, StopReason::Error, "{status}");
        assert_eq!(
            result.error_message.as_deref(),
            Some("Server requested 2s retry delay (max: 1s)"),
            "{status}"
        );
        assert_eq!(calls.count(), 1, "{status}");
    }
}

#[tokio::test]
async fn zstd_compresses_sse_request_bodies() {
    let _isolation = isolate().await;
    let (fetch, calls) = completed_fetch();
    let large_text = "compress me ".repeat(400);

    stream(
        &model(),
        &context(
            Some("You are a helpful assistant."),
            vec![user(&large_text, 1)],
            None,
        ),
        provider_options(sse_options(fetch.clone()), json!({})),
    )
    .result()
    .await;

    let call = &calls.calls()[0];
    assert_eq!(
        call.headers
            .get("content-encoding")
            .and_then(|v| v.to_str().ok()),
        Some("zstd")
    );
    let decoded: JsonValue = serde_json::from_slice(
        &zstd::decode_all(call.body.as_deref().expect("body")).expect("zstd"),
    )
    .expect("json");
    assert_eq!(decoded["input"][0]["content"][0]["text"], json!(large_text));

    stream(
        &model(),
        &context(
            Some("You are a helpful assistant."),
            vec![user("hi", 1)],
            None,
        ),
        provider_options(sse_options(fetch), json!({})),
    )
    .result()
    .await;

    let call = &calls.calls()[1];
    assert_eq!(
        call.headers
            .get("content-encoding")
            .and_then(|v| v.to_str().ok()),
        Some("zstd")
    );
    assert!(zstd::decode_all(call.body.as_deref().expect("body")).is_ok());
}

#[tokio::test(start_paused = true)]
async fn uses_exponential_backoff_across_repeated_sse_retries_without_retry_headers() {
    let _isolation = isolate().await;
    let (fetch, calls) =
        rate_limited_fetch(3, vec![("content-type".into(), "application/json".into())]);
    let mut options = sse_options(fetch);
    options.request.max_retries = Some(3);

    let result = stream(&model(), &say_hello(), provider_options(options, json!({})))
        .result()
        .await;

    assert_eq!(first_text(&result).as_deref(), Some("Hello"));
    let calls = calls.calls();
    assert_eq!(calls.len(), 4);
    let delays: Vec<u128> = calls
        .windows(2)
        .map(|pair| pair[1].at.duration_since(pair[0].at).as_millis())
        .collect();
    assert_eq!(delays, [1000, 2000, 4000]);
}

/// `max-thinking.test.ts`: "sends max to the Codex Responses API for %s".
#[tokio::test]
async fn sends_max_to_the_codex_responses_api() {
    for model_id in [
        "gpt-5.6-sol",
        "gpt-6-astra",
        "gpt-6-sol",
        "gpt-6-luna",
        "gpt-6.1-sol",
    ] {
        let _isolation = isolate().await;
        let model = get_builtin_model("openai-codex", model_id).expect("catalog model");
        let (on_payload_capture, captured) = capture_payload();
        let on_payload: crate::types::OnPayload<Model> = Arc::new(move |payload, model| {
            let capture = Arc::clone(&on_payload_capture);
            Box::pin(async move {
                capture(payload, model).await?;
                Err(ErrorObject::new("payload captured").thrown())
            })
        });
        let mut options = StreamOptions::default();
        options.request.api_key = Some(mock_token("acc_test"));
        options.request.on_payload = Some(on_payload);

        stream_simple(
            &model,
            &context(
                Some("You are a helpful assistant."),
                vec![user("Hello", 1)],
                None,
            ),
            SimpleStreamOptions {
                stream: options,
                reasoning: Some(ThinkingLevel::Max),
                ..SimpleStreamOptions::default()
            },
        )
        .result()
        .await;

        let payload = captured
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
            .expect("payload");
        assert_eq!(payload["reasoning"]["effort"], json!("max"), "{model_id}");
        assert_eq!(payload["reasoning"]["summary"], json!("auto"), "{model_id}");
    }
}
