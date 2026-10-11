//! WebSocket transport cases of `openai-codex-stream.test.ts`.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::pi_ai::{
    AssistantMessageEvent, CacheRetention, JsonObject, JsonValue, Model, StopReason, Transport,
};
use futures::StreamExt;
use serde_json::json;

use super::super::websocket::WebSocketEvent;
use super::super::{get_openai_codex_websocket_debug_stats, stream, stream_simple, test_clock};
use super::support::{
    assistant, build_sse_payload, context, first_text, hello_events, isolate, message, messages,
    mock_fetch, mock_token, mock_websocket, model, model_with, say_hello, sse_response,
    unexpected_fetch, user, FetchRecorder, MockWebSocketConfig, SendReply,
};
use crate::types::{
    FetchFunction, OnProviderStreamEvent, ProviderStreamOptions, SimpleStreamOptions, StreamOptions,
};

fn ws_options(
    transport: Transport,
    session_id: Option<&str>,
    fetch: FetchFunction,
    account_id: &str,
) -> StreamOptions {
    let mut options = StreamOptions {
        transport: Some(transport),
        session_id: session_id.map(str::to_owned),
        ..StreamOptions::default()
    };
    options.request.api_key = Some(mock_token(account_id));
    options.request.fetch = Some(fetch);
    options
}

fn provider_options(stream: StreamOptions) -> ProviderStreamOptions {
    ProviderStreamOptions {
        stream,
        extra: JsonObject::new(),
    }
}

fn completed(response_id: &str) -> JsonValue {
    json!({
        "type": "response.completed",
        "response": {
            "id": response_id,
            "status": "completed",
            "usage": { "input_tokens": 5, "output_tokens": 3, "total_tokens": 8 },
        },
    })
}

fn completed_sse_fetch() -> (FetchFunction, Arc<FetchRecorder>) {
    mock_fetch(|_, call| {
        assert_eq!(
            call.url, "https://chatgpt.com/backend-api/codex/responses",
            "Unexpected URL"
        );
        Box::pin(async { Ok(sse_response(&build_sse_payload("completed", false, None))) })
    })
}

/// Assert the debug stats of `session_id` match the listed camelCase fields.
fn assert_stats(session_id: &str, expected: &JsonValue) {
    let stats =
        serde_json::to_value(get_openai_codex_websocket_debug_stats(session_id).expect("stats"))
            .expect("serializable");
    for (key, value) in expected.as_object().expect("object") {
        assert_eq!(&stats[key], value, "stats.{key}");
    }
}

#[tokio::test]
async fn forwards_auto_transport_and_raw_provider_events_from_stream_simple() {
    let _isolation = isolate().await;
    let (fetch, fetch_calls) = unexpected_fetch();
    let recorder = mock_websocket(MockWebSocketConfig {
        open: true,
        ready_state: false,
        on_send: Box::new(|_, _, _| {
            let mut events = hello_events();
            events.push(json!({
                "type": "response.done",
                "response": {
                    "status": "completed",
                    "end_turn": false,
                    "usage": { "input_tokens": 5, "output_tokens": 3, "total_tokens": 8, "input_tokens_details": { "cached_tokens": 0 } },
                },
            }));
            messages(events)
        }),
    });
    let seen = Arc::new(Mutex::new(Vec::<(JsonValue, Model)>::new()));
    let sink = Arc::clone(&seen);
    let on_event: OnProviderStreamEvent = Arc::new(move |event, event_model| {
        sink.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push((event.clone(), event_model.clone()));
        Box::pin(async { Ok(()) })
    });
    let mut options = ws_options(Transport::Auto, Some("session-auto"), fetch, "acc_test");
    options.on_provider_stream_event = Some(on_event);
    let model = model();

    let result = stream_simple(
        &model,
        &say_hello(),
        SimpleStreamOptions {
            stream: options,
            ..SimpleStreamOptions::default()
        },
    )
    .result()
    .await;

    assert_eq!(result.end_turn, Some(false));
    assert_eq!(recorder.sent().len(), 1);
    let seen = seen.lock().unwrap_or_else(PoisonError::into_inner).clone();
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
            "response.done",
        ]
    );
    assert!(seen.iter().all(|(_, event_model)| *event_model == model));
    let headers = &recorder.headers()[0];
    assert_eq!(
        headers.get("session-id").map(String::as_str),
        Some("session-auto")
    );
    assert_eq!(headers.get("session_id"), None);
    assert_eq!(
        headers.get("x-client-request-id").map(String::as_str),
        Some("session-auto")
    );
    assert_eq!(fetch_calls.count(), 0);
    assert_stats(
        "session-auto",
        &json!({ "cachedContextRequests": 1, "fullContextRequests": 1 }),
    );
}

#[tokio::test]
async fn scopes_cached_websockets_to_the_authenticated_account() {
    // Regression for #7284: rotating accounts must not reuse a socket authenticated by another account.
    let _isolation = isolate().await;
    let (fetch, fetch_calls) = unexpected_fetch();
    let recorder = mock_websocket(MockWebSocketConfig {
        open: true,
        ready_state: true,
        on_send: Box::new(|_, _, index| {
            messages(vec![json!({
                "type": "response.completed",
                "response": {
                    "id": format!("resp_{index}"),
                    "status": "completed",
                    "usage": { "input_tokens": 1, "output_tokens": 1, "total_tokens": 2 },
                },
            })])
        }),
    });
    let context = context(Some(""), Vec::new(), None);

    for account in ["account-a", "account-b", "account-a"] {
        stream(
            &model(),
            &context,
            provider_options(ws_options(
                Transport::WebsocketCached,
                Some("shared-session"),
                fetch.clone(),
                account,
            )),
        )
        .result()
        .await;
    }

    let headers = recorder.headers();
    let accounts: Vec<&str> = headers
        .iter()
        .map(|headers| headers.get("chatgpt-account-id").map_or("", String::as_str))
        .collect();
    assert_eq!(accounts, ["account-a", "account-b"]);
    let authorizations: Vec<&str> = headers
        .iter()
        .map(|headers| headers.get("authorization").map_or("", String::as_str))
        .collect();
    assert_eq!(
        authorizations,
        [
            format!("Bearer {}", mock_token("account-a")),
            format!("Bearer {}", mock_token("account-b")),
        ]
    );
    assert_eq!(fetch_calls.count(), 0);
    assert_stats(
        "shared-session",
        &json!({ "connectionsCreated": 2, "connectionsReused": 1 }),
    );
}

#[tokio::test]
async fn closes_one_shot_websockets_when_cache_retention_is_none() {
    let _isolation = isolate().await;
    let (fetch, fetch_calls) = unexpected_fetch();
    let recorder = mock_websocket(MockWebSocketConfig {
        open: true,
        ready_state: false,
        on_send: Box::new(|connection, _, _| {
            messages(vec![completed(&format!("resp_{connection}"))])
        }),
    });

    for _ in 0..2 {
        let mut options = ws_options(
            Transport::Auto,
            Some("one-off-summary"),
            fetch.clone(),
            "acc_test",
        );
        options.cache_retention = Some(CacheRetention::None);
        stream(&model(), &say_hello(), provider_options(options))
            .result()
            .await;
    }

    assert_eq!(recorder.connections(), 2);
    assert_eq!(recorder.closed(), 2);
    let sent = recorder.sent();
    assert_eq!(sent.len(), 2);
    assert!(sent
        .iter()
        .all(|(_, body)| body.get("prompt_cache_key").is_none()));
    assert_eq!(
        get_openai_codex_websocket_debug_stats("one-off-summary"),
        None
    );
    assert_eq!(fetch_calls.count(), 0);
}

#[tokio::test(start_paused = true)]
async fn falls_back_to_sse_when_websocket_connect_does_not_open_before_the_connect_timeout() {
    let _isolation = isolate().await;
    let (fetch, fetch_calls) = completed_sse_fetch();
    mock_websocket(MockWebSocketConfig {
        open: false,
        ready_state: false,
        on_send: Box::new(|_, _, _| {
            SendReply::Throw("send should not be called before websocket open".into())
        }),
    });
    let mut options = ws_options(
        Transport::Auto,
        Some("ws-connect-timeout"),
        fetch,
        "acc_test",
    );
    options.request.timeout_ms = Some(300_000.0);
    options.websocket_connect_timeout_ms = Some(50.0);

    let result = stream(&model(), &say_hello(), provider_options(options))
        .result()
        .await;

    assert_eq!(first_text(&result).as_deref(), Some("Hello"));
    assert_eq!(fetch_calls.count(), 1);
    assert_stats(
        "ws-connect-timeout",
        &json!({
            "websocketFailures": 1,
            "sseFallbacks": 1,
            "websocketFallbackActive": true,
            "lastWebSocketError": "WebSocket connect timeout after 50ms",
        }),
    );
}

#[tokio::test]
async fn reconnects_once_when_the_websocket_connection_limit_is_reached_before_output_starts() {
    let _isolation = isolate().await;
    let (fetch, fetch_calls) = unexpected_fetch();
    let recorder = mock_websocket(MockWebSocketConfig {
        open: true,
        ready_state: false,
        on_send: Box::new(|connection, _, _| {
            if connection == 1 {
                messages(vec![
                    json!({ "type": "error", "error": { "code": "websocket_connection_limit_reached" } }),
                ])
            } else {
                messages(vec![completed("resp_1")])
            }
        }),
    });
    let mut options = StreamOptions::default();
    options.request.api_key = Some(mock_token("acc_test"));
    options.request.fetch = Some(fetch);

    let result = stream(
        &model(),
        &context(Some(""), Vec::new(), None),
        provider_options(options),
    )
    .result()
    .await;

    assert_eq!(result.stop_reason, StopReason::Stop);
    assert_eq!(recorder.connections(), 2);
    assert_eq!(fetch_calls.count(), 0);
}

#[tokio::test(start_paused = true)]
async fn falls_back_to_sse_when_a_websocket_is_idle_before_the_first_event() {
    let _isolation = isolate().await;
    let (fetch, fetch_calls) = completed_sse_fetch();
    let recorder = mock_websocket(MockWebSocketConfig {
        open: true,
        ready_state: true,
        on_send: Box::new(|_, _, _| SendReply::Events(Vec::new())),
    });
    let mut options = ws_options(
        Transport::Auto,
        Some("ws-idle-before-start"),
        fetch,
        "acc_test",
    );
    options.request.timeout_ms = Some(50.0);

    let result = stream(&model(), &say_hello(), provider_options(options))
        .result()
        .await;

    assert_eq!(recorder.sent().len(), 1);
    assert_eq!(first_text(&result).as_deref(), Some("Hello"));
    assert_eq!(fetch_calls.count(), 1);
    assert_stats(
        "ws-idle-before-start",
        &json!({ "websocketFailures": 1, "sseFallbacks": 1, "websocketFallbackActive": true }),
    );
}

#[tokio::test(start_paused = true)]
async fn errors_when_a_websocket_is_idle_after_the_stream_started() {
    let _isolation = isolate().await;
    let (fetch, fetch_calls) = unexpected_fetch();
    mock_websocket(MockWebSocketConfig {
        open: true,
        ready_state: true,
        on_send: Box::new(|_, _, _| {
            messages(vec![json!({
                "type": "response.output_item.added",
                "item": { "type": "message", "id": "msg_1", "role": "assistant", "status": "in_progress", "content": [] },
            })])
        }),
    });
    let mut options = ws_options(Transport::Auto, None, fetch, "acc_test");
    options.request.timeout_ms = Some(50.0);

    let result = stream(&model(), &say_hello(), provider_options(options))
        .result()
        .await;

    assert_eq!(result.stop_reason, StopReason::Error);
    assert_eq!(
        result.error_message.as_deref(),
        Some("WebSocket idle timeout after 50ms")
    );
    assert_eq!(fetch_calls.count(), 0);
}

#[tokio::test]
async fn opens_a_fresh_cached_websocket_before_the_backend_connection_age_limit() {
    let _isolation = isolate().await;
    let (fetch, _fetch_calls) = unexpected_fetch();
    let recorder = mock_websocket(MockWebSocketConfig {
        open: true,
        ready_state: true,
        on_send: Box::new(|connection, _, _| {
            messages(vec![completed(&format!("resp_{connection}"))])
        }),
    });
    let session_id = "aged-ws-session";
    let first_context = say_hello();

    let first = stream(
        &model(),
        &first_context,
        provider_options(ws_options(
            Transport::WebsocketCached,
            Some(session_id),
            fetch.clone(),
            "acc_test",
        )),
    )
    .result()
    .await;
    // TS `vi.setSystemTime(startedAt + 56 min)`.
    test_clock::set_offset_ms(56.0 * 60.0 * 1000.0);
    let mut messages = first_context.messages().to_vec();
    messages.push(assistant(first));
    messages.push(user("Now finish", 2));
    let second_context = context(None, messages, None);

    stream(
        &model(),
        &second_context,
        provider_options(ws_options(
            Transport::WebsocketCached,
            Some(session_id),
            fetch,
            "acc_test",
        )),
    )
    .result()
    .await;

    assert_eq!(recorder.connections(), 2);
    let connection_ids: Vec<usize> = recorder.sent().iter().map(|(id, _)| *id).collect();
    assert_eq!(connection_ids, [1, 2]);
    assert_stats(
        session_id,
        &json!({ "connectionsCreated": 2, "connectionsReused": 0 }),
    );
}

#[tokio::test]
#[allow(clippy::too_many_lines)] // One TS case with its mock socket.
async fn sends_only_response_input_deltas_in_websocket_cached_mode() {
    let _isolation = isolate().await;
    let (fetch, _fetch_calls) = unexpected_fetch();
    let recorder = mock_websocket(MockWebSocketConfig {
        open: true,
        ready_state: true,
        on_send: Box::new(|_, _, index| {
            let response_id = format!("resp_{index}");
            let mut events =
                vec![json!({ "type": "response.created", "response": { "id": response_id } })];
            if index == 1 {
                events.extend([
                    json!({
                        "type": "response.output_item.added",
                        "item": { "type": "custom_tool_call", "id": "ctc_1", "call_id": "call_1", "name": "sample_tool", "input": "" },
                    }),
                    json!({ "type": "response.custom_tool_call_input.delta", "item_id": "ctc_1", "delta": "abc" }),
                    json!({ "type": "response.custom_tool_call_input.done", "item_id": "ctc_1", "input": "abc" }),
                    json!({
                        "type": "response.output_item.done",
                        "item": { "type": "custom_tool_call", "id": "ctc_1", "call_id": "call_1", "name": "sample_tool", "input": "abc" },
                    }),
                ]);
            }
            events.push(json!({
                "type": "response.completed",
                "response": {
                    "id": response_id,
                    "status": "completed",
                    "usage": { "input_tokens": 5, "output_tokens": 3, "total_tokens": 8, "input_tokens_details": { "cached_tokens": 0 } },
                },
            }));
            messages(events)
        }),
    });
    let model = model_with(json!({ "compat": { "supportsOpenAIGrammarTools": true } }));
    let tools = json!([{
        "name": "sample_tool",
        "description": "Sample tool",
        "parameters": { "type": "object", "properties": { "payload": { "type": "string" } }, "required": ["payload"] },
        "constrainedSampling": { "type": "grammar", "variants": { "openai_lark": "start: /[a-z]+/" } },
    }]);
    let system_prompt = Some("You are a helpful assistant.");

    let first = stream(
        &model,
        &context(
            system_prompt,
            vec![user("Use the tool", 1)],
            Some(tools.clone()),
        ),
        provider_options(ws_options(
            Transport::WebsocketCached,
            Some("session-1"),
            fetch.clone(),
            "acc_test",
        )),
    )
    .result()
    .await;

    let second_context = context(
        system_prompt,
        vec![
            user("Use the tool", 1),
            assistant(first),
            message(json!({
                "role": "toolResult",
                "toolCallId": "call_1|ctc_1",
                "toolName": "sample_tool",
                "content": [{ "type": "text", "text": "real result" }],
                "isError": false,
                "timestamp": 2,
            })),
            user("Now finish", 3),
        ],
        Some(tools),
    );
    stream(
        &model,
        &second_context,
        provider_options(ws_options(
            Transport::WebsocketCached,
            Some("session-1"),
            fetch,
            "acc_test",
        )),
    )
    .result()
    .await;

    let sent = recorder.sent();
    assert_eq!(sent.len(), 2);
    let (first_body, second_body) = (&sent[0].1, &sent[1].1);
    assert_eq!(first_body["store"], json!(false));
    assert!(first_body.get("previous_response_id").is_none());
    assert_eq!(
        first_body["input"],
        json!([{ "role": "user", "content": [{ "type": "input_text", "text": "Use the tool" }] }])
    );
    assert_eq!(second_body["store"], json!(false));
    assert_eq!(second_body["previous_response_id"], json!("resp_1"));
    assert_eq!(
        second_body["input"],
        json!([
            { "type": "custom_tool_call_output", "call_id": "call_1", "output": "real result" },
            { "role": "user", "content": [{ "type": "input_text", "text": "Now finish" }] },
        ])
    );
    assert_stats(
        "session-1",
        &json!({
            "requests": 2,
            "connectionsCreated": 1,
            "connectionsReused": 1,
            "cachedContextRequests": 2,
            "storeTrueRequests": 0,
            "fullContextRequests": 1,
            "deltaRequests": 1,
            "lastDeltaInputItems": 2,
            "lastPreviousResponseId": "resp_1",
        }),
    );
}

#[tokio::test]
#[allow(clippy::too_many_lines)] // One TS case with its mock socket.
async fn recovers_a_missing_cached_websocket_continuation() {
    for recovery_transport in ["websocket", "sse"] {
        let _isolation = isolate().await;
        let session_id = format!("missing-continuation-{recovery_transport}");
        let (fetch, fetch_calls) = mock_fetch(|_, _| {
            Box::pin(async { Ok(sse_response(&build_sse_payload("completed", false, None))) })
        });
        let recorder = mock_websocket(MockWebSocketConfig {
            open: true,
            ready_state: true,
            on_send: Box::new(move |_, _, index| {
                if index == 2 {
                    return messages(vec![
                        json!({
                            "type": "codex.rate_limits",
                            "plan_type": "plus",
                            "rate_limits": {
                                "allowed": true,
                                "limit_reached": false,
                                "primary": { "used_percent": 7, "window_minutes": 10080, "reset_after_seconds": 556_112, "reset_at": 1_785_269_351 },
                                "secondary": null,
                            },
                            "code_review_rate_limits": null,
                            "additional_rate_limits": null,
                            "credits": { "has_credits": false, "unlimited": false, "balance": "0" },
                            "promo": null,
                        }),
                        json!({
                            "type": "error",
                            "status": 400,
                            "error": {
                                "code": "previous_response_not_found",
                                "message": "Previous response with id 'resp_1' not found.",
                                "param": "previous_response_id",
                            },
                        }),
                    ]);
                }
                if index == 3 && recovery_transport == "sse" {
                    return SendReply::Events(vec![WebSocketEvent::Error {
                        message: Some("retry websocket failed".into()),
                    }]);
                }
                let (response_id, message_id, text) = if index == 1 {
                    ("resp_1", "msg_1", "Hello")
                } else {
                    ("resp_2", "msg_2", "Recovered")
                };
                messages(vec![
                    json!({ "type": "response.created", "response": { "id": response_id } }),
                    json!({
                        "type": "response.output_item.added",
                        "output_index": 0,
                        "item": { "type": "message", "id": message_id, "role": "assistant", "status": "in_progress", "content": [] },
                    }),
                    json!({
                        "type": "response.output_item.done",
                        "output_index": 0,
                        "item": {
                            "type": "message",
                            "id": message_id,
                            "role": "assistant",
                            "status": "completed",
                            "content": [{ "type": "output_text", "text": text }],
                        },
                    }),
                    completed(response_id),
                ])
            }),
        });
        let first_context = say_hello();

        let first = stream(
            &model(),
            &first_context,
            provider_options(ws_options(
                Transport::WebsocketCached,
                Some(&session_id),
                fetch.clone(),
                "acc_test",
            )),
        )
        .result()
        .await;
        let mut second_messages = first_context.messages().to_vec();
        second_messages.push(assistant(first));
        second_messages.push(user("Now finish", 2));
        let second_stream = stream(
            &model(),
            &context(None, second_messages, None),
            provider_options(ws_options(
                Transport::WebsocketCached,
                Some(&session_id),
                fetch,
                "acc_test",
            )),
        );
        let event_types: Vec<&'static str> = second_stream
            .events()
            .map(|event: AssistantMessageEvent| event.type_name())
            .collect()
            .await;
        let second = second_stream.result().await;

        let label = recovery_transport;
        assert_eq!(second.stop_reason, StopReason::Stop, "{label}");
        assert_eq!(
            first_text(&second).as_deref(),
            Some(if recovery_transport == "sse" {
                "Hello"
            } else {
                "Recovered"
            }),
            "{label}"
        );
        assert_eq!(
            event_types.iter().filter(|kind| **kind == "start").count(),
            1,
            "{label}"
        );
        assert!(!event_types.contains(&"error"), "{label}");
        assert_eq!(recorder.connections(), 2, "{label}");
        let sent = recorder.sent();
        assert_eq!(sent.len(), 3, "{label}");
        let connection_ids: Vec<usize> = sent.iter().map(|(id, _)| *id).collect();
        assert_eq!(connection_ids, [1, 1, 2], "{label}");
        assert_eq!(
            sent[1].1["previous_response_id"],
            json!("resp_1"),
            "{label}"
        );
        assert_eq!(
            sent[1].1["input"],
            json!([{ "role": "user", "content": [{ "type": "input_text", "text": "Now finish" }] }]),
            "{label}"
        );
        assert!(sent[2].1.get("previous_response_id").is_none(), "{label}");
        let third_input = sent[2].1["input"].as_array().expect("input");
        assert_eq!(third_input.len(), 3, "{label}");
        assert_eq!(
            third_input.last(),
            Some(
                &json!({ "role": "user", "content": [{ "type": "input_text", "text": "Now finish" }] })
            ),
            "{label}"
        );
        assert_eq!(
            fetch_calls.count(),
            usize::from(recovery_transport == "sse"),
            "{label}"
        );
        let failures = u64::from(recovery_transport == "sse");
        assert_stats(
            &session_id,
            &json!({
                "requests": 3,
                "connectionsCreated": 2,
                "connectionsReused": 1,
                "fullContextRequests": 2,
                "deltaRequests": 1,
                "websocketFailures": failures,
                "sseFallbacks": failures,
            }),
        );
    }
}
