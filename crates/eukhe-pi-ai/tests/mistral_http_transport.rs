//! Port of `test/mistral-http-transport.test.ts`.

mod mistral_support;

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::AbortController;
use eukhe_pi_ai::api::mistral_conversations::stream as stream_mistral;
use eukhe_pi_ai::compat::get_model;
use eukhe_pi_ai::types::{OnProviderStreamEvent, OnResponse, ProviderStreamOptions};
use eukhe_pi_ai::utils::pi_user_agent::get_pi_user_agent;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{
    Context, JsonObject, JsonValue, Model, ProviderHeaders, ProviderResponse, StopReason,
};
use mistral_support::{
    capture_payload, captured, create_sse_response, create_terminal_event, mock_fetch, payload_of,
    MockResponse,
};
use serde_json::json;

fn mistral_model(id: &str) -> Model {
    get_model("mistral", id).expect("model")
}

fn context(value: JsonValue) -> eukhe_types::pi_ai::TranscriptContext {
    normalize_context(serde_json::from_value::<Context>(value).expect("context"))
}

fn hello_context() -> eukhe_types::pi_ai::TranscriptContext {
    context(json!({ "messages": [{ "role": "user", "content": "hello", "timestamp": 1 }] }))
}

fn extra(value: JsonValue) -> JsonObject {
    match value {
        JsonValue::Object(object) => object,
        _ => unreachable!("extra options are an object"),
    }
}

fn options(api_key: &str, fetch: eukhe_pi_ai::types::FetchFunction) -> ProviderStreamOptions {
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some(api_key.to_owned());
    options.stream.request.fetch = Some(fetch);
    options
}

fn header<'a>(headers: &'a reqwest::header::HeaderMap, name: &str) -> Option<&'a str> {
    headers.get(name).and_then(|value| value.to_str().ok())
}

#[tokio::test]
#[allow(clippy::too_many_lines)] // One TS test case with its full fixture and assertions.
async fn serializes_sdk_style_payloads_to_the_mistral_wire_format() {
    let model = mistral_model("mistral-large-latest");
    let context = context(json!({
        "systemPrompt": "Be precise",
        "messages": [{
            "role": "user",
            "content": [
                { "type": "text", "text": "describe" },
                { "type": "image", "data": "aGVsbG8=", "mimeType": "image/png" },
            ],
            "timestamp": 1,
        }],
        "tools": [{
            "name": "lookup",
            "description": "Look something up",
            "parameters": {
                "type": "object",
                "properties": { "query": { "type": "string" } },
                "required": ["query"],
            },
        }],
    }));
    let (fetch, capture) = mock_fetch(create_sse_response(
        &[create_terminal_event("stop")],
        &[("x-request-id", "request-1")],
    ))
    .await;
    let (on_payload, payload_store) = capture_payload(|payload| {
        let mut next = payload.as_object().cloned().expect("payload object");
        for (key, value) in extra(json!({
            "topP": 0.9,
            "randomSeed": 42,
            "responseFormat": {
                "type": "json_schema",
                "jsonSchema": {
                    "name": "result",
                    "schemaDefinition": {
                        "type": "object",
                        "properties": { "maxTokens": { "type": "number" } },
                    },
                },
            },
            "presencePenalty": 0.1,
            "frequencyPenalty": 0.2,
            "parallelToolCalls": true,
            "safePrompt": true,
        })) {
            next.insert(key, value);
        }
        Some(JsonValue::Object(next))
    });
    let response_store: Arc<Mutex<Option<ProviderResponse>>> = Arc::new(Mutex::new(None));
    let response_sink = Arc::clone(&response_store);
    let on_response: OnResponse<Model> = Arc::new(move |response, _model| {
        *response_sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(response);
        Box::pin(async { Ok(()) })
    });

    let mut options = options("secret", fetch);
    let mut headers = ProviderHeaders::new();
    headers.insert("x-custom".into(), Some("value".into()));
    options.stream.request.headers = Some(headers);
    options.stream.max_tokens = Some(123);
    options.stream.session_id = Some("session-1".into());
    options.stream.request.on_payload = Some(on_payload);
    options.stream.request.on_response = Some(on_response);
    options.extra = extra(json!({
        "promptMode": "reasoning",
        "reasoningEffort": "high",
        "toolChoice": { "type": "function", "function": { "name": "lookup" } },
    }));

    let message = stream_mistral(&model, &context, options).result().await;

    assert_eq!(message.stop_reason, StopReason::Stop);
    let request = captured(&capture);
    assert_eq!(request.url, "https://api.mistral.ai/v1/chat/completions");
    assert_eq!(
        header(&request.headers, "authorization"),
        Some("Bearer secret")
    );
    assert_eq!(
        header(&request.headers, "accept"),
        Some("text/event-stream")
    );
    assert_eq!(header(&request.headers, "x-affinity"), Some("session-1"));
    assert_eq!(header(&request.headers, "x-custom"), Some("value"));
    assert_eq!(
        header(&request.headers, "user-agent"),
        Some(get_pi_user_agent())
    );
    let callback_payload = payload_of(&payload_store);
    assert_eq!(callback_payload["maxTokens"], json!(123));
    assert_eq!(callback_payload["promptMode"], json!("reasoning"));
    assert_eq!(callback_payload["promptCacheKey"], json!("session-1"));
    let callback_response = response_store
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("onResponse called");
    assert_eq!(
        serde_json::to_value(callback_response).expect("serialize"),
        json!({
            "status": 200,
            "headers": { "content-type": "text/event-stream", "x-request-id": "request-1" },
        })
    );

    let wire_payload: JsonValue = serde_json::from_str(&request.body).expect("wire payload");
    assert_eq!(wire_payload["max_tokens"], json!(123));
    assert_eq!(wire_payload["prompt_mode"], json!("reasoning"));
    assert_eq!(wire_payload["reasoning_effort"], json!("high"));
    assert_eq!(
        wire_payload["tool_choice"],
        json!({ "type": "function", "function": { "name": "lookup" } })
    );
    assert_eq!(wire_payload["prompt_cache_key"], json!("session-1"));
    assert_eq!(wire_payload["top_p"], json!(0.9));
    assert_eq!(wire_payload["random_seed"], json!(42));
    assert_eq!(wire_payload["presence_penalty"], json!(0.1));
    assert_eq!(wire_payload["frequency_penalty"], json!(0.2));
    assert_eq!(wire_payload["parallel_tool_calls"], json!(true));
    assert_eq!(wire_payload["safe_prompt"], json!(true));
    assert_eq!(
        wire_payload["response_format"],
        json!({
            "type": "json_schema",
            "json_schema": {
                "name": "result",
                "schema": {
                    "type": "object",
                    "properties": { "maxTokens": { "type": "number" } },
                },
            },
        })
    );
    for key in ["maxTokens", "promptMode", "promptCacheKey"] {
        assert!(
            wire_payload.get(key).is_none(),
            "{key} must not be on the wire"
        );
    }
    assert_eq!(
        wire_payload["messages"],
        json!([
            { "role": "system", "content": "Be precise" },
            {
                "role": "user",
                "content": [
                    { "type": "text", "text": "describe" },
                    { "type": "image_url", "image_url": "data:image/png;base64,aGVsbG8=" },
                ],
            },
        ])
    );
}

#[tokio::test]
async fn serializes_assistant_thinking_tool_calls_and_tool_results_for_replay() {
    let model = mistral_model("mistral-large-latest");
    let context = context(json!({
        "messages": [
            {
                "role": "assistant",
                "api": "mistral-conversations",
                "provider": "mistral",
                "model": model.id,
                "content": [
                    { "type": "thinking", "thinking": "reason" },
                    { "type": "text", "text": "answer" },
                    { "type": "toolCall", "id": "abc123456", "name": "lookup", "arguments": { "query": "pi" } },
                ],
                "usage": {
                    "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                    "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
                },
                "stopReason": "toolUse",
                "timestamp": 1,
            },
            {
                "role": "toolResult",
                "toolCallId": "abc123456",
                "toolName": "lookup",
                "content": [
                    { "type": "text", "text": "found" },
                    { "type": "image", "data": "aGVsbG8=", "mimeType": "image/png" },
                ],
                "isError": false,
                "timestamp": 2,
            },
        ],
    }));
    let (fetch, capture) =
        mock_fetch(create_sse_response(&[create_terminal_event("stop")], &[])).await;

    let message = stream_mistral(&model, &context, options("test", fetch))
        .result()
        .await;

    assert_eq!(message.stop_reason, StopReason::Stop);
    let wire_payload: JsonValue = serde_json::from_str(&captured(&capture).body).expect("wire");
    assert_eq!(
        wire_payload["messages"],
        json!([
            {
                "role": "assistant",
                "prefix": false,
                "content": [
                    { "type": "thinking", "thinking": [{ "type": "text", "text": "reason" }] },
                    { "type": "text", "text": "answer" },
                ],
                "tool_calls": [{
                    "id": "abc123456",
                    "type": "function",
                    "function": { "name": "lookup", "arguments": "{\"query\":\"pi\"}" },
                    "index": 0,
                }],
            },
            {
                "role": "tool",
                "tool_call_id": "abc123456",
                "name": "lookup",
                "content": [
                    { "type": "text", "text": "found" },
                    { "type": "image_url", "image_url": "data:image/png;base64,aGVsbG8=" },
                ],
            },
        ])
    );
}

#[tokio::test]
async fn parses_native_thinking_text_fragmented_tool_calls_and_cached_token_usage() {
    let model = mistral_model("mistral-large-latest");
    let events = [
        json!({
            "id": "response-1", "model": model.id,
            "choices": [{ "index": 0, "finish_reason": null,
                "delta": { "content": [{ "type": "thinking", "thinking": [{ "type": "text", "text": "reason" }] }] } }],
        }),
        json!({
            "id": "response-1", "model": model.id,
            "choices": [{ "index": 0, "finish_reason": null,
                "delta": { "content": [{ "type": "text", "text": "answer" }] } }],
        }),
        json!({
            "id": "response-1", "model": model.id,
            "choices": [{ "index": 0, "finish_reason": null, "delta": {
                "tool_calls": [{ "id": "abc123456", "index": 0,
                    "function": { "name": "lookup", "arguments": "{\"query\":" } }],
            } }],
        }),
        json!({
            "id": "response-1", "model": model.id,
            "choices": [{ "index": 0, "finish_reason": "tool_calls", "delta": {
                "tool_calls": [{ "index": 0, "function": { "name": "", "arguments": "\"pi\"}" } }],
            } }],
            "usage": {
                "prompt_tokens": 10, "completion_tokens": 4, "total_tokens": 14,
                "prompt_tokens_details": { "cached_tokens": 3 },
            },
        }),
    ];
    let (fetch, _) = mock_fetch(create_sse_response(&events, &[])).await;

    let message = stream_mistral(&model, &hello_context(), options("test", fetch))
        .result()
        .await;

    assert_eq!(message.stop_reason, StopReason::ToolUse);
    assert_eq!(message.raw_stop_reason.as_deref(), Some("tool_calls"));
    assert_eq!(message.response_id.as_deref(), Some("response-1"));
    assert_eq!(
        serde_json::to_value(&message.content).expect("content"),
        json!([
            { "type": "thinking", "thinking": "reason" },
            { "type": "text", "text": "answer" },
            { "type": "toolCall", "id": "abc123456", "name": "lookup", "arguments": { "query": "pi" } },
        ])
    );
    assert_eq!(
        (
            message.usage.input,
            message.usage.output,
            message.usage.cache_read,
            message.usage.cache_write,
            message.usage.total_tokens,
        ),
        (7, 4, 3, 0, 14)
    );
}

/// #9674: GLM models on Mistral send empty content deltas at the start,
/// around tool calls, and sometimes mid-thinking. They must not open blocks
/// or split thinking.
#[tokio::test]
async fn ignores_empty_content_deltas() {
    let model = mistral_model("zai-glm-5-3");
    let thinking =
        |text: &str| json!({ "type": "thinking", "thinking": [{ "type": "text", "text": text }] });
    let tool_call = |args: &str, first: bool| {
        let mut call = json!({ "index": 0, "function": { "name": if first { "read" } else { "" }, "arguments": args } });
        if first {
            call["id"] = json!("abc123456");
        }
        call
    };
    let deltas = [
        json!({ "content": "" }),
        json!({ "content": [thinking("first part,")] }),
        json!({ "content": "" }),
        json!({ "content": [{ "type": "text", "text": "" }] }),
        json!({ "content": [thinking(" second part."), { "type": "text", "text": "Reading." }] }),
        json!({ "content": "", "tool_calls": [tool_call("", true)] }),
        json!({ "content": "", "tool_calls": [tool_call("{\"path\":", false)] }),
        json!({ "content": "", "tool_calls": [tool_call("\"a.txt\"}", false)] }),
        json!({ "content": "" }),
    ];
    let last = deltas.len() - 1;
    let events: Vec<JsonValue> = deltas
        .into_iter()
        .enumerate()
        .map(|(i, delta)| {
            json!({
                "id": "response-1",
                "model": model.id,
                "choices": [{ "index": 0, "finish_reason": if i == last { json!("tool_calls") } else { JsonValue::Null }, "delta": delta }],
            })
        })
        .collect();
    let (fetch, _) = mock_fetch(create_sse_response(&events, &[])).await;

    let message = stream_mistral(&model, &hello_context(), options("test", fetch))
        .result()
        .await;

    assert_eq!(
        serde_json::to_value(&message.content).expect("content"),
        json!([
            { "type": "thinking", "thinking": "first part, second part." },
            { "type": "text", "text": "Reading." },
            { "type": "toolCall", "id": "abc123456", "name": "read", "arguments": { "path": "a.txt" } },
        ])
    );
}

#[tokio::test]
async fn forwards_each_parsed_sse_payload_before_normalizing_it() {
    let model = mistral_model("mistral-large-latest");
    let events = [
        json!({
            "id": "response-1",
            "provider_metadata": { "request": "test" },
            "choices": [{ "index": 0, "finish_reason": null, "delta": { "content": "hello" } }],
        }),
        json!({
            "id": "response-1",
            "choices": [{ "index": 0, "finish_reason": "stop", "delta": {} }],
            "usage": { "prompt_tokens": 1, "completion_tokens": 1, "total_tokens": 2 },
        }),
    ];
    let (fetch, _) = mock_fetch(create_sse_response(&events, &[])).await;
    let received: Arc<Mutex<Vec<(JsonValue, Model)>>> = Arc::new(Mutex::new(Vec::new()));
    let sink = Arc::clone(&received);
    let on_event: OnProviderStreamEvent = Arc::new(move |event, event_model| {
        let sink = Arc::clone(&sink);
        let entry = (event.clone(), event_model.clone());
        Box::pin(async move {
            tokio::task::yield_now().await;
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(entry);
            Ok(())
        })
    });
    let mut options = options("test", fetch);
    options.stream.on_provider_stream_event = Some(on_event);

    let result = stream_mistral(&model, &hello_context(), options)
        .result()
        .await;

    let received = received
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(
        received
            .iter()
            .map(|(event, _)| event.clone())
            .collect::<Vec<_>>(),
        events.to_vec()
    );
    assert_eq!(
        received
            .iter()
            .map(|(_, model)| model.clone())
            .collect::<Vec<_>>(),
        vec![model.clone(), model]
    );
    assert_eq!(result.stop_reason, StopReason::Stop);
    assert_eq!(
        serde_json::to_value(&result.content).expect("content"),
        json!([{ "type": "text", "text": "hello" }])
    );
}

#[tokio::test]
async fn parses_sse_and_utf8_sequences_split_across_transport_chunks() {
    let model = mistral_model("mistral-large-latest");
    let event = json!({
        "id": "response-bytewise",
        "model": model.id,
        "choices": [{ "index": 0, "finish_reason": "stop", "delta": { "content": "héllo 🌍" } }],
        "usage": { "prompt_tokens": 1, "completion_tokens": 2, "total_tokens": 3 },
    });
    let bytes = format!("data: {event}\r\n\r\ndata: [DONE]\r\n\r\n").into_bytes();
    let mut response = MockResponse::sse(String::new(), &[]);
    response.chunks = bytes.into_iter().map(|byte| vec![byte]).collect();
    let (fetch, _) = mock_fetch(response).await;

    let message = stream_mistral(&model, &hello_context(), options("test", fetch))
        .result()
        .await;

    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(
        serde_json::to_value(&message.content).expect("content"),
        json!([{ "type": "text", "text": "héllo 🌍" }])
    );
}

#[tokio::test]
async fn honors_case_insensitive_header_overrides_and_explicit_affinity_suppression() {
    let mut model = mistral_model("mistral-large-latest");
    let mut model_headers = eukhe_types::pi_ai::IndexMap::new();
    model_headers.insert("Authorization".to_owned(), "Bearer model-key".to_owned());
    model_headers.insert("X-Affinity".to_owned(), "model-affinity".to_owned());
    model.headers = Some(model_headers);
    let (fetch, capture) =
        mock_fetch(create_sse_response(&[create_terminal_event("stop")], &[])).await;
    let mut options = options("request-key", fetch);
    options.stream.session_id = Some("automatic-affinity".into());
    let mut headers = ProviderHeaders::new();
    headers.insert("authorization".into(), None);
    headers.insert("x-affinity".into(), None);
    headers.insert("User-Agent".into(), Some("custom-agent".into()));
    options.stream.request.headers = Some(headers);

    let _ = stream_mistral(&model, &hello_context(), options)
        .result()
        .await;

    let request = captured(&capture);
    assert!(!request.headers.contains_key("authorization"));
    assert!(!request.headers.contains_key("x-affinity"));
    assert_eq!(header(&request.headers, "user-agent"), Some("custom-agent"));
}

fn hanging_response() -> MockResponse {
    let mut response = MockResponse::sse(String::new(), &[]);
    response.chunks.clear();
    response.hang = true;
    response
}

#[tokio::test]
async fn aborts_while_waiting_for_an_sse_chunk() {
    let model = mistral_model("mistral-large-latest");
    let controller = AbortController::new();
    let (fetch, _) = mock_fetch(hanging_response()).await;
    let mut options = options("test", fetch);
    options.stream.request.signal = Some(controller.signal());

    let stream = stream_mistral(&model, &hello_context(), options);
    let mut events = stream.events();
    // Abort once the request is in flight and streaming (`start` arrived).
    let first = futures::StreamExt::next(&mut events)
        .await
        .expect("start event");
    assert_eq!(first.type_name(), "start");
    controller.abort(None);
    let message = stream.result().await;

    assert_eq!(message.stop_reason, StopReason::Aborted);
}

#[tokio::test(start_paused = true)]
async fn applies_the_request_timeout_while_waiting_for_response_headers() {
    let model = mistral_model("mistral-large-latest");
    let fetch: eukhe_pi_ai::types::FetchFunction =
        Arc::new(|_request| Box::pin(std::future::pending()));
    let mut options = options("test", fetch);
    options.stream.request.timeout_ms = Some(5.0);

    let message = stream_mistral(&model, &hello_context(), options)
        .result()
        .await;

    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(
        message.error_message.as_deref(),
        Some("Mistral response headers timed out after 5ms")
    );
}

/// Regression test for #10609: an active stream must not be cut off after `timeoutMs`.
#[tokio::test(start_paused = true)]
async fn does_not_abort_an_active_stream_that_lasts_longer_than_the_request_timeout() {
    let model = mistral_model("mistral-large-latest");
    let thinking_event = json!({
        "choices": [{ "index": 0, "delta": { "content": [
            { "type": "thinking", "thinking": [{ "type": "text", "text": "x" }] },
        ] } }],
    });
    let fetch: eukhe_pi_ai::types::FetchFunction = Arc::new(move |_request| {
        let thinking = format!("data: {thinking_event}\n\n");
        Box::pin(async move {
            let terminal = format!(
                "data: {}\n\ndata: [DONE]\n\n",
                create_terminal_event("stop")
            );
            let chunks = futures::stream::unfold(0, move |index| {
                let thinking = thinking.clone();
                let terminal = terminal.clone();
                async move {
                    match index {
                        0..5 => {
                            if index > 0 {
                                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                            }
                            Some((Ok::<_, std::io::Error>(thinking.into_bytes()), index + 1))
                        }
                        5 => {
                            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
                            Some((Ok(terminal.into_bytes()), index + 1))
                        }
                        _ => None,
                    }
                }
            });
            let response = http::Response::builder()
                .status(200)
                .header("content-type", "text/event-stream")
                .body(reqwest::Body::wrap_stream(chunks))
                .expect("response");
            Ok(reqwest::Response::from(response))
        })
    });
    let mut options = options("test", fetch);
    options.stream.request.timeout_ms = Some(20.0);

    let message = stream_mistral(&model, &hello_context(), options)
        .result()
        .await;

    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(
        serde_json::to_value(&message.content).expect("content"),
        json!([{ "type": "thinking", "thinking": "xxxxx" }])
    );
}

#[tokio::test]
async fn preserves_http_status_and_response_bodies_in_errors() {
    let model = mistral_model("mistral-large-latest");
    let response = MockResponse {
        status: 403,
        reason: "Forbidden",
        headers: vec![("content-type".into(), "text/plain;charset=UTF-8".into())],
        chunks: vec![br#"{"message":"blocked by gateway"}"#.to_vec()],
        hang: false,
    };
    let (fetch, _) = mock_fetch(response).await;

    let message = stream_mistral(&model, &hello_context(), options("test", fetch))
        .result()
        .await;

    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(
        message.error_message.as_deref(),
        Some(r#"Mistral API error (403): {"message":"blocked by gateway"}"#)
    );
}
