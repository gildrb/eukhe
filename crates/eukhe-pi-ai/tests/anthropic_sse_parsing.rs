//! Port of `test/anthropic-sse-parsing.test.ts`.

mod anthropic_support;

use std::sync::{Arc, Mutex, PoisonError};

use anthropic_support::{
    collect, context, mock_fetch, model, requests, sse_body, sse_of, text_response_events,
    Captured, MockResponse,
};
use eukhe_pi_ai::api::anthropic_messages::{stream_anthropic, AnthropicOptions};
use eukhe_pi_ai::api::transform_messages::transform_messages;
use eukhe_pi_ai::compat::get_model;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, JsonValue, Message, Model, StopReason,
    TranscriptContext,
};
use serde_json::json;

#[tokio::test]
async fn forwards_parsed_provider_stream_events_in_order() {
    let model = model(&json!({ "id": "claude-haiku-4-5" }));
    let (fetch, _captured) = mock_fetch(MockResponse::sse(sse_of(&text_response_events("Hello"))));
    let seen: Arc<Mutex<Vec<(JsonValue, Model)>>> = Arc::default();
    let sink = Arc::clone(&seen);
    let mut options = AnthropicOptions::default();
    options.stream.request.api_key = Some("sk-test".into());
    options.stream.request.fetch = Some(fetch);
    options.stream.on_provider_stream_event = Some(Arc::new(move |event, event_model| {
        let sink = Arc::clone(&sink);
        let event = event.clone();
        let event_model = event_model.clone();
        Box::pin(async move {
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push((event, event_model));
            Ok(())
        })
    }));
    let context =
        context(&json!({ "messages": [{ "role": "user", "content": "Hello", "timestamp": 1 }] }));
    let (_, result) = collect(stream_anthropic(&model, &context, options)).await;

    assert_eq!(
        result.stop_reason,
        StopReason::Stop,
        "{:?}",
        result.error_message
    );
    let seen = seen.lock().unwrap_or_else(PoisonError::into_inner).clone();
    let types: Vec<&str> = seen
        .iter()
        .map(|(event, _)| event["type"].as_str().unwrap_or(""))
        .collect();
    assert_eq!(
        types,
        [
            "message_start",
            "content_block_start",
            "content_block_delta",
            "content_block_stop",
            "message_delta",
            "message_stop",
        ]
    );
    assert!(seen.iter().all(|(_, event_model)| *event_model == model));
}

fn get(provider: &str, id: &str) -> Model {
    get_model(provider, id).unwrap_or_else(|| panic!("{provider}/{id}"))
}

fn hello_context() -> TranscriptContext {
    context(&json!({ "messages": [{ "role": "user", "content": "Hello", "timestamp": 1 }] }))
}

/// TS `streamAnthropic(model, context, { client: createFakeAnthropicClient(response) })`.
fn fake_client_options(response: MockResponse) -> (AnthropicOptions, Captured) {
    let (fetch, captured) = mock_fetch(response);
    let mut options = AnthropicOptions::default();
    options.stream.request.api_key = Some("sk-test".into());
    options.stream.request.fetch = Some(fetch);
    (options, captured)
}

async fn run(model: &Model, context: &TranscriptContext, body: String) -> AssistantMessage {
    let (options, _) = fake_client_options(MockResponse::sse(body));
    collect(stream_anthropic(model, context, options)).await.1
}

/// TS `minimalAnthropicEvents`.
fn minimal_events() -> Vec<JsonValue> {
    text_response_events("Hello")
}

/// TS `createResponseModelSseResponse(model, contentBlock)`.
fn response_model_sse(model: &str, content_block: &JsonValue) -> String {
    sse_of(&[
        json!({ "type": "message_start", "message": { "id": "msg_response_model", "model": model, "usage": { "input_tokens": 100, "output_tokens": 0 } } }),
        json!({ "type": "content_block_start", "index": 0, "content_block": content_block }),
        json!({ "type": "content_block_stop", "index": 0 }),
        json!({ "type": "message_delta", "delta": { "stop_reason": "end_turn" }, "usage": { "input_tokens": 100, "output_tokens": 20 } }),
        json!({ "type": "message_stop" }),
    ])
}

fn to_json<T: serde::Serialize>(value: &T) -> JsonValue {
    serde_json::to_value(value).expect("json")
}

fn betas(captured: &Captured) -> Vec<String> {
    requests(captured)[0]
        .header("anthropic-beta")
        .map(|value| {
            value
                .split(',')
                .map(|beta| beta.trim().to_owned())
                .collect()
        })
        .unwrap_or_default()
}

#[tokio::test]
async fn keeps_signed_thinking_replayable_when_a_proxy_relabels_the_model() {
    // Regression test for earendil-works/pi#9188.
    let model = get("anthropic", "claude-opus-5");
    let response_model = "kimi-for-coding";
    let initial_context = hello_context();
    let first = run(
        &model,
        &initial_context,
        response_model_sse(
            response_model,
            &json!({ "type": "thinking", "thinking": "reasoning", "signature": "signature" }),
        ),
    )
    .await;

    assert_eq!(first.model, model.id);
    assert_eq!(first.response_model.as_deref(), Some(response_model));

    let mut messages = initial_context.messages().to_vec();
    messages.push(Message::Assistant(first));
    let transformed = transform_messages(&messages, &model, None);
    let replayed = transformed
        .iter()
        .find_map(|message| match message {
            Message::Assistant(assistant) => Some(assistant),
            _ => None,
        })
        .expect("assistant");
    assert_eq!(
        to_json(&replayed.content),
        json!([{ "type": "thinking", "thinking": "reasoning", "thinkingSignature": "signature" }])
    );
}

#[tokio::test]
async fn uses_a_returned_fallback_model_for_cost_attribution() {
    let fallback_model = "fallback-model";
    let mut value = to_json(&get("anthropic", "claude-opus-5"));
    value["compat"] = json!({
        "allowedFallbackModels": [{
            "provider": "anthropic",
            "model": fallback_model,
            "cost": { "input": 3, "output": 5, "cacheRead": 0, "cacheWrite": 0 },
        }],
    });
    let model: Model = serde_json::from_value(value).expect("model");
    let result = run(
        &model,
        &hello_context(),
        response_model_sse(fallback_model, &json!({ "type": "text", "text": "done" })),
    )
    .await;

    assert_eq!(result.model, model.id);
    assert_eq!(result.response_model.as_deref(), Some(fallback_model));
    assert!(
        (result.usage.cost.input - 0.0003).abs() < 5e-11,
        "{}",
        result.usage.cost.input
    );
    assert!(
        (result.usage.cost.output - 0.0001).abs() < 5e-11,
        "{}",
        result.usage.cost.output
    );
}

#[tokio::test]
async fn fails_safely_when_anthropic_falls_back_after_output_begins() {
    let model = get("anthropic", "claude-opus-5");
    let body = sse_of(&[
        json!({ "type": "message_start", "message": { "id": "msg_fallback", "model": "claude-opus-5", "usage": { "input_tokens": 1, "output_tokens": 0 } } }),
        json!({ "type": "content_block_start", "index": 0, "content_block": { "type": "text", "text": "partial" } }),
        json!({ "type": "content_block_stop", "index": 0 }),
        json!({ "type": "content_block_start", "index": 1, "content_block": { "type": "fallback", "from": { "model": "claude-opus-5" }, "to": { "model": "claude-opus-4-8" } } }),
    ]);
    let result = run(&model, &hello_context(), body).await;

    assert_eq!(result.stop_reason, StopReason::Error);
    assert!(
        result
            .error_message
            .as_deref()
            .unwrap_or("")
            .contains("unsupported mid-output model fallback"),
        "{:?}",
        result.error_message
    );
}

#[tokio::test]
async fn forces_streaming_after_an_on_payload_replacement() {
    let (mut options, captured) = fake_client_options(MockResponse::sse(sse_of(&minimal_events())));
    options.stream.request.on_payload = Some(Arc::new(|mut payload, _model| {
        payload["stream"] = json!(false);
        Box::pin(async move { Ok(Some(payload)) })
    }));
    let _ = collect(stream_anthropic(
        &get("anthropic", "claude-fable-5-1"),
        &hello_context(),
        options,
    ))
    .await;

    assert_eq!(requests(&captured)[0].body["stream"], json!(true));
}

#[tokio::test]
async fn omits_the_interleaved_thinking_beta_when_thinking_is_disabled() {
    let (mut options, captured) = fake_client_options(MockResponse::sse(sse_of(&minimal_events())));
    options.thinking_enabled = Some(false);
    let _ = collect(stream_anthropic(
        &get("openrouter", "anthropic/claude-haiku-4.5"),
        &hello_context(),
        options,
    ))
    .await;

    assert!(!betas(&captured).contains(&"interleaved-thinking-2025-05-14".to_owned()));
}

#[tokio::test]
async fn passes_managed_beta_features_to_injected_clients() {
    let (options, captured) = fake_client_options(MockResponse::sse(sse_of(&minimal_events())));
    let (_, result) = collect(stream_anthropic(
        &get("anthropic", "claude-fable-5-1"),
        &hello_context(),
        options,
    ))
    .await;

    assert_eq!(
        result.stop_reason,
        StopReason::Stop,
        "{:?}",
        result.error_message
    );
    let betas = betas(&captured);
    assert!(
        betas.contains(&"mid-conversation-output-config-2026-07-01".to_owned()),
        "{betas:?}"
    );
    assert!(
        betas.contains(&"thinking-binding-controls-2026-08-01".to_owned()),
        "{betas:?}"
    );
}

#[tokio::test]
async fn uses_the_serving_model_input_transformations_from_the_final_stream_event() {
    let mut events = minimal_events();
    events[0] = json!({
        "type": "message_start",
        "message": {
            "id": "msg_transformations",
            "model": "claude-fable-5-1",
            "usage": { "input_tokens": 12, "output_tokens": 0 },
            "input_transformations": [
                { "type": "thinking_dropped", "path": "messages.1.content.0", "reason": "prefix_binding_mismatch" },
            ],
        },
    });
    events[4]["input_transformations"] = json!([
        { "type": "thinking_dropped", "path": "messages.3.content.0", "reason": "model_binding_mismatch" },
    ]);
    let result = run(
        &get("anthropic", "claude-fable-5-1"),
        &hello_context(),
        sse_of(&events),
    )
    .await;

    let mut diagnostics = to_json(&result.diagnostics);
    for diagnostic in diagnostics.as_array_mut().expect("diagnostics") {
        assert!(diagnostic["timestamp"].is_number());
        diagnostic["timestamp"] = json!(0);
    }
    assert_eq!(
        diagnostics,
        json!([{
            "type": "anthropic_input_transformations",
            "timestamp": 0,
            "details": {
                "transformations": [{
                    "type": "thinking_dropped",
                    "path": "messages.3.content.0",
                    "reason": "model_binding_mismatch",
                }],
            },
        }])
    );
}

#[tokio::test]
async fn repairs_malformed_sse_json_and_malformed_streamed_tool_json() {
    let model = get("anthropic", "claude-haiku-4-5");
    let context = context(&json!({
        "messages": [{ "role": "user", "content": "Use the edit tool.", "timestamp": 1 }],
        "tools": [{
            "name": "edit",
            "description": "Edit a file.",
            "parameters": {
                "type": "object",
                "properties": { "path": { "type": "string" }, "text": { "type": "string" } },
                "required": ["path", "text"],
            },
        }],
    }));
    // TS String.raw: invalid `\H` escape and a literal tab inside the JSON string.
    let malformed_tool_json_delta = r#"{"type":"content_block_delta","index":0,"delta":{"type":"input_json_delta","partial_json":"{\"path\":\"A\H\",\"text\":\"col1<TAB>col2\"}"}}"#
        .replace("<TAB>", "\t");
    let usage = json!({ "input_tokens": 12, "output_tokens": 0, "cache_read_input_tokens": 0, "cache_creation_input_tokens": 0 });
    let body = sse_body(&[
        (
            "message_start",
            json!({ "type": "message_start", "message": { "id": "msg_test", "usage": usage } }),
        ),
        (
            "content_block_start",
            json!({ "type": "content_block_start", "index": 0, "content_block": { "type": "tool_use", "id": "toolu_test", "name": "edit", "input": {} } }),
        ),
        (
            "content_block_delta",
            JsonValue::String(malformed_tool_json_delta),
        ),
        (
            "content_block_stop",
            json!({ "type": "content_block_stop", "index": 0 }),
        ),
        (
            "message_delta",
            json!({ "type": "message_delta", "delta": { "stop_reason": "tool_use" }, "usage": { "input_tokens": 12, "output_tokens": 5, "cache_read_input_tokens": 0, "cache_creation_input_tokens": 0 } }),
        ),
        ("message_stop", json!({ "type": "message_stop" })),
    ]);
    let result = run(&model, &context, body).await;

    assert_eq!(
        result.stop_reason,
        StopReason::ToolUse,
        "{:?}",
        result.error_message
    );
    assert_eq!(result.error_message, None);
    let tool_call = result
        .content
        .iter()
        .find_map(|block| match block {
            AssistantContentBlock::ToolCall(call) => Some(call),
            _ => None,
        })
        .expect("tool call");
    assert_eq!(
        to_json(&tool_call.arguments),
        json!({ "path": "A\\H", "text": "col1\tcol2" })
    );
}

#[tokio::test]
async fn preserves_content_from_content_block_start_events() {
    let model = get("anthropic", "claude-haiku-4-5");
    let context = context(
        &json!({ "messages": [{ "role": "user", "content": "Say hello.", "timestamp": 1 }] }),
    );
    let body = sse_of(&[
        json!({ "type": "message_start", "message": { "id": "msg_initial_content", "usage": { "input_tokens": 12, "output_tokens": 0, "cache_read_input_tokens": 0, "cache_creation_input_tokens": 0 } } }),
        json!({ "type": "content_block_start", "index": 0, "content_block": { "type": "text", "text": "Initial text" } }),
        json!({ "type": "content_block_delta", "index": 0, "delta": { "type": "text_delta", "text": " plus delta" } }),
        json!({ "type": "content_block_stop", "index": 0 }),
        json!({ "type": "content_block_start", "index": 1, "content_block": { "type": "thinking", "thinking": "Initial thinking", "signature": "initial signature" } }),
        json!({ "type": "content_block_delta", "index": 1, "delta": { "type": "thinking_delta", "thinking": " plus delta" } }),
        json!({ "type": "content_block_delta", "index": 1, "delta": { "type": "signature_delta", "signature": " plus delta" } }),
        json!({ "type": "content_block_stop", "index": 1 }),
        json!({ "type": "message_delta", "delta": { "stop_reason": "end_turn" }, "usage": { "input_tokens": 12, "output_tokens": 5, "cache_read_input_tokens": 0, "cache_creation_input_tokens": 0 } }),
        json!({ "type": "message_stop" }),
    ]);
    let result = run(&model, &context, body).await;

    assert_eq!(
        to_json(&result.content),
        json!([
            { "type": "text", "text": "Initial text plus delta" },
            { "type": "thinking", "thinking": "Initial thinking plus delta", "thinkingSignature": "initial signature plus delta" },
        ])
    );
}

#[tokio::test]
async fn preserves_refusal_stop_details_from_message_delta() {
    let model = get("anthropic", "claude-fable-5");
    let context = context(
        &json!({ "messages": [{ "role": "user", "content": "blocked request", "timestamp": 1 }] }),
    );
    let explanation = "This request triggered restrictions on violative cyber content and was blocked under Anthropic's Usage Policy. To learn more, provide feedback, or request an exemption based on how you use Claude, visit our help center: https://support.claude.com/en/articles/14604842-real-time-cyber-safeguards-on-claude.";
    let usage = json!({ "input_tokens": 412, "output_tokens": 0, "cache_read_input_tokens": 0, "cache_creation_input_tokens": 0 });
    let body = sse_of(&[
        json!({ "type": "message_start", "message": { "id": "msg_01XFUDYJgAACzvnptvVoYEL", "usage": usage } }),
        json!({ "type": "message_delta", "delta": { "stop_reason": "refusal", "stop_details": { "type": "refusal", "category": "cyber", "explanation": explanation } }, "usage": usage }),
        json!({ "type": "message_stop" }),
    ]);
    let result = run(&model, &context, body).await;

    assert_eq!(result.stop_reason, StopReason::Error);
    assert_eq!(result.raw_stop_reason.as_deref(), Some("refusal"));
    assert_eq!(result.error_message.as_deref(), Some(explanation));
}

#[tokio::test]
async fn preserves_sensitive_stop_reasons_with_a_descriptive_error_message() {
    let model = get("anthropic", "claude-haiku-4-5");
    let context = context(
        &json!({ "messages": [{ "role": "user", "content": "blocked request", "timestamp": 1 }] }),
    );
    let usage = json!({ "input_tokens": 12, "output_tokens": 0, "cache_read_input_tokens": 0, "cache_creation_input_tokens": 0 });
    let body = sse_of(&[
        json!({ "type": "message_start", "message": { "id": "msg_sensitive", "usage": usage } }),
        json!({ "type": "message_delta", "delta": { "stop_reason": "sensitive" }, "usage": usage }),
        json!({ "type": "message_stop" }),
    ]);
    let result = run(&model, &context, body).await;

    assert_eq!(result.stop_reason, StopReason::Error);
    assert_eq!(result.raw_stop_reason.as_deref(), Some("sensitive"));
    assert_eq!(
        result.error_message.as_deref(),
        Some("Provider stopped with: sensitive")
    );
}

#[tokio::test]
async fn treats_message_delta_without_usage_as_a_no_op_for_usage_accumulation() {
    let model = get("anthropic", "claude-haiku-4-5");
    let context = context(
        &json!({ "messages": [{ "role": "user", "content": "Say hello.", "timestamp": 1 }] }),
    );
    let events: Vec<JsonValue> = minimal_events()
        .into_iter()
        .map(|event| {
            if event["type"] == "message_delta" {
                json!({ "type": "message_delta", "delta": { "stop_reason": "end_turn" } })
            } else {
                event
            }
        })
        .collect();
    let result = run(&model, &context, sse_of(&events)).await;

    assert_eq!(result.stop_reason, StopReason::Stop);
    assert_eq!(result.error_message, None);
    assert_eq!(
        to_json(&result.content),
        json!([{ "type": "text", "text": "Hello" }])
    );
    assert_eq!(result.usage.input, 12);
    assert_eq!(result.usage.total_tokens, 12);
}

#[tokio::test]
async fn ignores_unknown_sse_events_after_message_stop() {
    let model = get("anthropic", "claude-haiku-4-5");
    let context = context(
        &json!({ "messages": [{ "role": "user", "content": "Say hello.", "timestamp": 1 }] }),
    );
    let mut events: Vec<(&str, JsonValue)> = minimal_events()
        .into_iter()
        .map(|event| {
            let name = match event["type"].as_str().unwrap_or("") {
                "message_start" => "message_start",
                "content_block_start" => "content_block_start",
                "content_block_delta" => "content_block_delta",
                "content_block_stop" => "content_block_stop",
                "message_delta" => "message_delta",
                _ => "message_stop",
            };
            (name, event)
        })
        .collect();
    events.push(("done", JsonValue::String("[DONE]".into())));
    events.push(("proxy.stats", JsonValue::String("not json".into())));
    let result = run(&model, &context, sse_body(&events)).await;

    assert_eq!(result.stop_reason, StopReason::Stop);
    assert_eq!(result.error_message, None);
    assert_eq!(
        to_json(&result.content),
        json!([{ "type": "text", "text": "Hello" }])
    );
}
