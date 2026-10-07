//! Port of `test/openai-responses-terminal-event.test.ts`.
//!
//! TS mocks the `openai` SDK for the wrapper-stream cases; here the same
//! events are served through the `fetch` option.

mod openai_responses_support;

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::api::openai_responses::stream as stream_openai_responses;
use eukhe_pi_ai::api::openai_responses_shared::{
    process_responses_stream, OpenAIResponsesStreamOptions,
};
use eukhe_pi_ai::types::{JsonValue, OnProviderStreamEvent, ProviderStreamOptions};
use eukhe_pi_ai::utils::diagnostics::Thrown;
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{AssistantMessage, AssistantMessageEvent, Context, Model, StopReason};
use futures::StreamExt;
use openai_responses_support::{collect, mock_fetch, sse_events, MockResponse};
use serde_json::json;

fn create_model() -> Model {
    serde_json::from_value(json!({
        "id": "gpt-5-mini",
        "name": "GPT-5 Mini",
        "api": "openai-responses",
        "provider": "openai",
        "baseUrl": "https://api.openai.com/v1",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 400_000,
        "maxTokens": 128_000,
    }))
    .expect("model")
}

fn create_output(model: &Model) -> AssistantMessage {
    serde_json::from_value(json!({
        "role": "assistant",
        "content": [],
        "api": model.api,
        "provider": model.provider,
        "model": model.id,
        "usage": {
            "input": 0,
            "output": 0,
            "cacheRead": 0,
            "cacheWrite": 0,
            "totalTokens": 0,
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
        },
        "stopReason": "pending",
        "timestamp": 0,
    }))
    .expect("output")
}

fn wrapper_mock_events() -> Vec<JsonValue> {
    vec![
        json!({ "type": "response.created", "sequence_number": 0, "response": { "id": "resp_wrapper_early_eof" } }),
        json!({
            "type": "response.output_item.added",
            "sequence_number": 1,
            "output_index": 0,
            "item": { "type": "reasoning", "id": "rs_wrapper_early_eof", "summary": [] },
        }),
        json!({
            "type": "response.reasoning_text.delta",
            "sequence_number": 2,
            "output_index": 0,
            "content_index": 0,
            "item_id": "rs_wrapper_early_eof",
            "delta": "partial reasoning before the wrapper stream ends",
        }),
    ]
}

fn create_early_eof_events() -> Vec<JsonValue> {
    vec![
        json!({ "type": "response.created", "sequence_number": 0, "response": { "id": "resp_early_eof" } }),
        json!({
            "type": "response.output_item.added",
            "sequence_number": 1,
            "output_index": 0,
            "item": { "type": "reasoning", "id": "rs_early_eof", "summary": [] },
        }),
        json!({
            "type": "response.reasoning_text.delta",
            "sequence_number": 2,
            "output_index": 0,
            "content_index": 0,
            "item_id": "rs_early_eof",
            "delta": "partial reasoning before the stream ends",
        }),
    ]
}

fn create_completed_events() -> Vec<JsonValue> {
    vec![json!({
        "type": "response.completed",
        "sequence_number": 0,
        "response": {
            "id": "resp_completed",
            "status": "completed",
            "usage": {
                "input_tokens": 20,
                "output_tokens": 7,
                "total_tokens": 27,
                "input_tokens_details": { "cached_tokens": 2, "cache_write_tokens": 3 },
            },
        },
    })]
}

fn create_incomplete_events(reason: &str) -> Vec<JsonValue> {
    vec![json!({
        "type": "response.incomplete",
        "sequence_number": 0,
        "response": {
            "id": "resp_incomplete",
            "status": "incomplete",
            "incomplete_details": { "reason": reason },
            "usage": {
                "input_tokens": 30,
                "output_tokens": 12,
                "total_tokens": 42,
                "input_tokens_details": { "cached_tokens": 5 },
            },
        },
    })]
}

fn create_failed_events() -> Vec<JsonValue> {
    vec![json!({
        "type": "response.failed",
        "sequence_number": 0,
        "response": {
            "id": "resp_failed",
            "status": "failed",
            "error": { "code": "server_error", "message": "boom" },
        },
    })]
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TerminalStatus {
    Completed,
    Incomplete,
}

fn create_phased_message_events(
    phases: [&str; 2],
    terminal_status: TerminalStatus,
) -> Vec<JsonValue> {
    let mut events = vec![
        json!({
            "type": "response.output_item.added",
            "sequence_number": 0,
            "output_index": 0,
            "item": {
                "type": "message",
                "id": "msg_phase",
                "role": "assistant",
                "status": "in_progress",
                "content": [],
                "phase": phases[0],
            },
        }),
        json!({
            "type": "response.output_item.done",
            "sequence_number": 1,
            "output_index": 0,
            "item": {
                "type": "message",
                "id": "msg_phase",
                "role": "assistant",
                "status": "completed",
                "content": [{ "type": "output_text", "text": "answer", "annotations": [] }],
                "phase": phases[1],
            },
        }),
    ];
    events.push(match terminal_status {
        TerminalStatus::Incomplete => json!({
            "type": "response.incomplete",
            "sequence_number": 2,
            "response": {
                "id": "resp_phase",
                "status": "incomplete",
                "incomplete_details": { "reason": "max_output_tokens" },
            },
        }),
        TerminalStatus::Completed => json!({
            "type": "response.completed",
            "sequence_number": 2,
            "response": { "id": "resp_phase", "status": "completed" },
        }),
    });
    events
}

fn create_unfinished_tool_call_events() -> Vec<JsonValue> {
    vec![
        json!({
            "type": "response.output_item.added",
            "sequence_number": 0,
            "output_index": 0,
            "item": { "type": "function_call", "id": "fc_1", "call_id": "call_1", "name": "bash", "arguments": "" },
        }),
        json!({
            "type": "response.function_call_arguments.delta",
            "sequence_number": 1,
            "output_index": 0,
            "item_id": "fc_1",
            "delta": "{\"command\":\"rm -rf /tmp/build",
        }),
        json!({
            "type": "response.completed",
            "sequence_number": 2,
            "response": { "id": "resp_unfinished", "status": "completed" },
        }),
    ]
}

/// llama.cpp omits `output_index` from every event and sends both done
/// events after all deltas.
fn create_tool_calls_without_output_index_events() -> Vec<JsonValue> {
    let call = |n: &str, arguments: &str| json!({ "type": "function_call", "id": format!("fc_{n}"), "call_id": format!("call_{n}"), "name": "bash", "arguments": arguments });
    vec![
        json!({ "type": "response.output_item.added", "item": call("a", "") }),
        json!({ "type": "response.function_call_arguments.delta", "item_id": "fc_a", "delta": "{\"command\":\"echo a\"}" }),
        json!({ "type": "response.output_item.added", "item": call("b", "") }),
        json!({ "type": "response.function_call_arguments.delta", "item_id": "fc_b", "delta": "{\"command\":\"echo b\"}" }),
        json!({ "type": "response.output_item.done", "item": call("a", "{\"command\":\"echo a\"}") }),
        json!({ "type": "response.output_item.done", "item": call("b", "{\"command\":\"echo b\"}") }),
        json!({ "type": "response.completed", "response": { "id": "resp_no_output_index", "status": "completed" } }),
    ]
}

/// TS `processResponsesStream(events, output, stream, model)`.
async fn process(
    events: Vec<JsonValue>,
    output: &mut AssistantMessage,
    stream: &AssistantMessageEventStream,
    model: &Model,
) -> Result<(), Thrown> {
    process_responses_stream(
        futures::stream::iter(events.into_iter().map(Ok)),
        output,
        stream,
        model,
        &OpenAIResponsesStreamOptions::default(),
    )
    .await
}

/// The `partial.stopReason` of every pushed event carrying a `partial`
/// (TS wraps `stream.push`).
async fn observed_stop_reasons(stream: &AssistantMessageEventStream) -> Vec<StopReason> {
    stream.end(None);
    let events: Vec<AssistantMessageEvent> = stream.events().collect().await;
    events
        .iter()
        .filter_map(|event| match event {
            AssistantMessageEvent::Start { partial }
            | AssistantMessageEvent::TextStart { partial, .. }
            | AssistantMessageEvent::TextDelta { partial, .. }
            | AssistantMessageEvent::TextEnd { partial, .. }
            | AssistantMessageEvent::ThinkingStart { partial, .. }
            | AssistantMessageEvent::ThinkingDelta { partial, .. }
            | AssistantMessageEvent::ThinkingEnd { partial, .. }
            | AssistantMessageEvent::ToolCallStart { partial, .. }
            | AssistantMessageEvent::ToolCallDelta { partial, .. }
            | AssistantMessageEvent::ToolCallEnd { partial, .. } => Some(partial.stop_reason),
            AssistantMessageEvent::Done { .. } | AssistantMessageEvent::Error { .. } => None,
        })
        .collect()
}

fn hi_context() -> eukhe_pi_ai::types::TranscriptContext {
    normalize_context(
        serde_json::from_value::<Context>(json!({
            "systemPrompt": "",
            "messages": [{ "role": "user", "content": [{ "type": "text", "text": "hi" }], "timestamp": 0 }],
            "tools": [],
        }))
        .expect("context"),
    )
}

fn wrapper_options() -> ProviderStreamOptions {
    let (fetch, _) = mock_fetch(vec![MockResponse::sse(sse_events(&wrapper_mock_events()))]);
    let mut options = ProviderStreamOptions::default();
    options.stream.request.api_key = Some("test".into());
    options.stream.request.fetch = Some(fetch);
    options
}

#[tokio::test]
async fn rejects_streams_that_end_before_a_terminal_response_event() {
    let model = create_model();
    let mut output = create_output(&model);
    let stream = AssistantMessageEventStream::new();

    let error = process(create_early_eof_events(), &mut output, &stream, &model)
        .await
        .expect_err("rejects");
    assert!(error
        .to_string()
        .contains("OpenAI Responses stream ended before a terminal response event"));
}

#[tokio::test]
async fn rejects_completed_streams_whose_tool_call_never_received_output_item_done() {
    let model = create_model();

    let error = process(
        create_unfinished_tool_call_events(),
        &mut create_output(&model),
        &AssistantMessageEventStream::new(),
        &model,
    )
    .await
    .expect_err("rejects");
    assert!(error.to_string().contains(
        "OpenAI Responses stream completed with an unfinished tool call: bash (call_1|fc_1)"
    ));
}

// https://github.com/earendil-works/pi/issues/9974
#[tokio::test]
async fn rejects_parallel_tool_calls_without_output_index_instead_of_running_mixed_up_calls() {
    let model = create_model();

    let error = process(
        create_tool_calls_without_output_index_events(),
        &mut create_output(&model),
        &AssistantMessageEventStream::new(),
        &model,
    )
    .await
    .expect_err("rejects");
    assert!(error.to_string().contains(
        "OpenAI Responses stream completed with an unfinished tool call: bash (call_a|fc_a)"
    ));
}

#[tokio::test]
async fn forwards_parsed_provider_stream_events_in_order() {
    let model = create_model();
    let context = hi_context();
    let observed: Arc<Mutex<Vec<(JsonValue, Model)>>> = Arc::default();
    let sink = Arc::clone(&observed);
    let on_provider_stream_event: OnProviderStreamEvent = Arc::new(move |event, event_model| {
        let sink = Arc::clone(&sink);
        Box::pin(async move {
            tokio::task::yield_now().await;
            sink.lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push((event.clone(), event_model.clone()));
            Ok(())
        })
    });
    let mut options = wrapper_options();
    options.stream.on_provider_stream_event = Some(on_provider_stream_event);
    let stream = stream_openai_responses(&model, &context, options);

    stream.result().await;

    let observed = observed
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(observed.len(), 3);
    let types: Vec<&str> = observed
        .iter()
        .map(|(event, _)| event["type"].as_str().expect("type"))
        .collect();
    assert_eq!(
        types,
        [
            "response.created",
            "response.output_item.added",
            "response.reasoning_text.delta"
        ]
    );
    let models: Vec<Model> = observed.into_iter().map(|(_, model)| model).collect();
    assert_eq!(models, [model.clone(), model.clone(), model]);
}

#[tokio::test]
async fn emits_an_error_final_result_when_the_wrapper_stream_ends_before_a_terminal_response_event()
{
    let model = create_model();
    let context = hi_context();
    let stream = stream_openai_responses(&model, &context, wrapper_options());

    let (events, result) = collect(stream).await;
    let initial_stop_reason = events.iter().find_map(|event| match event {
        AssistantMessageEvent::Start { partial } => Some(partial.stop_reason),
        _ => None,
    });

    assert_eq!(initial_stop_reason, Some(StopReason::Pending));
    assert_eq!(
        events.last().map(AssistantMessageEvent::type_name),
        Some("error")
    );
    assert_eq!(result.stop_reason, StopReason::Error);
    assert_eq!(
        result.error_message.as_deref(),
        Some("OpenAI Responses stream ended before a terminal response event")
    );
}

async fn tracks_message_phases(phases: [&str; 2], expected: [StopReason; 2]) {
    let model = create_model();
    let mut output = create_output(&model);
    let stream = AssistantMessageEventStream::new();

    process(
        create_phased_message_events(phases, TerminalStatus::Completed),
        &mut output,
        &stream,
        &model,
    )
    .await
    .expect("processes");

    assert_eq!(observed_stop_reasons(&stream).await, expected);
    assert_eq!(output.stop_reason, StopReason::Stop);
}

#[tokio::test]
async fn tracks_message_phases_commentary_commentary() {
    tracks_message_phases(
        ["commentary", "commentary"],
        [StopReason::Pending, StopReason::Pending],
    )
    .await;
}

#[tokio::test]
async fn tracks_message_phases_final_answer_final_answer() {
    tracks_message_phases(
        ["final_answer", "final_answer"],
        [StopReason::Stop, StopReason::Stop],
    )
    .await;
}

#[tokio::test]
async fn tracks_message_phases_commentary_final_answer() {
    tracks_message_phases(
        ["commentary", "final_answer"],
        [StopReason::Pending, StopReason::Stop],
    )
    .await;
}

#[tokio::test]
async fn replaces_a_provisional_final_answer_stop_with_an_incomplete_terminal_reason() {
    let model = create_model();
    let mut output = create_output(&model);
    let stream = AssistantMessageEventStream::new();

    process(
        create_phased_message_events(["final_answer", "final_answer"], TerminalStatus::Incomplete),
        &mut output,
        &stream,
        &model,
    )
    .await
    .expect("processes");

    assert_eq!(
        observed_stop_reasons(&stream).await,
        [StopReason::Stop, StopReason::Stop]
    );
    assert_eq!(output.stop_reason, StopReason::Length);
}

#[tokio::test]
async fn finalizes_completed_terminal_events_as_stop() {
    let model = create_model();
    let mut output = create_output(&model);
    let stream = AssistantMessageEventStream::new();

    process(create_completed_events(), &mut output, &stream, &model)
        .await
        .expect("processes");

    assert_eq!(output.response_id.as_deref(), Some("resp_completed"));
    assert_eq!(output.stop_reason, StopReason::Stop);
    assert_eq!(output.raw_stop_reason.as_deref(), Some("completed"));
    assert_eq!(
        (
            output.usage.input,
            output.usage.output,
            output.usage.cache_read,
            output.usage.cache_write,
            output.usage.total_tokens
        ),
        (15, 7, 2, 3, 27)
    );
}

#[tokio::test]
async fn finalizes_incomplete_terminal_events_as_length_stops() {
    let model = create_model();
    let mut output = create_output(&model);
    let stream = AssistantMessageEventStream::new();

    process(
        create_incomplete_events("max_output_tokens"),
        &mut output,
        &stream,
        &model,
    )
    .await
    .expect("processes");

    assert_eq!(output.response_id.as_deref(), Some("resp_incomplete"));
    assert_eq!(output.stop_reason, StopReason::Length);
    assert_eq!(
        output.raw_stop_reason.as_deref(),
        Some("incomplete.max_output_tokens")
    );
    assert_eq!(
        (
            output.usage.input,
            output.usage.output,
            output.usage.cache_read,
            output.usage.cache_write,
            output.usage.total_tokens
        ),
        (25, 12, 5, 0, 42)
    );
}

#[tokio::test]
async fn finalizes_content_filtered_incomplete_responses_as_non_retryable_errors() {
    let model = create_model();
    let mut output = create_output(&model);
    let stream = AssistantMessageEventStream::new();

    process(
        create_incomplete_events("content_filter"),
        &mut output,
        &stream,
        &model,
    )
    .await
    .expect("processes");

    assert_eq!(output.stop_reason, StopReason::Error);
    assert_eq!(
        output.raw_stop_reason.as_deref(),
        Some("incomplete.content_filter")
    );
    assert_eq!(
        output.error_message.as_deref(),
        Some("Response incomplete: content_filter")
    );
}

#[tokio::test]
async fn preserves_unknown_provider_incomplete_reasons_as_non_retryable_errors() {
    let model = create_model();
    let mut output = create_output(&model);
    let stream = AssistantMessageEventStream::new();

    process(
        create_incomplete_events("max_time_limit"),
        &mut output,
        &stream,
        &model,
    )
    .await
    .expect("processes");

    assert_eq!(output.stop_reason, StopReason::Error);
    assert_eq!(
        output.raw_stop_reason.as_deref(),
        Some("incomplete.max_time_limit")
    );
    assert_eq!(
        output.error_message.as_deref(),
        Some("Response incomplete: max_time_limit")
    );
}

#[tokio::test]
async fn rejects_failed_terminal_events_with_the_provider_error() {
    let model = create_model();
    let mut output = create_output(&model);
    let stream = AssistantMessageEventStream::new();

    let error = process(create_failed_events(), &mut output, &stream, &model)
        .await
        .expect_err("rejects");
    assert!(error.to_string().contains("server_error: boom"));
    assert_eq!(output.raw_stop_reason.as_deref(), Some("failed"));
}
