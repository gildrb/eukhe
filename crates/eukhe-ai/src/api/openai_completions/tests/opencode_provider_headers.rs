//! Port of `opencode-provider-headers.test.ts` (tests
//! `providers::opencode_headers`, the wrapper the `opencode` providers put
//! around their `openai-completions` streams).

use std::sync::{Arc, Mutex, PoisonError};

use serde_json::json;

use super::support::{model, user_context};
use crate::api::ProviderStreams;
use crate::providers::faux::{faux_assistant_message, FauxAssistantMessageOptions};
use crate::providers::opencode_headers::with_opencode_session_header;
use crate::types::{
    AssistantMessageEvent, CacheRetention, DoneReason, Model, ProviderHeaders,
    ProviderStreamOptions, SimpleStreamOptions, StreamOptions, TranscriptContext,
};
use crate::utils::event_stream::AssistantMessageEventStream;

fn test_model() -> Model {
    model(json!({
        "id": "test-model",
        "name": "Test model",
        "api": "test-api",
        "provider": "opencode",
        "baseUrl": "https://opencode.ai/zen/v1",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 1000,
        "maxTokens": 100,
    }))
}

fn completed_stream() -> AssistantMessageEventStream {
    let stream = AssistantMessageEventStream::new();
    let message = faux_assistant_message("ok", FauxAssistantMessageOptions::default());
    stream.push(AssistantMessageEvent::Start {
        partial: message.clone(),
    });
    stream.push(AssistantMessageEvent::Done {
        reason: DoneReason::Stop,
        message: message.clone(),
    });
    stream.end(Some(message));
    stream
}

/// The captured `options.headers` of the last dispatched call
/// (`Some(None)`: a call without headers).
type Captured = Arc<Mutex<Option<Option<ProviderHeaders>>>>;

fn recording_streams() -> (ProviderStreams, Captured) {
    let captured: Captured = Arc::default();
    let stream_sink = Arc::clone(&captured);
    let simple_sink = Arc::clone(&captured);
    let streams = ProviderStreams {
        stream: Arc::new(
            move |_model: &Model, _context: &TranscriptContext, options: ProviderStreamOptions| {
                *stream_sink.lock().unwrap_or_else(PoisonError::into_inner) =
                    Some(options.stream.request.headers);
                completed_stream()
            },
        ),
        stream_simple: Arc::new(
            move |_model: &Model, _context: &TranscriptContext, options: SimpleStreamOptions| {
                *simple_sink.lock().unwrap_or_else(PoisonError::into_inner) =
                    Some(options.stream.request.headers);
                completed_stream()
            },
        ),
        fetch_deferred: None,
        cancel_deferred: None,
    };
    (streams, captured)
}

fn captured_headers(captured: &Captured) -> Option<ProviderHeaders> {
    captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("a stream was dispatched")
}

fn headers(entries: &[(&str, Option<&str>)]) -> ProviderHeaders {
    entries
        .iter()
        .map(|(name, value)| ((*name).to_owned(), value.map(str::to_owned)))
        .collect()
}

fn session_options(
    session_id: Option<&str>,
    request_headers: Option<ProviderHeaders>,
) -> StreamOptions {
    let mut options = StreamOptions {
        session_id: session_id.map(str::to_owned),
        ..StreamOptions::default()
    };
    options.request.headers = request_headers;
    options
}

// Regression test for https://github.com/earendil-works/pi/issues/9326
#[test]
fn maps_session_id_for_stream_requests_even_without_cache_retention() {
    let (recording, captured) = recording_streams();
    let streams = with_opencode_session_header(recording);

    let _stream = (streams.stream)(
        &test_model(),
        &user_context("hi"),
        ProviderStreamOptions {
            stream: StreamOptions {
                cache_retention: Some(CacheRetention::None),
                ..session_options(Some("conversation-1"), None)
            },
            ..ProviderStreamOptions::default()
        },
    );

    assert_eq!(
        captured_headers(&captured),
        Some(headers(&[("x-opencode-session", Some("conversation-1"))]))
    );
}

#[test]
fn maps_session_id_for_stream_simple_requests_even_without_cache_retention() {
    let (recording, captured) = recording_streams();
    let streams = with_opencode_session_header(recording);

    let _stream = (streams.stream_simple)(
        &test_model(),
        &user_context("hi"),
        SimpleStreamOptions {
            stream: StreamOptions {
                cache_retention: Some(CacheRetention::None),
                ..session_options(Some("conversation-1"), None)
            },
            ..SimpleStreamOptions::default()
        },
    );

    assert_eq!(
        captured_headers(&captured),
        Some(headers(&[("x-opencode-session", Some("conversation-1"))]))
    );
}

/// `it.each` of "preserves a case-insensitive caller override".
fn preserves_caller_override(value: Option<&str>) {
    let (recording, captured) = recording_streams();
    let streams = with_opencode_session_header(recording);
    let caller = headers(&[("X-OpenCode-Session", value)]);

    let _stream = (streams.stream_simple)(
        &test_model(),
        &user_context("hi"),
        SimpleStreamOptions {
            stream: session_options(Some("generated-value"), Some(caller.clone())),
            ..SimpleStreamOptions::default()
        },
    );

    assert_eq!(captured_headers(&captured), Some(caller));
}

#[test]
fn preserves_a_case_insensitive_caller_override_with_a_value() {
    preserves_caller_override(Some("caller-value"));
}

#[test]
fn preserves_a_case_insensitive_caller_override_with_null() {
    preserves_caller_override(None);
}

#[test]
fn does_not_fabricate_a_session_header_when_session_id_is_absent() {
    let (recording, captured) = recording_streams();
    let streams = with_opencode_session_header(recording);

    let _stream = (streams.stream_simple)(
        &test_model(),
        &user_context("hi"),
        SimpleStreamOptions {
            stream: session_options(None, Some(headers(&[("x-custom", Some("value"))]))),
            ..SimpleStreamOptions::default()
        },
    );

    assert_eq!(
        captured_headers(&captured),
        Some(headers(&[("x-custom", Some("value"))]))
    );
}
