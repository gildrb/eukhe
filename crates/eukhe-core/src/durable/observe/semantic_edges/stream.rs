//! The stream wrapper that binds one session's recorder to its provider
//! turns (TS `wrapStreamFnWithSemanticEdges`), over the pi-ai provider
//! contract: the stream fn is synchronous, so the wrapper wraps
//! OUTERMOST, mints and merges the id before the inner call, and settles
//! the request from a forwarding task that observes the inner stream's
//! events.

use std::sync::Arc;

use eukhe_pi_ai::api::{StreamFn, StreamSimpleFn};
use eukhe_pi_ai::types::StreamOptions;
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, Message, Model, StopReason, TranscriptContext,
};
use futures::StreamExt as _;
use serde_json::Value as JsonValue;
use sha2::{Digest as _, Sha256};

use super::{model_request_headers, SemanticEdgeRecorder};

/// Bind a full-options stream function to one session's recorder (TS
/// `wrapStreamFnWithSemanticEdges`; the engine wraps it OUTERMOST). The
/// id is minted and `request_started` appended before the inner call; the
/// request commits or fails when its stream settles (an error/aborted
/// final message is a failure, and a stream that ends with no terminal
/// event fails too). A disabled recorder leaves the call untouched: no
/// id, no headers, no event.
pub(crate) fn wrap_stream_fn(recorder: Arc<SemanticEdgeRecorder>, inner: StreamFn) -> StreamFn {
    Arc::new(move |model, context, mut options| {
        let tail = serde_json::json!({ "extra": options.extra.clone() });
        let fingerprint = turn_fingerprint(model, context, &options.stream, &tail);
        let Some(request_id) = recorder.start_turn_request(fingerprint) else {
            return inner(model, context, options);
        };
        merge_request_headers(&mut options.stream, &request_id);
        observe(
            Arc::clone(&recorder),
            request_id,
            inner(model, context, options),
        )
    })
}

/// Bind the provider-neutral `stream_simple` fn the same way
/// ([`wrap_stream_fn`]); the simple options' reasoning level rides the
/// fingerprint where the full options hash their API-specific `extra`.
pub(crate) fn wrap_stream_simple_fn(
    recorder: Arc<SemanticEdgeRecorder>,
    inner: StreamSimpleFn,
) -> StreamSimpleFn {
    Arc::new(move |model, context, mut options| {
        let tail = serde_json::json!({
            "reasoning": options.reasoning,
            "toolChoice": options.tool_choice,
        });
        let fingerprint = turn_fingerprint(model, context, &options.stream, &tail);
        let Some(request_id) = recorder.start_turn_request(fingerprint) else {
            return inner(model, context, options);
        };
        merge_request_headers(&mut options.stream, &request_id);
        observe(
            Arc::clone(&recorder),
            request_id,
            inner(model, context, options),
        )
    })
}

/// Overlay the two id-carrying headers on one call's headers (the id's
/// headers win, and they ride even a headerless call).
fn merge_request_headers(stream: &mut StreamOptions, request_id: &str) {
    let headers = stream.request.headers.get_or_insert_with(Default::default);
    for (header, id) in model_request_headers(request_id) {
        headers.insert(header, Some(id));
    }
}

/// Forward one inner stream through a fresh observed stream: the wrapper
/// returns synchronously, so the events are pumped by a spawned task that
/// settles the request by the first terminal event's stop reason, or as
/// failed when the stream ends with no terminal event. Must be called
/// inside a tokio runtime (the provider contract runs every request on
/// one).
fn observe(
    recorder: Arc<SemanticEdgeRecorder>,
    request_id: String,
    inner: AssistantMessageEventStream,
) -> AssistantMessageEventStream {
    let outer = AssistantMessageEventStream::new();
    let sink = outer.clone();
    tokio::spawn(async move {
        let mut settled = false;
        let mut events = inner.events();
        while let Some(event) = events.next().await {
            if !settled {
                if let Some(message) = terminal_message(&event) {
                    settled = true;
                    if matches!(message.stop_reason, StopReason::Error | StopReason::Aborted) {
                        recorder.fail_request(&request_id);
                    } else {
                        recorder.finish_request(&request_id);
                    }
                }
            }
            sink.push(event);
        }
        // A stream that ended without a terminal event never settles its
        // request: it is a failed request, not a stuck in-flight one.
        if !settled {
            recorder.fail_request(&request_id);
        }
        sink.end(None);
    });
    outer
}

/// The final message of a terminal event (`done` / `error`), else `None`.
fn terminal_message(event: &AssistantMessageEvent) -> Option<&AssistantMessage> {
    match event {
        AssistantMessageEvent::Done { message, .. } => Some(message),
        AssistantMessageEvent::Error { error, .. } => Some(error),
        _ => None,
    }
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher.finalize().into()
}

/// sha256 over the canonical JSON of one fingerprint input (TS
/// `digestJson`).
fn digest_json(value: &impl serde::Serialize) -> [u8; 32] {
    sha256(&serde_json::to_vec(value).unwrap_or_default())
}

/// Fingerprint of one turn call body (TS `hashTurnBody`, in-memory only —
/// never on disk): the recorder reuses a parked retry's id only for an
/// equal fingerprint. It hashes a bounded subset — the model identity, the
/// shared sampling options, a `tail` carrying the options shape the caller
/// used (the full options' API-specific `extra`, or the simple options'
/// reasoning level and tool choice), the leading system message's digest
/// (the normalized transcript carries the prompt there), the message
/// count, the last message's digest, and the tools digest (declared on
/// the transcript's system messages) — so the full body is never
/// re-serialized per request; the fingerprint only gates parked-retry id
/// reuse within one retry window.
fn turn_fingerprint(
    model: &Model,
    context: &TranscriptContext,
    stream: &StreamOptions,
    tail: &JsonValue,
) -> [u8; 32] {
    let messages = context.messages();
    let leading_system = messages.iter().find_map(|message| match message {
        Message::System(system) => Some(system),
        _ => None,
    });
    let tools: Vec<_> = messages
        .iter()
        .filter_map(|message| match message {
            Message::System(system) => Some((&system.tools_added, &system.tools_removed)),
            _ => None,
        })
        .collect();
    let body = serde_json::json!({
        "provider": model.provider,
        "model": model.id,
        "api": model.api,
        "temperature": stream.temperature,
        "maxTokens": stream.max_tokens,
        "serviceTier": stream.service_tier,
        "tail": tail,
        "systemPromptDigest": leading_system.map(digest_json),
        "messageCount": messages.len(),
        "lastMessageDigest": messages.last().map(digest_json),
        "toolsDigest": digest_json(&tools),
    });
    sha256(&serde_json::to_vec(&body).unwrap_or_default())
}
