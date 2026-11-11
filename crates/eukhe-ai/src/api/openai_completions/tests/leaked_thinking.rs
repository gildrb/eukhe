//! Reasoning leaked into `delta.content`: a server that does not split
//! reasoning into its own field streams the chat template's reasoning
//! section as content. omp turns it into thinking (`ThinkingInbandScanner`,
//! `LeakedThinkingProjector`); so does this stream.

use serde_json::{json, Value as JsonValue};

use super::support::{run_with_chunks, test_model, user_context};
use crate::api::openai_completions::OpenAICompletionsOptions;
use crate::types::{Model, StopReason};
use crate::utils::assistant_message_frame::{
    reduce_assistant_message_frames, AssistantMessageFrameEncoder,
};

/// A reasoning model on a local OpenAI-compatible server.
fn local_model() -> Model {
    test_model(json!({
        "provider": "elpis",
        "baseUrl": "http://127.0.0.1:8080/v1",
        "reasoning": true,
    }))
}

/// What one streamed reply left.
struct Streamed {
    /// The settled message's content.
    settled: JsonValue,
    /// The content a client that replays the stream's frames holds.
    replayed: JsonValue,
    stop_reason: StopReason,
}

/// Stream one reply: a chunk per delta, then `finish_reason`.
async fn stream(model: &Model, deltas: &[JsonValue], finish_reason: &str) -> Streamed {
    let mut chunks: Vec<JsonValue> = deltas
        .iter()
        .map(|delta| json!({ "id": "chatcmpl-1", "choices": [{ "index": 0, "delta": delta }] }))
        .collect();
    chunks.push(json!({
        "id": "chatcmpl-1",
        "choices": [{ "index": 0, "delta": {}, "finish_reason": finish_reason }],
    }));
    let (_, events, message) = run_with_chunks(
        model,
        &user_context("hello"),
        OpenAICompletionsOptions::default(),
        chunks,
    )
    .await;
    let mut encoder = AssistantMessageFrameEncoder::new();
    let frames: Vec<_> = events
        .iter()
        .filter_map(|event| {
            encoder
                .encode(event)
                .expect("the stream follows the frame protocol")
        })
        .collect();
    let replayed = reduce_assistant_message_frames(&frames)
        .expect("the frames replay")
        .expect("a start frame");
    Streamed {
        settled: serde_json::to_value(&message.content).expect("content JSON"),
        replayed: serde_json::to_value(&replayed.content).expect("content JSON"),
        stop_reason: message.stop_reason,
    }
}

fn content(text: &str) -> JsonValue {
    json!({ "content": text })
}

/// A `<think>` section in the content is thinking, its tags split across
/// chunks included; the text after it is the answer.
#[tokio::test]
async fn a_think_section_in_the_content_is_thinking() {
    let streamed = stream(
        &local_model(),
        &[
            content("<thi"),
            content("nk>plan the"),
            content(" answer</th"),
            content("ink>\n\nThe answer."),
        ],
        "stop",
    )
    .await;
    let expected = json!([
        { "type": "thinking", "thinking": "plan the answer" },
        { "type": "text", "text": "\n\nThe answer." },
    ]);
    assert_eq!(streamed.settled, expected);
    assert_eq!(streamed.replayed, expected);
}

/// A chat template that prefills `<think>` leaves only the close in the
/// stream (Qwen3, DeepSeek-R1): the text before a bare `</think>` was
/// reasoning. The stream's blocks only grow, so a client sees the leading
/// text block end empty and the reasoning go on as a thinking block; the
/// settled message holds the thinking and the answer.
#[tokio::test]
async fn a_bare_close_makes_the_leading_text_thinking() {
    let streamed = stream(
        &local_model(),
        &[
            content("I should plan"),
            content(" first.\n</think>"),
            content("\n\nThe answer."),
        ],
        "stop",
    )
    .await;
    assert_eq!(
        streamed.settled,
        json!([
            { "type": "thinking", "thinking": "I should plan first.\n" },
            { "type": "text", "text": "\n\nThe answer." },
        ])
    );
    assert_eq!(
        streamed.replayed,
        json!([
            { "type": "text", "text": "" },
            { "type": "thinking", "thinking": "I should plan first.\n" },
            { "type": "text", "text": "\n\nThe answer." },
        ])
    );
}

/// A reply cut at the output limit inside its `<think>` section is
/// reasoning only: no text.
#[tokio::test]
async fn a_think_section_cut_at_the_output_limit_is_thinking() {
    let streamed = stream(
        &local_model(),
        &[content("<think>The harness is telling me")],
        "length",
    )
    .await;
    let expected = json!([{ "type": "thinking", "thinking": "The harness is telling me" }]);
    assert_eq!(streamed.settled, expected);
    assert_eq!(streamed.replayed, expected);
    assert_eq!(streamed.stop_reason, StopReason::Length);
}

/// A stream that carries a reasoning field keeps that reasoning: a tagged
/// copy in the content is dropped, and so is a stray close.
#[tokio::test]
async fn tags_beside_a_reasoning_field_are_dropped() {
    let expected = json!([
        { "type": "thinking", "thinking": "plan", "thinkingSignature": "reasoning_content" },
        { "type": "text", "text": "The answer." },
    ]);
    for answer in ["<think>plan</think>The answer.", "</think>The answer."] {
        let streamed = stream(
            &local_model(),
            &[json!({ "reasoning_content": "plan" }), content(answer)],
            "stop",
        )
        .await;
        assert_eq!(streamed.settled, expected, "{answer}");
        assert_eq!(streamed.replayed, expected, "{answer}");
    }
}

/// A reasoning tag inside a Markdown code span or fenced block is text.
#[tokio::test]
async fn a_tag_inside_code_stays_text() {
    let answer = "Use `<think>` tags:\n```xml\n<think>x</think>\n```\ndone";
    let streamed = stream(&local_model(), &[content(answer)], "stop").await;
    let expected = json!([{ "type": "text", "text": answer }]);
    assert_eq!(streamed.settled, expected);
    assert_eq!(streamed.replayed, expected);
}

/// The official `OpenAI` endpoint never leaks: its content is not scanned.
#[tokio::test]
async fn the_official_openai_endpoint_is_not_scanned() {
    let answer = "<think>plan</think>The answer.";
    let streamed = stream(&test_model(json!({})), &[content(answer)], "stop").await;
    assert_eq!(
        streamed.settled,
        json!([{ "type": "text", "text": answer }])
    );
}
