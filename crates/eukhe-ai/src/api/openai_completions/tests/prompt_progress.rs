//! eukhe addition: llama.cpp `return_progress` / `prompt_progress`.

use serde_json::json;

use super::support::{capture_payload, run_with_chunks, test_model, user_context};
use crate::api::openai_completions::streaming::parse_prompt_progress;
use crate::api::openai_completions::OpenAICompletionsOptions;
use crate::types::{AssistantMessageEvent, JsonValue, PromptProgress, Usage, UsageCost};

async fn return_progress(overrides: JsonValue) -> Option<JsonValue> {
    capture_payload(
        &test_model(overrides),
        &user_context("hi"),
        OpenAICompletionsOptions::default(),
    )
    .await
    .get("return_progress")
    .cloned()
}

fn llama_cpp() -> JsonValue {
    json!({ "provider": "llama-cpp", "baseUrl": "http://127.0.0.1:8080/v1" })
}

#[tokio::test]
async fn llama_cpp_requests_prompt_progress() {
    assert_eq!(return_progress(llama_cpp()).await, Some(json!(true)));
}

#[tokio::test]
async fn openai_and_custom_providers_do_not_request_prompt_progress() {
    assert_eq!(return_progress(json!({})).await, None);
    assert_eq!(
        return_progress(json!({ "provider": "my-box", "baseUrl": "http://10.0.0.2:8000/v1" }))
            .await,
        None
    );
}

#[tokio::test]
async fn compat_supports_prompt_progress_requests_it_on_a_custom_provider() {
    let payload = return_progress(json!({
        "provider": "my-box",
        "baseUrl": "http://10.0.0.2:8000/v1",
        "compat": { "supportsPromptProgress": true },
    }))
    .await;
    assert_eq!(payload, Some(json!(true)));
}

#[tokio::test]
async fn llama_cpp_prompt_progress_chunks_become_events_before_the_text() {
    let id = "chatcmpl-llama";
    let chunks = vec![
        json!({ "id": id, "choices": [],
            "prompt_progress": { "total": 100, "cache": 40, "processed": 40, "time_ms": 3 } }),
        json!({ "id": id, "choices": [{ "index": 0, "delta": { "role": "assistant" } }],
            "prompt_progress": { "total": 100, "cache": 40, "processed": 100, "time_ms": 51 } }),
        json!({ "id": id, "choices": [{ "index": 0, "delta": { "content": "Hel" } }] }),
        json!({ "id": id, "choices": [{ "index": 0, "delta": { "content": "lo" } }] }),
        json!({ "id": id, "choices": [{ "index": 0, "delta": {}, "finish_reason": "stop" }] }),
        json!({ "id": id, "choices": [], "usage": {
            "prompt_tokens": 100, "completion_tokens": 2, "total_tokens": 102,
            "prompt_tokens_details": { "cached_tokens": 40 } } }),
    ];
    let (_, events, message) = run_with_chunks(
        &test_model(llama_cpp()),
        &user_context("hi"),
        OpenAICompletionsOptions::default(),
        chunks,
    )
    .await;

    let names: Vec<&str> = events
        .iter()
        .map(AssistantMessageEvent::type_name)
        .collect();
    assert_eq!(
        names,
        vec![
            "start",
            "prompt_progress",
            "prompt_progress",
            "text_start",
            "text_delta",
            "text_delta",
            "text_end",
            "done"
        ]
    );
    let progress: Vec<&PromptProgress> = events
        .iter()
        .filter_map(|event| {
            if let AssistantMessageEvent::PromptProgress { progress, .. } = event {
                Some(progress)
            } else {
                None
            }
        })
        .collect();
    assert_eq!(
        progress,
        vec![
            &PromptProgress {
                total: 100,
                cache: 40,
                processed: 40,
                time_ms: 3
            },
            &PromptProgress {
                total: 100,
                cache: 40,
                processed: 100,
                time_ms: 51
            },
        ]
    );
    assert_eq!(
        message.usage,
        Usage {
            input: 60,
            output: 2,
            cache_read: 40,
            cache_write: 0,
            cache_write_1h: None,
            reasoning: Some(0),
            total_tokens: 102,
            cost: UsageCost::default(),
        }
    );
}

#[test]
fn parse_prompt_progress_needs_total_and_processed_and_takes_floats() {
    assert_eq!(
        parse_prompt_progress(&json!({ "processed": 5, "cache": 1 })),
        None
    );
    assert_eq!(parse_prompt_progress(&json!({ "total": 5 })), None);
    assert_eq!(
        parse_prompt_progress(&json!({ "total": 10.0, "processed": 4.0, "time_ms": 7.5 })),
        Some(PromptProgress {
            total: 10,
            cache: 0,
            processed: 4,
            time_ms: 7
        })
    );
}
