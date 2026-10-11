//! Port of `openrouter-cache-write-repro.test.ts` (live E2E, needs
//! `OPENROUTER_API_KEY`).

use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use serde_json::json;

use crate::compat::complete_simple;
use crate::providers::all::get_builtin_model;
use crate::types::{
    Context, JsonValue, Model, OnPayload, ProviderRequestOptions, SimpleStreamOptions, StopReason,
    StreamOptions,
};

fn create_long_system_prompt() -> String {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |elapsed| elapsed.as_nanos());
    let probe = "Prompt-caching probe content. Keep this exact text stable across requests so the provider can reuse prefix tokens and report cache read and cache write usage.";
    format!(
        "You are a concise assistant.\nCache nonce: {nanos}\n\n{}",
        [probe; 80].join("\n\n")
    )
}

/// The TS `onPayload`: mark the last user text with `cache_control`.
fn mark_last_user_text(payload: &mut JsonValue) {
    let Some(messages) = payload
        .get_mut("messages")
        .and_then(JsonValue::as_array_mut)
    else {
        return;
    };
    for message in messages.iter_mut().rev() {
        if message["role"] != "user" {
            continue;
        }
        if let Some(text) = message["content"].as_str() {
            let text = text.to_owned();
            message["content"] =
                json!([{ "type": "text", "text": text, "cache_control": { "type": "ephemeral" } }]);
            break;
        }
        let Some(parts) = message["content"].as_array_mut() else {
            continue;
        };
        if let Some(part) = parts.iter_mut().rev().find(|part| part["type"] == "text") {
            part["cache_control"] = json!({ "type": "ephemeral" });
        }
        break;
    }
}

#[tokio::test]
#[ignore = "needs OPENROUTER_API_KEY; run with --ignored"]
async fn regression_preserves_cache_write_tokens_on_openai_completions_stream_path() {
    let api_key = std::env::var("OPENROUTER_API_KEY").expect("OPENROUTER_API_KEY");
    let model = get_builtin_model("openrouter", "google/gemini-2.5-flash").expect("catalog model");
    let context: Context = serde_json::from_value(json!({
        "systemPrompt": create_long_system_prompt(),
        "messages": [{ "role": "user", "content": "Reply with exactly: OK", "timestamp": 1 }],
    }))
    .expect("valid context JSON");
    let on_payload: OnPayload<Model> = Arc::new(|mut payload, _model| {
        mark_last_user_text(&mut payload);
        Box::pin(async move { Ok(Some(payload)) })
    });
    let options = SimpleStreamOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                api_key: Some(api_key),
                on_payload: Some(on_payload),
                ..ProviderRequestOptions::default()
            },
            max_tokens: Some(32),
            temperature: Some(0.0),
            ..StreamOptions::default()
        },
        ..SimpleStreamOptions::default()
    };

    let first = complete_simple(&model, context.clone(), options.clone())
        .await
        .expect("first request");
    assert_eq!(
        first.stop_reason,
        StopReason::Stop,
        "{:?}",
        first.error_message
    );

    let second = complete_simple(&model, context, options)
        .await
        .expect("second request");
    assert_eq!(
        second.stop_reason,
        StopReason::Stop,
        "{:?}",
        second.error_message
    );

    // With the cache_control marker, at least one of the calls creates cache.
    assert!(first.usage.cache_write > 0 || second.usage.cache_write > 0);
}
