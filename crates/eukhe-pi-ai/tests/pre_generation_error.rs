//! Port of `test/pre-generation-error.test.ts`: every direct API
//! `streamSimple` rejects a request without auth before generation starts.
//!
//! TS asserts the call throws synchronously with
//! "No API key for provider: test-provider". The Rust `stream_simple`
//! functions return an [`AssistantMessageEventStream`] instead of throwing;
//! the same pre-generation failure terminates that stream with a single error
//! event and an error result carrying the TS message verbatim, without any
//! request being sent.

use eukhe_pi_ai::api::{
    anthropic_messages, azure_openai_responses, google_generative_ai, mistral_conversations,
    openai_codex_responses, openai_completions, openai_responses,
};
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{
    AssistantMessageEvent, Context, ErrorReason, Model, StopReason, TranscriptContext,
};
use futures::StreamExt;
use serde_json::json;

const MISSING_AUTH: &str = "No API key for provider: test-provider";

fn model(api: &str) -> Model {
    serde_json::from_value(json!({
        "id": "test-model",
        "name": "Test",
        "api": api,
        "provider": "test-provider",
        "baseUrl": "https://example.invalid",
        "reasoning": false,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 1_000,
        "maxTokens": 100,
    }))
    .expect("test model")
}

/// TS `expect(create).toThrow("No API key for provider: test-provider")`:
/// the stream ends before generation with exactly one error event, and the
/// result is that error.
async fn expect_missing_auth_throws(api: &str, stream: AssistantMessageEventStream) {
    let events: Vec<AssistantMessageEvent> = stream.events().collect().await;
    let result = stream.result().await;

    assert_eq!(result.stop_reason, StopReason::Error, "{api}");
    assert_eq!(result.error_message.as_deref(), Some(MISSING_AUTH), "{api}");
    assert!(result.content.is_empty(), "{api}: {:?}", result.content);
    assert_eq!(result.api, api);
    assert_eq!(result.provider, "test-provider", "{api}");
    assert_eq!(result.model, "test-model", "{api}");

    let [AssistantMessageEvent::Error { reason, error }] = events.as_slice() else {
        panic!("{api}: expected a single error event, got {events:?}");
    };
    assert_eq!(*reason, ErrorReason::Error, "{api}");
    assert_eq!(error, &result, "{api}");
}

#[tokio::test]
async fn throws_synchronously_when_auth_is_missing() {
    let context: TranscriptContext = normalize_context(Context::default());
    let options = SimpleStreamOptions::default;

    expect_missing_auth_throws(
        "anthropic-messages",
        anthropic_messages::stream_simple(&model("anthropic-messages"), &context, &options()),
    )
    .await;
    expect_missing_auth_throws(
        "azure-openai-responses",
        azure_openai_responses::stream_simple(
            &model("azure-openai-responses"),
            &context,
            options(),
        ),
    )
    .await;
    expect_missing_auth_throws(
        "google-generative-ai",
        google_generative_ai::stream_simple(&model("google-generative-ai"), &context, options()),
    )
    .await;
    expect_missing_auth_throws(
        "mistral-conversations",
        mistral_conversations::stream_simple(&model("mistral-conversations"), &context, options()),
    )
    .await;
    expect_missing_auth_throws(
        "openai-codex-responses",
        openai_codex_responses::stream_simple(
            &model("openai-codex-responses"),
            &context,
            options(),
        ),
    )
    .await;
    expect_missing_auth_throws(
        "openai-completions",
        openai_completions::stream_simple(&model("openai-completions"), &context, options()),
    )
    .await;
    expect_missing_auth_throws(
        "openai-responses",
        openai_responses::stream_simple(&model("openai-responses"), &context, options()),
    )
    .await;
}
