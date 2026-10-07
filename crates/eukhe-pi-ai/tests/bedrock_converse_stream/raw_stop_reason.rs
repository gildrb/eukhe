//! Port of `test/bedrock-raw-stop-reason.test.ts`.
//!
//! "forwards SDK error items": with the real SDK an exception item is a
//! modeled `InternalServerException`, so the message carries the
//! `Internal server error:` prefix (the TS mock's plain `Error` has none).

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_pi_ai::api::bedrock_converse_stream::stream;
use eukhe_pi_ai::types::OnProviderStreamEvent;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, CacheRetention, JsonValue, Model, StopReason,
    TextContent,
};
use serde_json::json;

use super::support::{
    context_of, event_stream, get_model, mock_env, options, user, with_base_url, EnvGuard,
    MockBedrock, Reply,
};

type Received = Arc<Mutex<Vec<(JsonValue, Model)>>>;

fn recorder(received: Received) -> OnProviderStreamEvent {
    Arc::new(move |item, model| {
        let received = received.clone();
        let item = item.clone();
        let model = model.clone();
        Box::pin(async move {
            tokio::task::yield_now().await;
            received
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push((item, model));
            Ok(())
        })
    })
}

async fn run(items: &[JsonValue], received: Option<Received>) -> (AssistantMessage, Model) {
    let server = MockBedrock::start(vec![Reply::events(&[], event_stream(items))]).await;
    let model = with_base_url(
        &get_model("amazon-bedrock", "us.anthropic.claude-opus-4-8"),
        &server.url,
    );
    let mut options = options(json!({}));
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.request.env = Some(mock_env());
    options.stream.on_provider_stream_event = received.map(recorder);
    let message = stream(&model, &context_of(vec![user("hello")]), options)
        .result()
        .await;
    (message, model)
}

fn ending_with(stop_reason: &str) -> Vec<JsonValue> {
    vec![
        json!({ "messageStart": { "role": "assistant" } }),
        json!({ "messageStop": { "stopReason": stop_reason } }),
    ]
}

#[tokio::test]
async fn forwards_sdk_stream_items_in_order_before_normalizing_them() {
    let _env = EnvGuard::new(&[]).await;
    let items = vec![
        json!({ "messageStart": { "role": "assistant" } }),
        json!({ "contentBlockDelta": { "contentBlockIndex": 0, "delta": { "text": "hello" } } }),
        json!({ "messageStop": { "stopReason": "end_turn", "additionalModelResponseFields": { "source": "test" } } }),
        json!({ "metadata": { "usage": { "inputTokens": 1, "outputTokens": 1, "totalTokens": 2 } } }),
    ];
    let received: Received = Arc::default();
    let (result, model) = run(&items, Some(received.clone())).await;
    let received = received
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(
        received
            .iter()
            .map(|(item, _)| item.clone())
            .collect::<Vec<_>>(),
        items
    );
    assert!(received
        .iter()
        .all(|(_, event_model)| *event_model == model));
    assert_eq!(result.stop_reason, StopReason::Stop);
    assert_eq!(
        result.content,
        vec![AssistantContentBlock::Text(TextContent::new("hello"))]
    );
}

#[tokio::test]
async fn forwards_sdk_error_items_before_reporting_them() {
    let _env = EnvGuard::new(&[]).await;
    let items = vec![
        json!({ "messageStart": { "role": "assistant" } }),
        json!({ "internalServerException": { "message": "bedrock stream failed" } }),
    ];
    let received: Received = Arc::default();
    let (result, _) = run(&items, Some(received.clone())).await;
    let received = received
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(received.len(), 2);
    assert_eq!(received[0].0, items[0]);
    assert_eq!(
        received[1].0["internalServerException"]["message"],
        json!("bedrock stream failed")
    );
    assert_eq!(result.stop_reason, StopReason::Error);
    assert_eq!(
        result.error_message.as_deref(),
        Some("Internal server error: bedrock stream failed")
    );
}

#[tokio::test]
async fn preserves_raw_bedrock_stop_reasons_for_successful_stops() {
    let _env = EnvGuard::new(&[]).await;
    let (message, _) = run(&ending_with("end_turn"), None).await;
    assert_eq!(message.stop_reason, StopReason::Stop);
    assert_eq!(message.raw_stop_reason.as_deref(), Some("end_turn"));
    assert_eq!(message.error_message, None);
}

#[tokio::test]
async fn preserves_raw_bedrock_stop_reasons_for_provider_error_stops() {
    let _env = EnvGuard::new(&[]).await;
    let (message, _) = run(&ending_with("guardrail_intervened"), None).await;
    assert_eq!(message.stop_reason, StopReason::Error);
    assert_eq!(
        message.raw_stop_reason.as_deref(),
        Some("guardrail_intervened")
    );
    assert_eq!(
        message.error_message.as_deref(),
        Some("Provider stopped with: guardrail_intervened")
    );
}
