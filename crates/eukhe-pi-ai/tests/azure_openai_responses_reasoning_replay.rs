//! Port of `test/azure-openai-responses-reasoning-replay.test.ts`.

use eukhe_pi_ai::api::openai_responses_shared::{
    convert_responses_messages, process_responses_stream, ConvertResponsesMessagesOptions,
    OpenAIResponsesStreamOptions,
};
use eukhe_pi_ai::types::{AssistantMessage, JsonValue, Model, StopReason, Usage};
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{Context, Message};
use serde_json::json;

fn now() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock")
            .as_millis(),
    )
    .expect("epoch ms")
}

fn create_model() -> Model {
    serde_json::from_value(json!({
        "id": "gpt-5-mini",
        "name": "GPT-5 Mini",
        "api": "azure-openai-responses",
        "provider": "azure",
        "baseUrl": "https://example.invalid",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 400_000,
        "maxTokens": 128_000,
    }))
    .expect("model")
}

fn create_output(model: &Model) -> AssistantMessage {
    AssistantMessage {
        content: Vec::new(),
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason: StopReason::Pending,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: now(),
    }
}

fn create_events(
    done_item: &JsonValue,
    completed_item: &JsonValue,
) -> impl futures::Stream<Item = Result<JsonValue, eukhe_pi_ai::utils::diagnostics::Thrown>> + Send
{
    futures::stream::iter(
        [
            json!({
                "type": "response.output_item.added",
                "output_index": 0,
                "sequence_number": 0,
                "item": { "type": "reasoning", "id": done_item["id"], "summary": [] },
            }),
            json!({
                "type": "response.output_item.done",
                "output_index": 0,
                "sequence_number": 1,
                "item": done_item,
            }),
            json!({
                "type": "response.completed",
                "sequence_number": 2,
                "response": {
                    "id": "resp_test",
                    "status": "completed",
                    "output": [completed_item],
                },
            }),
        ]
        .into_iter()
        .map(Ok),
    )
}

fn get_replayed_reasoning(model: &Model, assistant: &AssistantMessage) -> Option<JsonValue> {
    let timestamp = now();
    let context: Context = serde_json::from_value(json!({
        "messages": [
            { "role": "user", "content": "first", "timestamp": timestamp - 1 },
            Message::Assistant(assistant.clone()),
            { "role": "user", "content": "follow-up", "timestamp": timestamp },
        ],
    }))
    .expect("context");
    let context = normalize_context(context);
    let input = convert_responses_messages(
        model,
        &context,
        &["azure"],
        &ConvertResponsesMessagesOptions::default(),
    )
    .expect("convert");
    input.into_iter().find(|item| item["type"] == "reasoning")
}

/// TS `toMatchObject` on the listed keys.
fn assert_match_object(actual: Option<JsonValue>, expected: &JsonValue) {
    let actual = actual.expect("reasoning item");
    for (key, value) in expected.as_object().expect("object") {
        assert_eq!(&actual[key], value, "key {key} of {actual}");
    }
}

async fn replay(done_item: &JsonValue, completed_item: &JsonValue) -> Option<JsonValue> {
    let model = create_model();
    let mut output = create_output(&model);
    process_responses_stream(
        create_events(done_item, completed_item),
        &mut output,
        &AssistantMessageEventStream::new(),
        &model,
        &OpenAIResponsesStreamOptions::default(),
    )
    .await
    .expect("process");
    get_replayed_reasoning(&model, &output)
}

#[tokio::test]
async fn preserves_existing_encrypted_content_from_output_item_done() {
    let done_item = json!({
        "type": "reasoning",
        "id": "rs_done",
        "summary": [],
        "encrypted_content": "from-output-item-done",
    });
    let mut completed_item = done_item.clone();
    completed_item["encrypted_content"] = json!("from-response-completed");

    assert_match_object(
        replay(&done_item, &completed_item).await,
        &json!({
            "type": "reasoning",
            "id": "rs_done",
            "encrypted_content": "from-output-item-done",
        }),
    );
}

#[tokio::test]
async fn fills_encrypted_content_when_output_item_done_omitted_it() {
    let done_item = json!({
        "type": "reasoning",
        "id": "rs_missing",
        "summary": [],
    });
    let mut completed_item = done_item.clone();
    completed_item["encrypted_content"] = json!("from-response-completed");

    assert_match_object(
        replay(&done_item, &completed_item).await,
        &json!({
            "type": "reasoning",
            "id": "rs_missing",
            "encrypted_content": "from-response-completed",
        }),
    );
}
