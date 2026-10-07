//! Port of `test/openai-responses-namespace.test.ts`.

use eukhe_pi_ai::api::openai_responses_shared::{
    convert_responses_messages, process_responses_stream, ConvertResponsesMessagesOptions,
    GrammarToolInputProperties, OpenAIResponsesStreamOptions,
};
use eukhe_pi_ai::types::JsonValue;
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Context, Message, Model, ToolCall,
};
use serde_json::json;

fn model_json() -> JsonValue {
    json!({
        "id": "gpt-5.4",
        "name": "GPT-5.4",
        "api": "openai-responses",
        "provider": "openai",
        "baseUrl": "https://api.openai.com/v1",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 400_000,
        "maxTokens": 128_000,
    })
}

fn model_from(value: JsonValue) -> Model {
    serde_json::from_value(value).expect("model")
}

fn model() -> Model {
    model_from(model_json())
}

/// TS `{ ...model, ...overrides }`.
fn model_with(overrides: &JsonValue) -> Model {
    let mut value = model_json();
    for (key, field) in overrides.as_object().expect("object") {
        value[key] = field.clone();
    }
    model_from(value)
}

fn create_output() -> AssistantMessage {
    let model = model();
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

fn create_function_call_events() -> Vec<JsonValue> {
    vec![
        json!({
            "type": "response.output_item.added",
            "sequence_number": 0,
            "output_index": 0,
            "item": { "type": "function_call", "id": "fc_test", "call_id": "call_test", "name": "lookup", "arguments": "" },
        }),
        json!({
            "type": "response.output_item.done",
            "sequence_number": 1,
            "output_index": 0,
            "item": {
                "type": "function_call",
                "id": "fc_test",
                "call_id": "call_test",
                "name": "lookup",
                "arguments": "{\"value\":\"hello\"}",
                "namespace": "dynamic_tools",
            },
        }),
        json!({
            "type": "response.completed",
            "sequence_number": 2,
            "response": { "id": "resp_test", "status": "completed" },
        }),
    ]
}

fn create_custom_tool_call_events() -> Vec<JsonValue> {
    vec![
        json!({
            "type": "response.output_item.added",
            "sequence_number": 0,
            "output_index": 0,
            "item": { "type": "custom_tool_call", "id": "ctc_test", "call_id": "call_test", "name": "query", "input": "" },
        }),
        json!({
            "type": "response.output_item.done",
            "sequence_number": 1,
            "output_index": 0,
            "item": {
                "type": "custom_tool_call",
                "id": "ctc_test",
                "call_id": "call_test",
                "name": "query",
                "input": "hello",
                "namespace": "dynamic_tools",
            },
        }),
        json!({
            "type": "response.completed",
            "sequence_number": 2,
            "response": { "id": "resp_test", "status": "completed" },
        }),
    ]
}

async fn process(
    events: Vec<JsonValue>,
    output: &mut AssistantMessage,
    options: &OpenAIResponsesStreamOptions,
) {
    process_responses_stream(
        futures::stream::iter(events.into_iter().map(Ok)),
        output,
        &AssistantMessageEventStream::new(),
        &model(),
        options,
    )
    .await
    .expect("processes");
}

fn get_tool_call(output: &AssistantMessage) -> &ToolCall {
    match output.content.first() {
        Some(AssistantContentBlock::ToolCall(tool_call)) => tool_call,
        _ => panic!("Expected toolCall block"),
    }
}

/// TS `toMatchObject` for flat objects.
fn assert_match_object(actual: &JsonValue, expected: &JsonValue) {
    for (key, value) in expected.as_object().expect("object") {
        assert_eq!(actual.get(key), Some(value), "property {key} of {actual}");
    }
}

/// TS `normalizeContext({ messages: [output] })`.
fn context_of(output: &AssistantMessage) -> eukhe_pi_ai::types::TranscriptContext {
    normalize_context(Context {
        messages: vec![Message::Assistant(output.clone())],
        ..Context::default()
    })
}

fn query_grammar() -> GrammarToolInputProperties {
    [("query".to_owned(), "input".to_owned())]
        .into_iter()
        .collect()
}

fn find_type<'a>(items: &'a [JsonValue], item_type: &str) -> Option<&'a JsonValue> {
    items.iter().find(|item| item["type"] == item_type)
}

// describe("OpenAI Responses terminal messages")
#[tokio::test]
async fn omits_an_absent_error_message() {
    let mut output = create_output();
    process(
        create_function_call_events(),
        &mut output,
        &OpenAIResponsesStreamOptions::default(),
    )
    .await;

    assert_eq!(output.error_message, None);
    assert!(serde_json::to_value(&output)
        .expect("serializes")
        .get("errorMessage")
        .is_none());
}

#[tokio::test]
async fn round_trips_a_function_namespace_received_only_on_output_item_done() {
    let mut output = create_output();
    process(
        create_function_call_events(),
        &mut output,
        &OpenAIResponsesStreamOptions::default(),
    )
    .await;

    let tool_call = get_tool_call(&output);
    assert_match_object(
        &serde_json::to_value(tool_call).expect("serializes"),
        &json!({
            "id": "call_test|fc_test",
            "name": "lookup",
            "arguments": { "value": "hello" },
            "namespace": "dynamic_tools",
        }),
    );

    let replayed = convert_responses_messages(
        &model(),
        &context_of(&output),
        &["openai"],
        &ConvertResponsesMessagesOptions::default(),
    )
    .expect("converts");
    assert_match_object(
        find_type(&replayed, "function_call").expect("function_call"),
        &json!({
            "type": "function_call",
            "id": "fc_test",
            "call_id": "call_test",
            "name": "lookup",
            "arguments": "{\"value\":\"hello\"}",
            "namespace": "dynamic_tools",
        }),
    );
}

#[tokio::test]
async fn round_trips_a_custom_tool_namespace_received_only_on_output_item_done() {
    let mut output = create_output();
    let options = OpenAIResponsesStreamOptions {
        grammar_tool_input_properties: Some(query_grammar()),
        ..OpenAIResponsesStreamOptions::default()
    };
    process(create_custom_tool_call_events(), &mut output, &options).await;

    let tool_call = get_tool_call(&output);
    assert_match_object(
        &serde_json::to_value(tool_call).expect("serializes"),
        &json!({
            "id": "call_test|ctc_test",
            "name": "query",
            "arguments": { "input": "hello" },
            "namespace": "dynamic_tools",
        }),
    );

    let replayed = convert_responses_messages(
        &model(),
        &context_of(&output),
        &["openai"],
        &ConvertResponsesMessagesOptions {
            grammar_tool_input_properties: Some(query_grammar()),
            ..ConvertResponsesMessagesOptions::default()
        },
    )
    .expect("converts");
    assert_match_object(
        find_type(&replayed, "custom_tool_call").expect("custom_tool_call"),
        &json!({
            "type": "custom_tool_call",
            "id": "ctc_test",
            "call_id": "call_test",
            "name": "query",
            "input": "hello",
            "namespace": "dynamic_tools",
        }),
    );
}

fn tool_call_block(value: JsonValue) -> AssistantContentBlock {
    serde_json::from_value(value).expect("tool call")
}

#[test]
fn drops_namespaces_when_the_target_cannot_replay_their_load_items() {
    let mut output = create_output();
    output.content.push(tool_call_block(json!({
        "type": "toolCall",
        "id": "call_function|fc_test",
        "name": "lookup",
        "arguments": { "value": "hello" },
        "namespace": "dynamic_tools",
    })));
    output.content.push(tool_call_block(json!({
        "type": "toolCall",
        "id": "call_custom|ctc_test",
        "name": "query",
        "arguments": { "input": "hello" },
        "namespace": "dynamic_tools",
    })));
    let target_models = [
        model_with(&json!({ "id": "gpt-5.2", "name": "GPT-5.2" })),
        model_with(&json!({ "provider": "azure" })),
        model_with(&json!({
            "api": "openai-codex-responses",
            "provider": "openai-codex",
            "id": "gpt-5.3-codex-spark",
            "name": "GPT-5.3 Codex Spark",
        })),
    ];

    for target_model in &target_models {
        let replayed = convert_responses_messages(
            target_model,
            &context_of(&output),
            &["openai"],
            &ConvertResponsesMessagesOptions {
                grammar_tool_input_properties: Some(query_grammar()),
                ..ConvertResponsesMessagesOptions::default()
            },
        )
        .expect("converts");
        let function_call = find_type(&replayed, "function_call").expect("function_call");
        let custom_tool_call = find_type(&replayed, "custom_tool_call").expect("custom_tool_call");
        assert!(function_call.get("namespace").is_none());
        assert!(custom_tool_call.get("namespace").is_none());
    }
}

#[test]
fn does_not_add_a_namespace_to_ordinary_function_calls() {
    let mut output = create_output();
    output.content.push(tool_call_block(json!({
        "type": "toolCall",
        "id": "call_test|fc_test",
        "name": "lookup",
        "arguments": { "value": "hello" },
    })));

    let replayed = convert_responses_messages(
        &model(),
        &context_of(&output),
        &["openai"],
        &ConvertResponsesMessagesOptions::default(),
    )
    .expect("converts");
    let replayed = find_type(&replayed, "function_call").expect("function_call");
    assert!(replayed.get("namespace").is_none());
}
