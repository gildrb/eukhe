//! Port of `test/openai-responses-partial-json-cleanup.test.ts`.
//!
//! Rust tool-call blocks never carry the `partialJson` scratch field (it lives
//! in the stream processor), so its absence is checked on the serialized
//! wire form.

use eukhe_pi_ai::api::openai_responses_shared::{
    process_responses_stream, OpenAIResponsesStreamOptions,
};
use eukhe_pi_ai::types::JsonValue;
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, Model, ToolCall,
};
use futures::StreamExt;
use serde_json::json;

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

fn create_function_call_events(arguments_json: &str) -> Vec<JsonValue> {
    vec![
        json!({
            "type": "response.output_item.added",
            "item": { "type": "function_call", "id": "fc_test", "call_id": "call_test", "name": "edit", "arguments": "" },
        }),
        json!({ "type": "response.function_call_arguments.delta", "delta": "{\"path\":\"README.md\"" }),
        json!({ "type": "response.function_call_arguments.delta", "delta": ",\"content\":\"updated\"}" }),
        json!({ "type": "response.function_call_arguments.done", "arguments": arguments_json }),
        json!({
            "type": "response.output_item.done",
            "item": { "type": "function_call", "id": "fc_test", "call_id": "call_test", "name": "edit", "arguments": arguments_json },
        }),
        json!({
            "type": "response.completed",
            "sequence_number": 5,
            "response": { "id": "resp_test", "status": "completed" },
        }),
    ]
}

fn has_partial_json(tool_call: &ToolCall) -> bool {
    serde_json::to_value(tool_call)
        .expect("serializes")
        .get("partialJson")
        .is_some()
}

#[tokio::test]
async fn removes_partial_json_from_persisted_tool_call_blocks_at_output_item_done() {
    let model: Model = serde_json::from_value(json!({
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
    .expect("model");
    let mut output = create_output(&model);
    let stream = AssistantMessageEventStream::new();
    let arguments_json = r#"{"path":"README.md","content":"updated"}"#;

    process_responses_stream(
        futures::stream::iter(
            create_function_call_events(arguments_json)
                .into_iter()
                .map(Ok),
        ),
        &mut output,
        &stream,
        &model,
        &OpenAIResponsesStreamOptions::default(),
    )
    .await
    .expect("processes");

    assert_eq!(output.content.len(), 1);
    let AssistantContentBlock::ToolCall(persisted_tool_call) = &output.content[0] else {
        panic!("Expected toolCall block");
    };
    assert_eq!(
        JsonValue::Object(persisted_tool_call.arguments.clone()),
        json!({ "path": "README.md", "content": "updated" })
    );
    assert!(!has_partial_json(persisted_tool_call));

    stream.end(None);
    let emitted_events: Vec<AssistantMessageEvent> = stream.events().collect().await;
    let tool_call_end = emitted_events
        .iter()
        .find_map(|event| match event {
            AssistantMessageEvent::ToolCallEnd { tool_call, .. } => Some(tool_call),
            _ => None,
        })
        .expect("Expected toolcall_end event");
    assert_eq!(tool_call_end, persisted_tool_call);
    assert!(!has_partial_json(tool_call_end));
}
