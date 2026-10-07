//! Port of the `openai-responses-shared` cases of
//! `test/constrained-sampling.test.ts` (`convertResponsesTools`,
//! `convertResponsesMessages`, `processResponsesStream`).

use eukhe_pi_ai::api::openai_responses_shared::{
    convert_responses_messages, convert_responses_tools, process_responses_stream,
    ConvertResponsesMessagesOptions, ConvertResponsesToolsOptions, GrammarToolInputProperties,
    OpenAIResponsesStreamOptions,
};
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_pi_ai::utils::transcript::normalize_context;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, AssistantMessageEvent, Context, JsonValue, Model,
    StopReason, Tool,
};
use futures::StreamExt;
use serde_json::json;

fn make_model() -> Model {
    serde_json::from_value(json!({
        "id": "gpt-test",
        "name": "GPT Test",
        "api": "openai-responses",
        "provider": "openai",
        "baseUrl": "https://api.openai.com/v1",
        "reasoning": false,
        "input": ["text", "image"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 4096,
    }))
    .expect("model")
}

fn make_usage() -> JsonValue {
    json!({
        "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
    })
}

fn now() -> u64 {
    u64::try_from(
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap_or_default()
            .as_millis(),
    )
    .unwrap_or(u64::MAX)
}

fn make_output() -> AssistantMessage {
    serde_json::from_value(json!({
        "role": "assistant",
        "content": [],
        "api": "openai-responses",
        "provider": "openai",
        "model": "gpt-test",
        "usage": make_usage(),
        "stopReason": "pending",
        "timestamp": now(),
    }))
    .expect("output")
}

/// `makeTool(overrides)`: the default tool with `overrides` merged over it.
fn make_tool(overrides: &JsonValue) -> Tool {
    let mut tool = json!({
        "name": "sample_tool",
        "description": "Sample tool",
        "parameters": {
            "additionalProperties": false,
            "type": "object",
            "properties": { "payload": { "type": "string" } },
            "required": ["payload"],
        },
    });
    for (key, value) in overrides.as_object().expect("overrides") {
        tool[key] = value.clone();
    }
    serde_json::from_value(tool).expect("tool")
}

fn grammar_properties() -> GrammarToolInputProperties {
    [("sample_tool".to_owned(), "payload".to_owned())]
        .into_iter()
        .collect()
}

fn tools_options(
    supports_strict_mode: Option<bool>,
    supports_openai_grammar_tools: Option<bool>,
) -> ConvertResponsesToolsOptions {
    ConvertResponsesToolsOptions {
        supports_strict_mode,
        supports_openai_grammar_tools,
        ..ConvertResponsesToolsOptions::default()
    }
}

/// Vitest `toMatchObject`: objects match recursively by subset, arrays
/// element-wise with equal length, other values by equality.
fn assert_match_object(actual: &JsonValue, expected: &JsonValue) {
    assert!(
        matches_object(actual, expected),
        "expected {actual:#} to match {expected:#}"
    );
}

fn matches_object(actual: &JsonValue, expected: &JsonValue) -> bool {
    match (actual, expected) {
        (JsonValue::Object(actual), JsonValue::Object(expected)) => {
            expected.iter().all(|(key, value)| {
                actual
                    .get(key)
                    .is_some_and(|actual| matches_object(actual, value))
            })
        }
        (JsonValue::Array(actual), JsonValue::Array(expected)) => {
            actual.len() == expected.len()
                && actual
                    .iter()
                    .zip(expected)
                    .all(|(actual, expected)| matches_object(actual, expected))
        }
        _ => actual == expected,
    }
}

fn convert_error(tools: &[Tool], options: ConvertResponsesToolsOptions) -> String {
    convert_responses_tools(tools, &options)
        .expect_err("expected a throw")
        .to_string()
}

#[test]
fn converts_supported_constraints_and_falls_back_when_unsupported() {
    let prefer =
        make_tool(&json!({ "constrainedSampling": { "type": "json_schema", "strict": "prefer" } }));
    assert_match_object(
        &convert_responses_tools(&[prefer], &ConvertResponsesToolsOptions::default())
            .expect("tools")[0],
        &json!({ "type": "function", "name": "sample_tool", "strict": true }),
    );

    let require = make_tool(
        &json!({ "constrainedSampling": { "type": "json_schema", "strict": "require" } }),
    );
    assert!(convert_error(&[require], tools_options(Some(false), None))
        .contains(r#"Tool "sample_tool" requires JSON-schema constrained sampling"#));

    let grammar_tool = make_tool(&json!({
        "constrainedSampling": { "type": "grammar", "variants": { "openai_lark": "start: /[a-z]+/" } },
    }));
    assert_match_object(
        &convert_responses_tools(
            std::slice::from_ref(&grammar_tool),
            &tools_options(None, Some(true)),
        )
        .expect("tools")[0],
        &json!({
            "type": "custom",
            "name": "sample_tool",
            "format": { "type": "grammar", "syntax": "lark", "definition": "start: /[a-z]+/" },
        }),
    );
    let empty_variants =
        make_tool(&json!({ "constrainedSampling": { "type": "grammar", "variants": {} } }));
    assert!(
        convert_error(&[empty_variants], tools_options(None, Some(true))).contains(
            r#"Tool "sample_tool" cannot use grammar constrained sampling: no supported grammar variant was provided"#
        )
    );

    let fallback =
        convert_responses_tools(&[grammar_tool], &tools_options(Some(false), Some(false)))
            .expect("tools")
            .remove(0);
    assert_match_object(
        &fallback,
        &json!({ "type": "function", "name": "sample_tool" }),
    );
    assert!(fallback.get("strict").is_none());

    assert_eq!(
        convert_responses_tools(
            &[make_tool(&json!({ "constrainedSampling": false }))],
            &ConvertResponsesToolsOptions::default(),
        )
        .expect("tools"),
        convert_responses_tools(
            &[make_tool(&json!({}))],
            &ConvertResponsesToolsOptions::default()
        )
        .expect("tools"),
    );
}

/// Only the `convertResponsesTools` assertions of the TS case; the
/// `makeStrictJsonSchema` / `resolveJsonSchemaStrictSampling` ones belong to
/// the constrained-sampling port.
#[test]
fn falls_back_or_rejects_schemas_that_cannot_be_safely_converted() {
    let cases = [
        json!({
            "type": "object",
            "properties": {
                "metadata": {
                    "additionalProperties": { "type": "string" },
                    "type": "object",
                    "properties": {},
                },
            },
            "required": ["metadata"],
        }),
        json!({
            "allOf": [
                { "type": "object", "properties": { "a": { "type": "string" } }, "required": ["a"] },
                { "type": "object", "properties": { "b": { "type": "number" } }, "required": ["b"] },
            ],
        }),
        json!({
            "type": "object",
            "properties": {
                "value": {
                    "anyOf": [
                        { "type": "object", "properties": { "nested": { "type": "string" } }, "required": ["nested"] },
                        { "type": "null" },
                    ],
                },
            },
            "required": ["value"],
        }),
        json!({
            "type": "object",
            "properties": { "child": { "$ref": "https://example.com/child.json" } },
            "required": ["child"],
        }),
    ];

    for parameters in cases {
        let tool = make_tool(&json!({
            "parameters": parameters,
            "constrainedSampling": { "type": "json_schema", "strict": "prefer" },
        }));
        assert_match_object(
            &convert_responses_tools(&[tool], &tools_options(Some(true), None)).expect("tools")[0],
            &json!({ "strict": false, "parameters": parameters }),
        );
    }
}

fn replay_context(
    replayed_tool_call: &JsonValue,
    api: &str,
    provider: &str,
    model: &str,
) -> Context {
    serde_json::from_value(json!({
        "messages": [
            {
                "role": "assistant",
                "api": api,
                "provider": provider,
                "model": model,
                "content": [replayed_tool_call],
                "usage": make_usage(),
                "stopReason": "toolUse",
                "timestamp": now(),
            },
            {
                "role": "toolResult",
                "toolCallId": "call_1|ctc_1",
                "toolName": "sample_tool",
                "content": [{ "type": "text", "text": "done" }],
                "isError": false,
                "timestamp": now(),
            },
        ],
    }))
    .expect("context")
}

fn grammar_messages_options() -> ConvertResponsesMessagesOptions {
    ConvertResponsesMessagesOptions {
        grammar_tool_input_properties: Some(grammar_properties()),
        ..ConvertResponsesMessagesOptions::default()
    }
}

#[test]
fn replays_grammar_calls_as_custom_responses_items() {
    let tool_call = |arguments: JsonValue| json!({ "type": "toolCall", "id": "call_1|ctc_1", "name": "sample_tool", "arguments": arguments });
    for invalid_arguments in [json!({}), json!({ "payload": 42 })] {
        let context = normalize_context(replay_context(
            &tool_call(invalid_arguments),
            "openai-responses",
            "openai",
            "gpt-test",
        ));
        let error = convert_responses_messages(
            &make_model(),
            &context,
            &["openai"],
            &grammar_messages_options(),
        )
        .expect_err("expected a throw")
        .to_string();
        assert!(
            error.contains(
                r#"Grammar tool call "sample_tool" requires argument "payload" to be a string"#
            ),
            "{error}"
        );
    }

    let context = normalize_context(replay_context(
        &tool_call(json!({ "payload": "abc" })),
        "openai-responses",
        "openai",
        "gpt-test",
    ));
    let messages = convert_responses_messages(
        &make_model(),
        &context,
        &["openai"],
        &grammar_messages_options(),
    )
    .expect("messages");

    assert!(messages.contains(&json!({
        "type": "custom_tool_call",
        "id": "ctc_1",
        "call_id": "call_1",
        "name": "sample_tool",
        "input": "abc",
    })));
    assert!(messages.contains(&json!({
        "type": "custom_tool_call_output",
        "call_id": "call_1",
        "output": "done",
    })));
}

// earendil-works/radius#115: a gateway forwards another model's history as a foreign provider.
#[test]
fn drops_foreign_item_ids_when_replaying_grammar_calls_as_custom_responses_items() {
    let context = normalize_context(replay_context(
        &json!({ "type": "toolCall", "id": "call_1|ctc_1", "name": "sample_tool", "arguments": { "payload": "abc" } }),
        "pi-messages",
        "radius",
        "gpt-other",
    ));

    let messages = convert_responses_messages(
        &make_model(),
        &context,
        &["openai"],
        &grammar_messages_options(),
    )
    .expect("messages");

    let call = messages
        .iter()
        .find(|item| item["type"] == "custom_tool_call")
        .expect("custom_tool_call");
    assert_match_object(
        call,
        &json!({ "type": "custom_tool_call", "call_id": "call_1", "input": "abc" }),
    );
    assert!(call.get("id").is_none());
}

#[tokio::test]
async fn starts_custom_responses_tool_calls_with_their_initial_input() {
    let mut output = make_output();
    let stream = AssistantMessageEventStream::new();
    let events = vec![
        json!({
            "type": "response.output_item.added",
            "output_index": 0,
            "item": { "type": "custom_tool_call", "call_id": "call_1", "id": "ctc_1", "name": "sample_tool", "input": "a" },
        }),
        json!({
            "type": "response.custom_tool_call_input.delta",
            "output_index": 0,
            "item_id": "ctc_1",
            "delta": "b",
        }),
        json!({
            "type": "response.custom_tool_call_input.done",
            "output_index": 0,
            "item_id": "ctc_1",
            "input": "abc",
        }),
        json!({
            "type": "response.output_item.done",
            "output_index": 0,
            "item": { "type": "custom_tool_call", "call_id": "call_1", "id": "ctc_1", "name": "sample_tool", "input": "abc" },
        }),
        json!({
            "type": "response.completed",
            "response": { "status": "completed", "usage": { "input_tokens": 1, "output_tokens": 1, "total_tokens": 2 } },
        }),
    ];

    process_responses_stream(
        futures::stream::iter(events.into_iter().map(Ok)),
        &mut output,
        &stream,
        &make_model(),
        &OpenAIResponsesStreamOptions {
            grammar_tool_input_properties: Some(grammar_properties()),
            ..OpenAIResponsesStreamOptions::default()
        },
    )
    .await
    .expect("process");
    stream.end(None);

    // TS `captureToolCallEvents`: argument snapshots at `toolcall_start` and
    // the `toolcall_delta` deltas.
    let mut starts: Vec<JsonValue> = Vec::new();
    let mut deltas: Vec<String> = Vec::new();
    let pushed: Vec<AssistantMessageEvent> = stream.events().collect().await;
    for event in pushed {
        match event {
            AssistantMessageEvent::ToolCallStart {
                content_index,
                partial,
            } => {
                if let Some(AssistantContentBlock::ToolCall(block)) =
                    partial.content.get(content_index)
                {
                    starts.push(JsonValue::Object(block.arguments.clone()));
                }
            }
            AssistantMessageEvent::ToolCallDelta { delta, .. } => deltas.push(delta),
            _ => {}
        }
    }

    assert_eq!(output.stop_reason, StopReason::ToolUse);
    assert_eq!(starts, vec![json!({ "payload": "a" })]);
    assert_eq!(
        serde_json::to_value(&output.content).expect("content"),
        json!([{ "type": "toolCall", "id": "call_1|ctc_1", "name": "sample_tool", "arguments": { "payload": "abc" } }])
    );
    let joined: JsonValue = serde_json::from_str(&deltas.concat()).expect("deltas JSON");
    assert_eq!(joined, json!({ "payload": "abc" }));
}
