use serde_json::json;

use super::*;

fn usage() -> Usage {
    Usage {
        input: 0,
        output: 0,
        cache_read: 0,
        cache_write: 0,
        cache_write_1h: None,
        reasoning: None,
        total_tokens: 0,
        cost: UsageCost::default(),
    }
}

#[test]
fn assistant_message_serializes_role_first_and_js_numbers() {
    let message = AssistantMessage {
        content: vec![
            AssistantContentBlock::Thinking(ThinkingContent {
                thinking: "reasoning".into(),
                thinking_signature: None,
                redacted: None,
            }),
            AssistantContentBlock::Text(TextContent::new("first")),
            AssistantContentBlock::ToolCall(ToolCall {
                id: "1".into(),
                name: "read".into(),
                arguments: JsonObject::new(),
                thought_signature: None,
                namespace: None,
            }),
        ],
        api: "openai-completions".into(),
        provider: "openai".into(),
        model: "m".into(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage {
            cost: UsageCost {
                input: 0.5,
                output: 1.0,
                ..UsageCost::default()
            },
            ..usage()
        },
        stop_reason: StopReason::ToolUse,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: 1,
    };
    let text = serde_json::to_string(&Message::Assistant(message.clone())).unwrap();
    assert_eq!(
        text,
        r#"{"role":"assistant","content":[{"type":"thinking","thinking":"reasoning"},{"type":"text","text":"first"},{"type":"toolCall","id":"1","name":"read","arguments":{}}],"api":"openai-completions","provider":"openai","model":"m","usage":{"input":0,"output":0,"cacheRead":0,"cacheWrite":0,"totalTokens":0,"cost":{"input":0.5,"output":1,"cacheRead":0,"cacheWrite":0,"total":0}},"stopReason":"toolUse","timestamp":1}"#
    );
    let parsed: Message = serde_json::from_str(&text).unwrap();
    assert_eq!(parsed, Message::Assistant(message));
}

#[test]
fn lax_message_content_reads_null_and_missing_as_empty() {
    let messages: Vec<Message> = serde_json::from_value(json!([
        { "role": "user", "content": null, "timestamp": 1 },
        {
            "role": "assistant", "content": null, "api": "openai-completions", "provider": "openai",
            "model": "test-model",
            "usage": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 } },
            "stopReason": "stop", "timestamp": 1
        },
        { "role": "toolResult", "toolCallId": "call_1", "toolName": "web_search", "isError": false, "timestamp": 1 }
    ]))
    .unwrap();
    let Message::User(user) = &messages[0] else {
        panic!("user")
    };
    assert_eq!(user.content, UserContent::Blocks(Vec::new()));
    let Message::Assistant(assistant) = &messages[1] else {
        panic!("assistant")
    };
    assert!(assistant.content.is_empty());
    let Message::ToolResult(result) = &messages[2] else {
        panic!("toolResult")
    };
    assert!(result.content.is_empty());
}

#[test]
fn tool_result_details_keep_explicit_null() {
    let value = json!({
        "role": "toolResult", "toolCallId": "call-1", "toolName": "read", "content": [],
        "details": null, "isError": false, "timestamp": 1
    });
    let message: Message = serde_json::from_value(value.clone()).unwrap();
    assert_eq!(serde_json::to_value(&message).unwrap(), value);
}

#[test]
fn system_message_round_trips_sections_and_tools() {
    let value = json!({
        "role": "system",
        "content": [{ "type": "text", "text": "base" }],
        "sections": { "a": "x", "b": null },
        "toolsAdded": [{ "name": "t", "description": "d", "parameters": { "type": "object" }, "constrainedSampling": false }],
        "toolsRemoved": [{ "name": "old" }],
        "timestamp": 0
    });
    let message: Message = serde_json::from_value(value.clone()).unwrap();
    let Message::System(system) = &message else {
        panic!("system")
    };
    assert_eq!(
        system.tools_added.as_ref().unwrap()[0].constrained_sampling,
        Some(ToolConstrainedSampling::Disabled)
    );
    assert_eq!(serde_json::to_value(&message).unwrap(), value);
}

#[test]
fn any_model_dispatches_on_type_and_compat_on_api() {
    let chat = json!({
        "id": "m", "name": "M", "api": "openai-responses", "provider": "openai", "baseUrl": "https://x",
        "input": ["text"], "cost": { "input": 1, "output": 2, "cacheRead": 0.1, "cacheWrite": 0 },
        "reasoning": true, "contextWindow": 10, "maxTokens": 5,
        "compat": { "supportsOpenAIGrammarTools": true }
    });
    let model: AnyModel = serde_json::from_value(chat.clone()).unwrap();
    let AnyModel::Chat(chat_model) = &model else {
        panic!("chat")
    };
    assert_eq!(
        chat_model
            .compat
            .as_ref()
            .and_then(ModelCompat::as_openai_responses),
        Some(&OpenAIResponsesCompat {
            supports_openai_grammar_tools: Some(true),
            ..OpenAIResponsesCompat::default()
        })
    );
    assert_eq!(serde_json::to_value(&model).unwrap(), chat);

    let image = json!({
        "type": "image", "id": "i", "name": "I", "api": "openrouter-images", "provider": "openrouter",
        "baseUrl": "https://x", "input": ["text"], "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "output": ["image", "text"]
    });
    let model: AnyModel = serde_json::from_value(image.clone()).unwrap();
    assert_eq!(model.model_type(), ModelType::Image);
    assert_eq!(serde_json::to_value(&model).unwrap(), image);

    let unknown = json!({ "type": "video" });
    assert!(serde_json::from_value::<AnyModel>(unknown).is_err());
}

#[test]
fn events_serialize_with_camel_case_fields() {
    let partial = AssistantMessage {
        content: Vec::new(),
        api: "a".into(),
        provider: "p".into(),
        model: "m".into(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: usage(),
        stop_reason: StopReason::Pending,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: 0,
    };
    let event = AssistantMessageEvent::TextDelta {
        content_index: 2,
        delta: "d".into(),
        partial,
    };
    let value = serde_json::to_value(&event).unwrap();
    assert_eq!(value["type"], "text_delta");
    assert_eq!(value["contentIndex"], 2);
    assert_eq!(value["partial"]["role"], "assistant");
    assert_eq!(
        serde_json::from_value::<AssistantMessageEvent>(value).unwrap(),
        event
    );
}

#[test]
fn chat_template_values_and_routing_round_trip() {
    let value = json!({
        "thinkingFormat": "chat-template",
        "chatTemplateKwargs": { "enable": { "$var": "thinking.enabled", "omitWhenOff": true }, "n": 1, "s": "x", "z": null },
        "openRouterRouting": { "allow_fallbacks": false, "sort": { "by": "price", "partition": null }, "max_price": { "prompt": "1", "completion": 2 } }
    });
    let compat: OpenAICompletionsCompat = serde_json::from_value(value.clone()).unwrap();
    assert_eq!(serde_json::to_value(&compat).unwrap(), value);
}
