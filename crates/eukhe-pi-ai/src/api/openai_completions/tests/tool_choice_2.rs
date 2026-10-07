//! Port of `openai-completions-tool-choice.test.ts`, second half (from
//! "ignores empty custom objects on function tool call deltas"); helpers
//! live in `tool_choice.rs`.

use std::collections::BTreeMap;

use serde_json::json;

use super::super::compat::ResolvedCompat;
use super::super::convert::{convert_messages, ConvertCompletionsMessagesOptions};
use super::support::context;
use super::tool_choice::{
    assert_match_object, catalog_model, compat_json, completions_model, ctx, local_model,
    provider_payload, run_simple, simple_options, simple_payload, simple_reasoning, zero_usage,
};
use crate::types::{
    AssistantMessageEvent, CacheRetention, IndexMap, JsonValue, MaxTokensField,
    SessionAffinityFormat, SimpleStreamOptions, StopReason, StreamOptions, ThinkingFormat,
    ThinkingLevel,
};

fn event_json(event: &AssistantMessageEvent) -> JsonValue {
    serde_json::to_value(event).expect("serialize event")
}

fn is_tool_call_event(event_type: &str) -> bool {
    matches!(
        event_type,
        "toolcall_start" | "toolcall_delta" | "toolcall_end"
    )
}

fn content_json(content: &[crate::types::AssistantContentBlock]) -> Vec<JsonValue> {
    content
        .iter()
        .map(|block| serde_json::to_value(block).expect("serialize content block"))
        .collect()
}

/// `toolCall` has no TS scratch fields (`streamIndex`, `partialArgs`).
fn assert_no_scratch_fields(tool_call: &JsonValue) {
    assert!(tool_call.get("streamIndex").is_none(), "{tool_call}");
    assert!(tool_call.get("partialArgs").is_none(), "{tool_call}");
}

#[tokio::test]
async fn ignores_empty_custom_objects_on_function_tool_call_deltas() {
    let chunks = vec![json!({
        "id": "chatcmpl-empty-custom",
        "choices": [{
            "delta": {
                "tool_calls": [{
                    "index": 0,
                    "id": "call_1",
                    "type": "function",
                    "function": { "name": "read", "arguments": "{\"path\":\"README.md\"}" },
                    "custom": {},
                }],
            },
            "finish_reason": "tool_calls",
        }],
    })];
    let model = completions_model("openai", "gpt-4o-mini", &json!({}));
    let tools = json!([{
        "name": "read",
        "description": "Read a file",
        "parameters": {
            "type": "object",
            "properties": { "path": { "type": "string" } },
            "required": ["path"],
        },
    }]);
    let (_, _, response) = run_simple(
        &model,
        &ctx("Read README.md", Some(tools), None),
        simple_options(),
        chunks,
    )
    .await;

    assert_eq!(
        content_json(&response.content),
        vec![json!({
            "type": "toolCall",
            "id": "call_1",
            "name": "read",
            "arguments": { "path": "README.md" },
        })]
    );
}

#[tokio::test]
async fn coalesces_tool_call_deltas_by_stable_index_when_provider_mutates_ids_mid_stream() {
    let tool_call_chunk = |id: &str, name: JsonValue, arguments: &str, finish: JsonValue| {
        json!({
            "id": "chatcmpl-kimi-bad-stream",
            "choices": [{
                "delta": {
                    "tool_calls": [{
                        "index": 0,
                        "id": id,
                        "type": "function",
                        "function": { "name": name, "arguments": arguments },
                    }],
                },
                "finish_reason": finish,
            }],
        })
    };
    let mut last = tool_call_chunk(
        "chatcmpl-tool-b",
        JsonValue::Null,
        ".md\"}",
        json!("tool_calls"),
    );
    last["usage"] = json!({
        "prompt_tokens": 10,
        "completion_tokens": 5,
        "prompt_tokens_details": { "cached_tokens": 0 },
        "completion_tokens_details": { "reasoning_tokens": 0 },
    });
    let chunks = vec![
        tool_call_chunk("functions.read:0", json!("read"), "", JsonValue::Null),
        tool_call_chunk(
            "chatcmpl-tool-a",
            JsonValue::Null,
            "{\"path\":\"README",
            JsonValue::Null,
        ),
        last,
    ];
    let model = completions_model("openai", "gpt-4o-mini", &json!({}));
    let tools = json!([{
        "name": "read",
        "description": "Read a file",
        "parameters": {
            "type": "object",
            "properties": { "path": { "type": "string" } },
            "required": ["path"],
        },
    }]);
    let (_, events, response) = run_simple(
        &model,
        &ctx("Read README.md", Some(tools), None),
        simple_options(),
        chunks,
    )
    .await;

    let tool_call_content_indexes: Vec<JsonValue> = events
        .iter()
        .map(event_json)
        .filter(|event| event["type"].as_str().is_some_and(is_tool_call_event))
        .map(|event| event["contentIndex"].clone())
        .collect();

    assert_eq!(response.stop_reason, StopReason::ToolUse);
    assert_eq!(tool_call_content_indexes, vec![json!(0); 5]);
    let content = content_json(&response.content);
    assert_eq!(content.len(), 1);
    let tool_call = &content[0];
    assert_eq!(tool_call["type"], json!("toolCall"));
    assert_eq!(tool_call["id"], json!("functions.read:0"));
    assert_eq!(tool_call["name"], json!("read"));
    assert_eq!(tool_call["arguments"], json!({ "path": "README.md" }));
    assert_no_scratch_fields(tool_call);
}

// The TS case is one long fixture plus one whole-message assertion.
#[allow(clippy::too_many_lines)]
#[tokio::test]
async fn accumulates_mixed_content_reasoning_and_parallel_tool_call_deltas_independently() {
    let chunks = vec![
        json!({
            "id": "chatcmpl-mixed-deltas",
            "choices": [{
                "delta": {
                    "content": "answer 1",
                    "reasoning_content": "think 1",
                    "tool_calls": [
                        {
                            "index": 0,
                            "id": "tc_read_initial",
                            "type": "function",
                            "function": { "name": "read", "arguments": "{\"path\":\"README" },
                        },
                        {
                            "index": 1,
                            "id": "tc_grep_initial",
                            "type": "function",
                            "function": { "name": "grep", "arguments": "{\"pattern\":\"TODO" },
                        },
                        {
                            "id": "tc_list_no_index",
                            "type": "function",
                            "function": { "name": "list", "arguments": "{\"path\":\"packages" },
                        },
                        {
                            "id": "tc_write_no_index",
                            "type": "function",
                            "function": { "name": "write", "arguments": "{\"path\":\"out" },
                        },
                    ],
                },
                "finish_reason": null,
            }],
        }),
        json!({
            "id": "chatcmpl-mixed-deltas",
            "choices": [{
                "delta": {
                    "content": " answer 2",
                    "tool_calls": [
                        {
                            "index": 1,
                            "id": "tc_grep_changed",
                            "type": "function",
                            "function": { "arguments": "\",\"path\":\"src" },
                        },
                        {
                            "id": "tc_write_no_index",
                            "type": "function",
                            "function": { "arguments": ".txt\",\"content\":\"ok\"}" },
                        },
                        {
                            "id": "tc_list_no_index",
                            "type": "function",
                            "function": { "arguments": "/ai\"}" },
                        },
                    ],
                },
                "finish_reason": null,
            }],
        }),
        json!({
            "id": "chatcmpl-mixed-deltas",
            "choices": [{
                "delta": {
                    "content": "\n",
                    "reasoning_content": " think 2",
                    "tool_calls": [
                        {
                            "index": 0,
                            "id": "tc_read_changed",
                            "type": "function",
                            "function": { "arguments": ".md\"}" },
                        },
                        { "index": 1, "type": "function", "function": { "arguments": "\"}" } },
                    ],
                },
                "finish_reason": "tool_calls",
            }],
            "usage": {
                "prompt_tokens": 10,
                "completion_tokens": 8,
                "prompt_tokens_details": { "cached_tokens": 0 },
                "completion_tokens_details": { "reasoning_tokens": 2 },
            },
        }),
    ];
    let model = completions_model("openai", "gpt-4o-mini", &json!({}));
    let string_tool = |name: &str, description: &str, fields: &[&str]| {
        let properties: serde_json::Map<String, JsonValue> = fields
            .iter()
            .map(|field| ((*field).to_owned(), json!({ "type": "string" })))
            .collect();
        json!({
            "name": name,
            "description": description,
            "parameters": { "type": "object", "properties": properties, "required": fields },
        })
    };
    let tools = json!([
        string_tool("read", "Read a file", &["path"]),
        string_tool("grep", "Search a file", &["pattern", "path"]),
        string_tool("list", "List a directory", &["path"]),
        string_tool("write", "Write a file", &["path", "content"]),
    ]);
    let (_, events, response) = run_simple(
        &model,
        &ctx("Think, answer, and use tools.", Some(tools), None),
        simple_options(),
        chunks,
    )
    .await;

    let mut event_types: Vec<String> = Vec::new();
    let mut tool_events_by_content_index: BTreeMap<u64, Vec<String>> = BTreeMap::new();
    for event in events.iter().map(event_json) {
        let event_type = event["type"].as_str().expect("event type").to_owned();
        if is_tool_call_event(&event_type) {
            let index = event["contentIndex"].as_u64().expect("contentIndex");
            tool_events_by_content_index
                .entry(index)
                .or_default()
                .push(event_type.clone());
        }
        event_types.push(event_type);
    }
    let count = |name: &str| {
        event_types
            .iter()
            .filter(|event_type| *event_type == name)
            .count()
    };

    assert_eq!(response.stop_reason, StopReason::ToolUse);
    assert_eq!(count("text_start"), 1);
    assert_eq!(count("text_delta"), 3);
    assert_eq!(count("text_end"), 1);
    assert_eq!(count("thinking_start"), 1);
    assert_eq!(count("thinking_delta"), 2);
    assert_eq!(count("thinking_end"), 1);
    assert_eq!(count("toolcall_start"), 4);
    assert_eq!(count("toolcall_delta"), 9);
    assert_eq!(count("toolcall_end"), 4);
    let sequence = |deltas: usize| {
        let mut sequence = vec!["toolcall_start".to_owned()];
        sequence.extend(std::iter::repeat_n("toolcall_delta".to_owned(), deltas));
        sequence.push("toolcall_end".to_owned());
        sequence
    };
    assert_eq!(tool_events_by_content_index.get(&2), Some(&sequence(2)));
    assert_eq!(tool_events_by_content_index.get(&3), Some(&sequence(3)));
    assert_eq!(tool_events_by_content_index.get(&4), Some(&sequence(2)));
    assert_eq!(tool_events_by_content_index.get(&5), Some(&sequence(2)));

    let content = content_json(&response.content);
    assert_eq!(content.len(), 6);
    assert_eq!(
        content[0],
        json!({ "type": "text", "text": "answer 1 answer 2\n" })
    );
    assert_eq!(
        content[1],
        json!({ "type": "thinking", "thinking": "think 1 think 2", "thinkingSignature": "reasoning_content" })
    );
    let expected_calls = [
        ("tc_read_initial", "read", json!({ "path": "README.md" })),
        (
            "tc_grep_initial",
            "grep",
            json!({ "pattern": "TODO", "path": "src" }),
        ),
        ("tc_list_no_index", "list", json!({ "path": "packages/ai" })),
        (
            "tc_write_no_index",
            "write",
            json!({ "path": "out.txt", "content": "ok" }),
        ),
    ];
    for (call, (id, name, arguments)) in content[2..].iter().zip(expected_calls) {
        assert_eq!(call["type"], json!("toolCall"));
        assert_eq!(call["id"], json!(id));
        assert_eq!(call["name"], json!(name));
        assert_eq!(call["arguments"], arguments);
        assert_no_scratch_fields(call);
    }
}

#[tokio::test]
async fn uses_system_messages_for_non_openai_anthropic_openrouter_reasoning_model_instructions() {
    let model = catalog_model("openrouter", "deepseek/deepseek-v4-pro");
    let params = simple_payload(
        &model,
        &ctx("Hi", None, Some("Follow instructions.")),
        simple_options(),
    )
    .await;

    assert_eq!(params["messages"][0]["role"], json!("system"));
}

#[tokio::test]
async fn keeps_developer_messages_for_openai_and_anthropic_openrouter_batch_instructions() {
    for id in ["openai/gpt-5.2-codex", "anthropic/claude-fable-5.1:batch"] {
        let model = catalog_model("openrouter", id);
        let params = simple_payload(
            &model,
            &ctx("Hi", None, Some("Follow instructions.")),
            simple_options(),
        )
        .await;

        assert_eq!(params["messages"][0]["role"], json!("developer"), "{id}");
    }
}

#[tokio::test]
async fn keeps_developer_messages_for_openai_reasoning_model_instructions() {
    let model = completions_model("openai", "gpt-5.5", &json!({}));
    let params = simple_payload(
        &model,
        &ctx("Hi", None, Some("Follow instructions.")),
        simple_options(),
    )
    .await;

    assert_eq!(params["messages"][0]["role"], json!("developer"));
}

#[test]
fn stores_openrouter_kimi_k2_6_reasoning_replay_compat_in_built_in_metadata() {
    // `:free` variant delisted from the OpenRouter API; the generator override
    // matches any `moonshotai/kimi-k2.6*` variant that is listed.
    let compat = compat_json(&catalog_model("openrouter", "moonshotai/kimi-k2.6"));
    assert_eq!(compat["supportsDeveloperRole"], json!(false));
    assert_eq!(
        compat["requiresReasoningContentOnAssistantMessages"],
        json!(true)
    );
}

#[test]
fn stores_xiaomi_mimo_reasoning_replay_compat_in_built_in_metadata() {
    for provider in [
        "xiaomi",
        "xiaomi-token-plan-cn",
        "xiaomi-token-plan-ams",
        "xiaomi-token-plan-sgp",
    ] {
        let compat = compat_json(&catalog_model(provider, "mimo-v2.5-pro"));
        assert_eq!(
            compat["requiresReasoningContentOnAssistantMessages"],
            json!(true),
            "{provider}"
        );
        assert_eq!(compat["thinkingFormat"], json!("deepseek"), "{provider}");
        assert!(compat.get("maxTokensField").is_none(), "{provider}");
        assert!(compat.get("supportsDeveloperRole").is_none(), "{provider}");
    }
}

#[test]
fn stores_qwen_token_plan_reasoning_replay_compat_in_built_in_metadata() {
    for provider in [
        "qwen-token-plan",
        "qwen-token-plan-cn",
        "qwen-token-plan-individual",
    ] {
        let compat = compat_json(&catalog_model(provider, "qwen3.7-max"));
        assert_eq!(compat["thinkingFormat"], json!("qwen"), "{provider}");
        assert!(
            compat
                .get("requiresReasoningContentOnAssistantMessages")
                .is_none(),
            "{provider}"
        );
        assert_eq!(compat["supportsDeveloperRole"], json!(false), "{provider}");
        assert_eq!(compat["supportsStore"], json!(false), "{provider}");
    }
}

#[tokio::test]
async fn replays_xiaomi_mimo_assistant_tool_calls_with_empty_reasoning_content_when_thinking_is_missing(
) {
    let model = catalog_model("xiaomi", "mimo-v2.5-pro");
    let context = context(json!({
        "messages": [
            { "role": "user", "content": "Read README.md", "timestamp": 1 },
            {
                "role": "assistant",
                "api": "openai-completions",
                "provider": "xiaomi",
                "model": "mimo-v2.5-pro",
                "content": [
                    { "type": "toolCall", "id": "call_1", "name": "read", "arguments": { "path": "README.md" } },
                ],
                "usage": zero_usage(),
                "stopReason": "toolUse",
                "timestamp": 1,
            },
            {
                "role": "toolResult",
                "toolCallId": "call_1",
                "toolName": "read",
                "content": [{ "type": "text", "text": "contents" }],
                "isError": false,
                "timestamp": 1,
            },
        ],
    }));
    let params = simple_payload(&model, &context, simple_reasoning(ThinkingLevel::High)).await;

    let replayed_assistant = params["messages"]
        .as_array()
        .expect("messages")
        .iter()
        .find(|message| message["role"] == "assistant")
        .expect("replayed assistant");
    assert_match_object(
        replayed_assistant,
        &json!({ "role": "assistant", "reasoning_content": "" }),
    );
    assert_eq!(params["thinking"], json!({ "type": "enabled" }));
    assert_eq!(params["reasoning_effort"], json!("high"));
}

#[tokio::test]
async fn normalizes_opencode_go_reasoning_deltas_to_reasoning_content_for_replay() {
    let chunks = vec![json!({
        "id": "chatcmpl-opencode-go-reasoning",
        "choices": [{ "delta": { "reasoning": "think" }, "finish_reason": "stop" }],
    })];
    let model = completions_model("opencode-go", "kimi-k3", &json!({}));
    let (_, _, response) = run_simple(
        &model,
        &ctx("Use reasoning.", None, None),
        simple_options(),
        chunks,
    )
    .await;

    assert_eq!(
        content_json(&response.content),
        vec![
            json!({ "type": "thinking", "thinking": "think", "thinkingSignature": "reasoning_content" })
        ]
    );
}

#[tokio::test]
async fn keeps_non_opencode_go_reasoning_deltas_on_the_original_reasoning_field() {
    let chunks = vec![json!({
        "id": "chatcmpl-reasoning",
        "choices": [{ "delta": { "reasoning": "think" }, "finish_reason": "stop" }],
    })];
    let model = completions_model("openai", "gpt-4o-mini", &json!({}));
    let (_, _, response) = run_simple(
        &model,
        &ctx("Use reasoning.", None, None),
        simple_options(),
        chunks,
    )
    .await;

    assert_eq!(
        content_json(&response.content),
        vec![json!({ "type": "thinking", "thinking": "think", "thinkingSignature": "reasoning" })]
    );
}

#[test]
fn replays_opencode_go_reasoning_thinking_blocks_as_reasoning_content() {
    let model = completions_model("opencode-go", "kimi-k3", &json!({}));
    // TS spreads `model.compat` (absent here) under an explicit full record.
    let compat = ResolvedCompat {
        supports_store: false,
        supports_developer_role: false,
        supports_reasoning_effort: true,
        supports_usage_in_streaming: true,
        supports_finish_reason: true,
        max_tokens_field: MaxTokensField::MaxCompletionTokens,
        requires_tool_result_name: false,
        requires_assistant_after_tool_result: false,
        requires_thinking_as_text: false,
        requires_reasoning_content_on_assistant_messages: false,
        thinking_format: ThinkingFormat::OpenAI,
        chat_template_kwargs: IndexMap::new(),
        chat_template_args: IndexMap::new(),
        zai_tool_stream: false,
        supports_thinking_token_budget: None,
        thinking_token_budget_field: None,
        supports_strict_mode: true,
        supports_openai_grammar_tools: false,
        supports_mid_convo_system_messages: None,
        supports_mid_convo_tool_additions: None,
        cache_control_format: None,
        send_session_affinity_headers: false,
        session_affinity_format: SessionAffinityFormat::OpenAI,
        supports_long_cache_retention: true,
        vllm_priority: None,
    };
    let transcript = context(json!({
        "messages": [{
            "role": "assistant",
            "api": "openai-completions",
            "provider": "opencode-go",
            "model": "kimi-k3",
            "content": [
                { "type": "thinking", "thinking": "think", "thinkingSignature": "reasoning" },
                { "type": "toolCall", "id": "call_1", "name": "read", "arguments": { "path": "README.md" } },
            ],
            "usage": zero_usage(),
            "stopReason": "stop",
            "timestamp": 1,
        }],
    }));
    let messages = convert_messages(
        &model,
        &transcript,
        &compat,
        &ConvertCompletionsMessagesOptions::default(),
    )
    .expect("convert messages");

    assert_match_object(
        &messages[0],
        &json!({ "role": "assistant", "reasoning_content": "think" }),
    );
    assert!(messages[0].get("reasoning").is_none());
}

#[tokio::test]
async fn sends_thinking_disabled_for_opencode_kimi_k2_6_when_thinking_is_off() {
    let model = catalog_model("opencode", "kimi-k2.6");
    let params = simple_payload(&model, &ctx("Hi", None, None), simple_options()).await;

    assert_eq!(params["thinking"], json!({ "type": "disabled" }));
    assert!(params.get("reasoning_effort").is_none());
}

#[tokio::test]
async fn sends_thinking_enabled_for_opencode_kimi_k2_6_when_thinking_is_enabled() {
    let model = catalog_model("opencode", "kimi-k2.6");
    let params = simple_payload(
        &model,
        &ctx("Hi", None, None),
        simple_reasoning(ThinkingLevel::High),
    )
    .await;

    assert_eq!(params["thinking"], json!({ "type": "enabled" }));
    assert!(params.get("reasoning_effort").is_none());
}

#[tokio::test]
async fn omits_disabled_thinking_for_moonshot_kimi_k2_7_code_models() {
    for provider in ["moonshotai", "moonshotai-cn"] {
        let model = catalog_model(provider, "kimi-k2.7-code");
        let params = simple_payload(&model, &ctx("Hi", None, None), simple_options()).await;

        assert!(params.get("thinking").is_none(), "{provider}");
        assert!(params.get("reasoning_effort").is_none(), "{provider}");
    }
}

#[tokio::test]
async fn keeps_disabled_thinking_for_moonshot_kimi_k2_6_when_thinking_is_off() {
    let model = catalog_model("moonshotai-cn", "kimi-k2.6");
    let params = simple_payload(&model, &ctx("Hi", None, None), simple_options()).await;

    assert_eq!(params["thinking"], json!({ "type": "disabled" }));
    assert!(params.get("reasoning_effort").is_none());
}

/// `{ apiKey: "test", maxTokens: 123 }` simple options.
fn max_tokens_options() -> SimpleStreamOptions {
    let mut options = simple_options();
    options.stream.max_tokens = Some(123);
    options
}

async fn assert_sends_max_tokens(model: &crate::types::Model) {
    let params = simple_payload(model, &ctx("Hi", None, None), max_tokens_options()).await;

    assert_eq!(params["max_tokens"], json!(123), "{}", model.id);
    assert!(
        params.get("max_completion_tokens").is_none(),
        "{}",
        model.id
    );
}

#[tokio::test]
async fn sends_max_tokens_for_opencode_completions_models() {
    for model in [
        catalog_model("opencode-go", "kimi-k3"),
        catalog_model("opencode", "kimi-k2.6"),
    ] {
        assert_eq!(compat_json(&model)["maxTokensField"], json!("max_tokens"));
        assert_sends_max_tokens(&model).await;
    }
}

#[tokio::test]
async fn sends_max_tokens_for_built_in_and_custom_deepseek_api_models() {
    let custom_model = local_model(&json!({
        "id": "custom-deepseek-model",
        "name": "Custom DeepSeek Model",
        "provider": "custom-deepseek",
        "baseUrl": "https://api.deepseek.com",
    }));
    let custom_uppercase_model = local_model(&json!({
        "id": "custom-uppercase-deepseek-model",
        "name": "Custom Uppercase DeepSeek Model",
        "provider": "custom-deepseek",
        "baseUrl": "https://API.DeepSeek.COM",
    }));
    let native_models = [
        catalog_model("deepseek", "deepseek-flash"),
        catalog_model("deepseek", "deepseek-v4-pro"),
    ];

    for model in &native_models {
        assert_eq!(compat_json(model)["maxTokensField"], json!("max_tokens"));
    }

    for model in native_models
        .iter()
        .chain([&custom_model, &custom_uppercase_model])
    {
        assert_sends_max_tokens(model).await;
    }
}

#[tokio::test]
async fn sends_max_tokens_for_z_ai_completions_models() {
    for model in [
        catalog_model("zai", "glm-5-turbo"),
        catalog_model("zai", "glm-5.2"),
    ] {
        assert_eq!(compat_json(&model)["maxTokensField"], json!("max_tokens"));
        assert_sends_max_tokens(&model).await;
    }
}

/// The catalog model uses `openai-responses`; TS `streamSimple` (compat.ts)
/// routes it there, so this case goes through the top-level router.
#[tokio::test]
async fn omits_reasoning_effort_for_opencode_grok_build() {
    let model = catalog_model("opencode", "grok-build-0.1");
    let (fetch, _requests) = super::support::sse_fetch(super::support::stop_chunks());
    let (hook, seen) = super::support::payload_recorder();
    let mut options = simple_reasoning(ThinkingLevel::High);
    options.stream.request.fetch = Some(fetch);
    options.stream.request.on_payload = Some(hook);
    let context: crate::types::Context = serde_json::from_value(
        json!({ "messages": [{ "role": "user", "content": "Hi", "timestamp": 1 }] }),
    )
    .expect("valid context JSON");
    let message = crate::compat::stream_simple(&model, context, options)
        .expect("stream_simple")
        .result()
        .await;
    let params = seen
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .last()
        .cloned()
        .unwrap_or_else(|| panic!("no payload was built: {:?}", message.error_message));

    assert!(params.get("reasoning_effort").is_none());
}

#[tokio::test]
async fn does_not_double_count_reasoning_tokens_in_completion_usage() {
    let chunks = vec![json!({
        "id": "chatcmpl-reasoning-usage",
        "choices": [{ "delta": {}, "finish_reason": "stop" }],
        "usage": {
            "prompt_tokens": 10,
            "completion_tokens": 33,
            "prompt_tokens_details": { "cached_tokens": 0 },
            "completion_tokens_details": { "reasoning_tokens": 21 },
        },
    })];
    let model = completions_model("openai", "gpt-4o-mini", &json!({}));
    let (_, _, response) = run_simple(
        &model,
        &ctx("Use reasoning.", None, None),
        simple_options(),
        chunks,
    )
    .await;

    assert_eq!(response.usage.input, 10);
    assert_eq!(response.usage.output, 33);
    assert_eq!(response.usage.total_tokens, 43);
}

fn cache_usage() -> JsonValue {
    json!({
        "prompt_tokens": 100,
        "completion_tokens": 5,
        "prompt_tokens_details": { "cached_tokens": 50, "cache_write_tokens": 30 },
        "completion_tokens_details": { "reasoning_tokens": 0 },
    })
}

#[tokio::test]
async fn preserves_prompt_tokens_details_cache_read_write_fields_from_chunk_usage() {
    let chunks = vec![
        json!({ "id": "chatcmpl-cache-write", "choices": [{ "delta": { "content": "OK" }, "finish_reason": null }] }),
        json!({
            "id": "chatcmpl-cache-write",
            "choices": [{ "delta": {}, "finish_reason": "stop" }],
            "usage": cache_usage(),
        }),
    ];
    let model = completions_model("openai", "gpt-4o-mini", &json!({}));
    let (_, _, response) = run_simple(
        &model,
        &ctx("Reply with exactly OK", None, None),
        simple_options(),
        chunks,
    )
    .await;

    // cached_tokens is documented as cache reads; cache_write_tokens is separate.
    assert_eq!(response.usage.input, 20);
    assert_eq!(response.usage.cache_read, 50);
    assert_eq!(response.usage.cache_write, 30);
    assert_eq!(response.usage.total_tokens, 105);
}

#[tokio::test]
async fn preserves_prompt_tokens_details_cache_read_write_fields_from_choice_usage_fallback() {
    let chunks = vec![
        json!({
            "id": "chatcmpl-cache-write-choice",
            "choices": [{ "delta": { "content": "OK" }, "finish_reason": null }],
        }),
        json!({
            "id": "chatcmpl-cache-write-choice",
            "choices": [{ "delta": {}, "finish_reason": "stop", "usage": cache_usage() }],
        }),
    ];
    let model = completions_model("openai", "gpt-4o-mini", &json!({}));
    let (_, _, response) = run_simple(
        &model,
        &ctx("Reply with exactly OK", None, None),
        simple_options(),
        chunks,
    )
    .await;

    // cached_tokens is documented as cache reads; cache_write_tokens is separate.
    assert_eq!(response.usage.input, 20);
    assert_eq!(response.usage.cache_read, 50);
    assert_eq!(response.usage.cache_write, 30);
    assert_eq!(response.usage.total_tokens, 105);
}

#[tokio::test]
async fn uses_openrouter_reasoning_object_instead_of_reasoning_effort() {
    let model = catalog_model("openrouter", "deepseek/deepseek-r1");
    let params = simple_payload(
        &model,
        &ctx("Hi", None, None),
        simple_reasoning(ThinkingLevel::High),
    )
    .await;

    assert_eq!(params["reasoning"], json!({ "effort": "high" }));
    assert!(params.get("reasoning_effort").is_none());
}

#[tokio::test]
async fn uses_ant_ling_compatibility_metadata() {
    let model = catalog_model("ant-ling", "Ring-2.6-1T");
    let compat = compat_json(&model);

    assert_match_object(
        &compat,
        &json!({
            "supportsStore": false,
            "supportsDeveloperRole": false,
            "supportsReasoningEffort": false,
            "maxTokensField": "max_tokens",
            "thinkingFormat": "ant-ling",
            "supportsLongCacheRetention": false,
        }),
    );
    assert_eq!(compat["supportsStrictMode"], json!(true));
    assert!(compat
        .get("requiresReasoningContentOnAssistantMessages")
        .is_none());

    let options = SimpleStreamOptions {
        stream: StreamOptions {
            max_tokens: Some(123),
            cache_retention: Some(CacheRetention::Long),
            session_id: Some("ant-ling-session".to_owned()),
            ..simple_options().stream
        },
        reasoning: Some(ThinkingLevel::High),
        ..SimpleStreamOptions::default()
    };
    let params = simple_payload(
        &model,
        &ctx("Hi", None, Some("Follow instructions.")),
        options,
    )
    .await;

    assert_eq!(params["max_tokens"], json!(123));
    assert!(params.get("max_completion_tokens").is_none());
    assert_eq!(params["messages"][0]["role"], json!("system"));
    assert_eq!(params["reasoning"], json!({ "effort": "high" }));
    assert!(params.get("reasoning_effort").is_none());
    assert!(params.get("store").is_none());
    assert!(params.get("prompt_cache_key").is_none());
    assert!(params.get("prompt_cache_retention").is_none());
}

#[tokio::test]
async fn omits_ant_ling_reasoning_for_unmapped_direct_reasoning_efforts_and_non_reasoning_models() {
    let ring = catalog_model("ant-ling", "Ring-2.6-1T");
    let params = provider_payload(
        &ring,
        &ctx("Hi", None, None),
        &json!({ "reasoningEffort": "medium" }),
    )
    .await;

    assert!(params.get("reasoning").is_none());

    let ling = catalog_model("ant-ling", "Ling-2.6-flash");
    let params = simple_payload(
        &ling,
        &ctx("Hi", None, None),
        simple_reasoning(ThinkingLevel::High),
    )
    .await;

    assert!(params.get("reasoning").is_none());
}
