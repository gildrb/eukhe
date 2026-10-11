//! Port of `openai-completions-tool-choice.test.ts`, first half (through
//! "accepts streams without `finish_reason` when compat disables it"); the
//! rest is in `tool_choice_2.rs`, which reuses the helpers below.
//!
//! TS `getModel(provider, id)` reads the generated catalogs
//! ([`catalog_model`]); `{ compat: _, ...getModel(...), api:
//! "openai-completions" }` is [`completions_model`]. TS `onPayload` captures
//! become [`simple_payload`]; the fake SDK's default chunk list is
//! [`default_chunks`].

use std::sync::PoisonError;

use serde_json::json;

use super::support::{collect, context, model, payload_recorder, sse_fetch};
use crate::api::openai_completions::{stream, stream_simple};
use crate::model_catalog::ChatModelCatalog;
use crate::providers::{
    ant_ling_models, deepseek_models, groq_models, moonshotai_cn_models, moonshotai_models,
    openai_models, opencode_go_models, opencode_models, openrouter_models,
    qwen_token_plan_cn_models, qwen_token_plan_individual_models, qwen_token_plan_models,
    xiaomi_models, xiaomi_token_plan_ams_models, xiaomi_token_plan_cn_models,
    xiaomi_token_plan_sgp_models, zai_coding_cn_models, zai_models,
};
use crate::types::{
    AssistantMessage, AssistantMessageEvent, JsonObject, JsonValue, Model, ProviderRequestOptions,
    ProviderStreamOptions, SimpleStreamOptions, StopReason, StreamOptions, ThinkingLevel,
    ToolChoice, TranscriptContext,
};

/// TS `getModel(provider, id)!` over the generated catalogs this file uses.
pub(super) fn catalog_model(provider: &str, id: &str) -> Model {
    let catalog: &ChatModelCatalog = match provider {
        "ant-ling" => &ant_ling_models::ANT_LING_MODELS,
        "deepseek" => &deepseek_models::DEEPSEEK_MODELS,
        "groq" => &groq_models::GROQ_MODELS,
        "moonshotai" => &moonshotai_models::MOONSHOTAI_MODELS,
        "moonshotai-cn" => &moonshotai_cn_models::MOONSHOTAI_CN_MODELS,
        "openai" => &openai_models::OPENAI_MODELS,
        "opencode" => &opencode_models::OPENCODE_MODELS,
        "opencode-go" => &opencode_go_models::OPENCODE_GO_MODELS,
        "openrouter" => &openrouter_models::OPENROUTER_MODELS,
        "qwen-token-plan" => &qwen_token_plan_models::QWEN_TOKEN_PLAN_MODELS,
        "qwen-token-plan-cn" => &qwen_token_plan_cn_models::QWEN_TOKEN_PLAN_CN_MODELS,
        "qwen-token-plan-individual" => {
            &qwen_token_plan_individual_models::QWEN_TOKEN_PLAN_INDIVIDUAL_MODELS
        }
        "xiaomi" => &xiaomi_models::XIAOMI_MODELS,
        "xiaomi-token-plan-ams" => &xiaomi_token_plan_ams_models::XIAOMI_TOKEN_PLAN_AMS_MODELS,
        "xiaomi-token-plan-cn" => &xiaomi_token_plan_cn_models::XIAOMI_TOKEN_PLAN_CN_MODELS,
        "xiaomi-token-plan-sgp" => &xiaomi_token_plan_sgp_models::XIAOMI_TOKEN_PLAN_SGP_MODELS,
        "zai" => &zai_models::ZAI_MODELS,
        "zai-coding-cn" => &zai_coding_cn_models::ZAI_CODING_CN_MODELS,
        other => panic!("no catalog wired for provider {other}"),
    };
    catalog
        .get(id)
        .cloned()
        .unwrap_or_else(|| panic!("no built-in model {provider}/{id}"))
}

/// The model as TS-shaped JSON.
pub(super) fn model_json(model: &Model) -> JsonValue {
    serde_json::to_value(model).expect("serialize model")
}

/// `model.compat` as JSON (`null` when unset), for `model.compat?.x` checks.
pub(super) fn compat_json(model: &Model) -> JsonValue {
    serde_json::to_value(&model.compat).expect("serialize compat")
}

/// `{ compat: _, ...getModel(provider, id)!, api: "openai-completions", ...extra }`.
pub(super) fn completions_model(provider: &str, id: &str, extra: &JsonValue) -> Model {
    let mut value = model_json(&catalog_model(provider, id));
    let object = value.as_object_mut().expect("model JSON object");
    object.remove("compat");
    object.insert("api".to_owned(), json!("openai-completions"));
    if let Some(extra) = extra.as_object() {
        for (key, field) in extra {
            object.insert(key.clone(), field.clone());
        }
    }
    model(value)
}

/// `{ ...localOpenAICompletionsModel, ...overrides }`.
pub(super) fn local_model(overrides: &JsonValue) -> Model {
    let mut value = json!({
        "api": "openai-completions",
        "provider": "local-vllm",
        "baseUrl": "http://localhost:8000/v1",
        "reasoning": true,
        "input": ["text"],
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
        "contextWindow": 128_000,
        "maxTokens": 8192,
    });
    let object = value.as_object_mut().expect("model JSON object");
    if let Some(overrides) = overrides.as_object() {
        for (key, field) in overrides {
            object.insert(key.clone(), field.clone());
        }
    }
    model(value)
}

/// The fake SDK's default chunks (`mockState.chunks ?? [...]`).
pub(super) fn default_chunks() -> Vec<JsonValue> {
    vec![json!({
        "choices": [{ "delta": {}, "finish_reason": "stop" }],
        "usage": {
            "prompt_tokens": 1,
            "completion_tokens": 1,
            "prompt_tokens_details": { "cached_tokens": 0 },
            "completion_tokens_details": { "reasoning_tokens": 0 },
        },
    })]
}

/// `{ apiKey: "test" }` simple options.
pub(super) fn simple_options() -> SimpleStreamOptions {
    SimpleStreamOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                api_key: Some("test".to_owned()),
                ..ProviderRequestOptions::default()
            },
            ..StreamOptions::default()
        },
        ..SimpleStreamOptions::default()
    }
}

/// `{ apiKey: "test", reasoning }` simple options.
pub(super) fn simple_reasoning(reasoning: ThinkingLevel) -> SimpleStreamOptions {
    SimpleStreamOptions {
        reasoning: Some(reasoning),
        ..simple_options()
    }
}

/// `{ messages: [{ role: "user", content: text }], tools? , systemPrompt? }`.
pub(super) fn ctx(
    text: &str,
    tools: Option<JsonValue>,
    system_prompt: Option<&str>,
) -> TranscriptContext {
    let mut value = json!({ "messages": [{ "role": "user", "content": text, "timestamp": 1 }] });
    let object = value.as_object_mut().expect("context JSON object");
    if let Some(tools) = tools {
        object.insert("tools".to_owned(), tools);
    }
    if let Some(system_prompt) = system_prompt {
        object.insert("systemPrompt".to_owned(), json!(system_prompt));
    }
    context(value)
}

/// `[{ name: "ping", description: "Ping tool", parameters: Type.Object({ ok: Type.Boolean() }) }]`.
pub(super) fn ping_tools() -> JsonValue {
    json!([{
        "name": "ping",
        "description": "Ping tool",
        "parameters": {
            "type": "object",
            "properties": { "ok": { "type": "boolean" } },
            "required": ["ok"],
        },
    }])
}

/// Run `streamSimple` answered with `chunks`; returns the payload `onPayload`
/// saw (if any), the events, and the final message.
pub(super) async fn run_simple(
    model: &Model,
    context: &TranscriptContext,
    mut options: SimpleStreamOptions,
    chunks: Vec<JsonValue>,
) -> (
    Option<JsonValue>,
    Vec<AssistantMessageEvent>,
    AssistantMessage,
) {
    let (fetch, _requests) = sse_fetch(chunks);
    options.stream.request.fetch = Some(fetch);
    let (hook, seen) = payload_recorder();
    options.stream.request.on_payload = Some(hook);
    let (events, message) = collect(stream_simple(model, context, options)).await;
    let payload = seen
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .last()
        .cloned();
    (payload, events, message)
}

/// The payload `onPayload` saw for a `streamSimple` call answered with the
/// default chunks.
pub(super) async fn simple_payload(
    model: &Model,
    context: &TranscriptContext,
    options: SimpleStreamOptions,
) -> JsonValue {
    let (payload, _, message) = run_simple(model, context, options, default_chunks()).await;
    payload.unwrap_or_else(|| panic!("no payload was built: {:?}", message.error_message))
}

/// TS `captureSimpleParams(model, reasoning)`.
async fn capture_simple_params(model: &Model, reasoning: Option<ThinkingLevel>) -> JsonValue {
    let options = SimpleStreamOptions {
        reasoning,
        ..simple_options()
    };
    simple_payload(model, &ctx("Hi", None, None), options).await
}

/// Run `stream` (provider options with `extra`) answered with the default
/// chunks; returns the payload `onPayload` saw.
pub(super) async fn provider_payload(
    model: &Model,
    context: &TranscriptContext,
    extra: &JsonValue,
) -> JsonValue {
    let (fetch, _requests) = sse_fetch(default_chunks());
    let (hook, seen) = payload_recorder();
    let options = ProviderStreamOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                api_key: Some("test".to_owned()),
                fetch: Some(fetch),
                on_payload: Some(hook),
                ..ProviderRequestOptions::default()
            },
            ..StreamOptions::default()
        },
        extra: extra.as_object().cloned().unwrap_or_else(JsonObject::new),
    };
    let (_, message) = collect(stream(model, context, options)).await;
    let payload = seen
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .last()
        .cloned();
    payload.unwrap_or_else(|| panic!("no payload was built: {:?}", message.error_message))
}

// Rust `ToolChoice` (simple options) has no `"required"`; TS passes it through
// an `as unknown` cast. The closest Rust path that forwards an arbitrary tool
// choice is `stream` with `extra.toolChoice`.
#[tokio::test]
async fn forwards_tool_choice_from_simple_options_to_payload() {
    let model = completions_model("openai", "gpt-4o-mini", &json!({}));
    let params = provider_payload(
        &model,
        &ctx("Call ping with ok=true", Some(ping_tools()), None),
        &json!({ "toolChoice": "required" }),
    )
    .await;

    assert_eq!(params["tool_choice"], json!("required"));
    let tools = params["tools"].as_array().expect("tools array");
    assert!(!tools.is_empty());
}

#[tokio::test]
async fn includes_tool_choice_when_no_tools_are_provided() {
    let model = completions_model("openai", "gpt-4o-mini", &json!({}));
    let options = SimpleStreamOptions {
        tool_choice: Some(ToolChoice::None),
        ..simple_options()
    };
    let params = simple_payload(
        &model,
        &ctx("Summarize the conversation", None, None),
        options,
    )
    .await;

    assert_eq!(params["tool_choice"], json!("none"));
    assert!(params.get("tools").is_none());
}

#[tokio::test]
async fn omits_strict_when_compat_disables_strict_mode() {
    let model = completions_model(
        "openai",
        "gpt-4o-mini",
        &json!({ "compat": { "supportsStrictMode": false } }),
    );
    let params = simple_payload(
        &model,
        &ctx("Call ping with ok=true", Some(ping_tools()), None),
        simple_options(),
    )
    .await;

    let tool = params["tools"][0]["function"]
        .as_object()
        .expect("function tool");
    assert!(!tool.contains_key("strict"));
}

/// The tool of the strict-mode cases: `{ required: String, optional?: String }`
/// with `constrainedSampling: { type: "json_schema", strict: "prefer" }`.
fn prefer_strict_tools() -> JsonValue {
    json!([{
        "name": "ping",
        "description": "Ping tool",
        "parameters": {
            "type": "object",
            "properties": {
                "required": { "type": "string" },
                "optional": { "type": "string" },
            },
            "required": ["required"],
        },
        "constrainedSampling": { "type": "json_schema", "strict": "prefer" },
    }])
}

#[tokio::test]
async fn defaults_unknown_openai_compatible_endpoints_to_non_strict_tools() {
    // Regression test for #9816.
    let model = local_model(&json!({ "id": "local-model", "name": "Local Model" }));
    let params = simple_payload(
        &model,
        &ctx("Call ping", Some(prefer_strict_tools()), None),
        simple_options(),
    )
    .await;

    let function_tool = params["tools"][0]["function"]
        .as_object()
        .expect("function tool");
    assert!(!function_tool.contains_key("strict"));
    assert_eq!(function_tool["parameters"]["required"], json!(["required"]));
}

#[tokio::test]
async fn preserves_strict_tools_for_capable_built_in_chat_completions_models() {
    let model = catalog_model("groq", "openai/gpt-oss-20b");
    assert_eq!(compat_json(&model)["supportsStrictMode"], json!(true));
    let params = simple_payload(
        &model,
        &ctx("Call ping", Some(prefer_strict_tools()), None),
        simple_options(),
    )
    .await;

    let function_tool = &params["tools"][0]["function"];
    assert_eq!(function_tool["strict"], json!(true));
    assert_eq!(
        function_tool["parameters"]["required"],
        json!(["required", "optional"])
    );
}

#[tokio::test]
async fn maps_groq_qwen_reasoning_levels_to_default_reasoning_effort() {
    let model = catalog_model("groq", "qwen/qwen3.6-27b");
    let params = simple_payload(
        &model,
        &ctx("Hi", None, None),
        simple_reasoning(ThinkingLevel::Medium),
    )
    .await;

    assert_eq!(params["reasoning_effort"], json!("default"));
}

#[tokio::test]
async fn keeps_normal_reasoning_effort_for_groq_models_without_compat_mapping() {
    let model = catalog_model("groq", "openai/gpt-oss-20b");
    let params = simple_payload(
        &model,
        &ctx("Hi", None, None),
        simple_reasoning(ThinkingLevel::Medium),
    )
    .await;

    assert_eq!(params["reasoning_effort"], json!("medium"));
}

#[tokio::test]
async fn enables_tool_stream_for_supported_z_ai_models_with_tools() {
    let model = catalog_model("zai", "glm-5.2");
    let params = simple_payload(
        &model,
        &ctx("Call ping with ok=true", Some(ping_tools()), None),
        simple_options(),
    )
    .await;

    assert_eq!(params["tool_stream"], json!(true));
}

#[test]
fn stores_z_ai_tool_stream_support_in_model_compat_metadata() {
    for id in ["glm-4.7", "glm-4.7", "glm-5-turbo", "glm-5.2"] {
        assert_eq!(
            compat_json(&catalog_model("zai", id))["zaiToolStream"],
            json!(true),
            "{id}"
        );
    }
}

#[test]
fn stores_z_ai_effort_metadata() {
    for model_id in ["glm-5.2", "glm-5.2-highspeed"] {
        let model = catalog_model("zai", model_id);
        assert_eq!(compat_json(&model)["supportsReasoningEffort"], json!(true));
        assert_eq!(
            model_json(&model)["thinkingLevelMap"],
            json!({
                "off": "none",
                "minimal": null,
                "low": null,
                "medium": null,
                "high": "high",
                "xhigh": null,
                "max": "max",
            })
        );
    }

    for provider in ["zai", "zai-coding-cn"] {
        let glm53 = catalog_model(provider, "glm-5.3");
        assert_eq!(compat_json(&glm53)["supportsReasoningEffort"], json!(true));
        assert_eq!(
            model_json(&glm53)["thinkingLevelMap"],
            json!({
                "off": null,
                "minimal": null,
                "low": "low",
                "medium": null,
                "high": "high",
                "xhigh": null,
                "max": "max",
            })
        );
    }
}

#[tokio::test]
async fn maps_z_ai_glm_5_2_thinking_levels_to_reasoning_effort() {
    let model = catalog_model("zai", "glm-5.2");
    let cases = [
        (ThinkingLevel::Low, "high"),
        (ThinkingLevel::Medium, "high"),
        (ThinkingLevel::High, "high"),
        (ThinkingLevel::Max, "max"),
    ];

    for (reasoning, effort) in cases {
        let params =
            simple_payload(&model, &ctx("Hi", None, None), simple_reasoning(reasoning)).await;

        assert_eq!(
            params["thinking"],
            json!({ "type": "enabled", "clear_thinking": false })
        );
        assert_eq!(params["reasoning_effort"], json!(effort));
    }
}

/// The empty usage of the replayed assistant messages.
pub(super) fn zero_usage() -> JsonValue {
    json!({
        "input": 0,
        "output": 0,
        "cacheRead": 0,
        "cacheWrite": 0,
        "totalTokens": 0,
        "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 },
    })
}

/// Fields of `actual` named in `expected` equal theirs (`toMatchObject`).
pub(super) fn assert_match_object(actual: &JsonValue, expected: &JsonValue) {
    let expected = expected.as_object().expect("expected object");
    for (key, value) in expected {
        assert_eq!(actual.get(key), Some(value), "field {key} of {actual}");
    }
}

#[tokio::test]
async fn preserves_z_ai_thinking_when_replaying_reasoning_content() {
    let model = catalog_model("zai", "glm-5.2");
    let context = context(json!({
        "messages": [
            { "role": "user", "content": "Read README.md", "timestamp": 1 },
            {
                "role": "assistant",
                "api": "openai-completions",
                "provider": "zai",
                "model": "glm-5.2",
                "content": [
                    { "type": "thinking", "thinking": "prior reasoning", "thinkingSignature": "reasoning_content" },
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
            { "role": "user", "content": "Continue", "timestamp": 1 },
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
        &json!({ "reasoning_content": "prior reasoning" }),
    );
    assert_eq!(
        params["thinking"],
        json!({ "type": "enabled", "clear_thinking": false })
    );
}

#[tokio::test]
async fn omits_z_ai_glm_5_2_reasoning_effort_when_thinking_is_off() {
    let model = catalog_model("zai", "glm-5.2");
    let params = simple_payload(&model, &ctx("Hi", None, None), simple_options()).await;

    assert_eq!(params["thinking"], json!({ "type": "disabled" }));
    assert!(params.get("reasoning_effort").is_none());
}

#[tokio::test]
async fn respects_explicit_z_ai_tool_stream_compat_override() {
    let base_model = catalog_model("zai", "glm-5.2");
    let mut value = model_json(&base_model);
    let mut compat = compat_json(&base_model);
    if !compat.is_object() {
        compat = json!({});
    }
    compat["zaiToolStream"] = json!(true);
    value["compat"] = compat;
    let model = model(value);
    let params = simple_payload(
        &model,
        &ctx("Call ping with ok=true", Some(ping_tools()), None),
        simple_options(),
    )
    .await;

    assert_eq!(params["tool_stream"], json!(true));
}

#[tokio::test]
async fn omits_tool_stream_when_no_tools_are_provided() {
    let model = catalog_model("zai", "glm-5.2");
    let params = simple_payload(&model, &ctx("Hi", None, None), simple_options()).await;

    assert!(params.get("tool_stream").is_none());
}

#[tokio::test]
async fn maps_non_standard_provider_finish_reason_values_to_stop_reason_error() {
    let chunks = vec![
        json!({ "choices": [{ "delta": { "content": "partial" }, "finish_reason": null }] }),
        json!({
            "choices": [{ "delta": {}, "finish_reason": "network_error" }],
            "usage": {
                "prompt_tokens": 1,
                "completion_tokens": 1,
                "prompt_tokens_details": { "cached_tokens": 0 },
                "completion_tokens_details": { "reasoning_tokens": 0 },
            },
        }),
    ];
    let model = catalog_model("zai", "glm-5.2");
    let (_, _, response) =
        run_simple(&model, &ctx("Hi", None, None), simple_options(), chunks).await;

    assert_eq!(response.stop_reason, StopReason::Error);
    assert_eq!(
        response.error_message.as_deref(),
        Some("Provider finish_reason: network_error")
    );
}

#[tokio::test]
async fn ignores_null_stream_chunks_from_openai_compatible_providers() {
    let chunks = vec![
        JsonValue::Null,
        json!({ "id": "chatcmpl-test", "choices": [{ "delta": { "content": "OK" }, "finish_reason": null }] }),
        json!({
            "id": "chatcmpl-test",
            "choices": [{ "delta": {}, "finish_reason": "stop" }],
            "usage": {
                "prompt_tokens": 3,
                "completion_tokens": 1,
                "prompt_tokens_details": { "cached_tokens": 0 },
                "completion_tokens_details": { "reasoning_tokens": 0 },
            },
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

    assert_eq!(response.stop_reason, StopReason::Stop);
    assert_eq!(response.error_message, None);
    assert_eq!(response.response_id.as_deref(), Some("chatcmpl-test"));
    assert_eq!(response.usage.total_tokens, 4);
    assert_eq!(
        serde_json::to_value(&response.content).expect("serialize content"),
        json!([{ "type": "text", "text": "OK" }])
    );
}

#[tokio::test]
async fn errors_when_a_stream_ends_after_only_null_finish_reason_chunks() {
    let chunk = json!({
        "id": "chatcmpl-truncated",
        "choices": [{ "delta": { "content": "partial answer" }, "finish_reason": null }],
    });
    let model = completions_model("openai", "gpt-4o-mini", &json!({}));
    let (_, _, response) = run_simple(
        &model,
        &ctx("Reply with a longer sentence", None, None),
        simple_options(),
        vec![chunk.clone(), chunk],
    )
    .await;

    assert_eq!(response.stop_reason, StopReason::Error);
    assert_eq!(
        response.error_message.as_deref(),
        Some("Stream ended without finish_reason")
    );
}

#[tokio::test]
async fn accepts_streams_without_finish_reason_when_compat_disables_it() {
    let chunks = vec![json!({
        "id": "chatcmpl-no-finish-reason",
        "choices": [{ "delta": { "content": "complete answer" }, "finish_reason": null }],
    })];
    let model = completions_model(
        "openai",
        "gpt-4o-mini",
        &json!({ "compat": { "supportsFinishReason": false } }),
    );
    let (_, _, response) = run_simple(
        &model,
        &ctx("Reply with a complete answer", None, None),
        simple_options(),
        chunks,
    )
    .await;

    assert_eq!(response.stop_reason, StopReason::Stop);
    assert_eq!(response.error_message, None);
    assert_eq!(
        serde_json::to_value(&response.content).expect("serialize content"),
        json!([{ "type": "text", "text": "complete answer" }])
    );
}

#[tokio::test]
async fn uses_configurable_chat_template_boolean_thinking_kwargs() {
    let model = local_model(&json!({
        "id": "deepseek-ai/DeepSeek-V3.1",
        "name": "DeepSeek V3.1 via vLLM",
        "compat": {
            "thinkingFormat": "chat-template",
            "supportsReasoningEffort": false,
            "chatTemplateKwargs": { "thinking": { "$var": "thinking.enabled" } },
        },
    }));

    for (reasoning, expected) in [(Some(ThinkingLevel::High), true), (None, false)] {
        let params = capture_simple_params(&model, reasoning).await;

        assert_eq!(
            params["chat_template_kwargs"],
            json!({ "thinking": expected })
        );
        assert!(params.get("thinking").is_none());
        assert!(params.get("reasoning_effort").is_none());
    }
}

#[tokio::test]
async fn uses_qwen_chat_template_thinking_kwargs() {
    let model = local_model(&json!({
        "id": "Qwen/Qwen3-Coder",
        "name": "Qwen3 Coder via vLLM",
        "compat": { "thinkingFormat": "qwen-chat-template", "supportsReasoningEffort": false },
    }));

    for (reasoning, expected) in [(Some(ThinkingLevel::High), true), (None, false)] {
        let params = capture_simple_params(&model, reasoning).await;

        assert_eq!(
            params["chat_template_kwargs"],
            json!({ "enable_thinking": expected, "preserve_thinking": true })
        );
        assert!(params.get("reasoning_effort").is_none());
    }
}

#[tokio::test]
async fn uses_configurable_chat_template_effort_kwargs_with_static_kwargs() {
    let model = local_model(&json!({
        "id": "unsloth/gpt-oss-120b-GGUF",
        "name": "GPT OSS via vLLM",
        "thinkingLevelMap": { "xhigh": "max" },
        "compat": {
            "thinkingFormat": "chat-template",
            "supportsReasoningEffort": false,
            "chatTemplateKwargs": {
                "preserve_thinking": true,
                "reasoning_effort": { "$var": "thinking.effort", "omitWhenOff": true },
            },
        },
    }));

    let params = capture_simple_params(&model, Some(ThinkingLevel::Xhigh)).await;

    assert_eq!(
        params["chat_template_kwargs"],
        json!({ "preserve_thinking": true, "reasoning_effort": "max" })
    );
    assert!(params.get("reasoning_effort").is_none());
}
