//! Request body construction (TS `buildParams` and its helpers).

use crate::types::IndexMap;
use serde_json::json;

use super::compat::{model_compat, ResolvedCompat};
use super::convert::{convert_messages, convert_tools, ConvertCompletionsMessagesOptions};
use super::OpenAICompletionsOptions;
use crate::api::cache_breakpoints::CacheMarkBudget;
use crate::api::openai_prompt_cache::clamp_openai_prompt_cache_key;
use crate::api::simple_options::{
    clamp_thinking_budget_to_answer_room, resolve_sampling_params, thinking_budget_for_level,
};
use crate::types::{
    AssistantContentBlock, CacheControlFormat, CacheRetention, ChatTemplateKwargValue,
    ChatTemplateVar, JsonObject, JsonValue, MaxTokensField, Message, Model, ModelThinkingLevel,
    ThinkingFormat, ThinkingLevel, ThinkingTokenBudgetField, TranscriptContext,
};
use crate::utils::diagnostics::Thrown;
use crate::utils::provider_env::get_provider_env_value;
use crate::utils::transcript::resolve_transcript_tools;

/// TS `resolveCacheRetention`.
pub(crate) fn resolve_cache_retention(
    cache_retention: Option<CacheRetention>,
    env: Option<&crate::types::ProviderEnv>,
) -> CacheRetention {
    if let Some(cache_retention) = cache_retention {
        return cache_retention;
    }
    if get_provider_env_value("PI_CACHE_RETENTION", env).as_deref() == Some("long") {
        return CacheRetention::Long;
    }
    CacheRetention::Short
}

/// Check if conversation messages contain tool calls or tool results:
/// Anthropic (via proxy) requires the tools param when they do.
fn has_tool_history(messages: &[Message]) -> bool {
    messages.iter().any(|message| match message {
        Message::ToolResult(_) => true,
        Message::Assistant(assistant) => assistant
            .content
            .iter()
            .any(|block| matches!(block, AssistantContentBlock::ToolCall(_))),
        Message::System(_) | Message::User(_) => false,
    })
}

/// `model.thinkingLevelMap?.[level]`: `None` when the key is missing,
/// `Some(None)` for an explicit `null`.
// Mirrors TS `undefined` (missing key) vs `null` (unsupported level) of `ThinkingLevelMap`.
#[allow(clippy::option_option)]
fn level_map(model: &Model, level: ModelThinkingLevel) -> Option<Option<&str>> {
    model
        .thinking_level_map
        .as_ref()?
        .get(&level)
        .map(Option::as_deref)
}

/// `model.thinkingLevelMap?.[effort] ?? effort`.
fn mapped_effort_or_default(model: &Model, effort: ThinkingLevel) -> String {
    level_map(model, effort.into())
        .flatten()
        .map_or_else(|| effort.as_str().to_owned(), str::to_owned)
}

fn insert(params: &mut JsonObject, key: &str, value: JsonValue) {
    params.insert(key.to_owned(), value);
}

/// TS `buildParams`.
///
/// # Errors
///
/// Fails on invalid constrained-sampling configs or unreplayable grammar
/// tool calls.
// One linear body mirroring the TS request construction order.
#[allow(clippy::too_many_lines)]
pub(crate) fn build_params(
    model: &Model,
    context: &TranscriptContext,
    options: &OpenAICompletionsOptions,
    compat: &ResolvedCompat,
    cache_retention: CacheRetention,
    grammar_tool_input_properties: &IndexMap<String, String>,
) -> Result<JsonObject, Thrown> {
    let stream_options = &options.stream;
    let transcript_tools = resolve_transcript_tools(
        context.messages(),
        compat.supports_mid_convo_system_messages == Some(true)
            && compat.supports_mid_convo_tool_additions == Some(true),
    );
    let cache_control = get_compat_cache_control(compat, cache_retention);
    let mut messages = convert_messages(
        model,
        context,
        compat,
        &ConvertCompletionsMessagesOptions {
            grammar_tool_input_properties: Some(grammar_tool_input_properties),
            cache_control: cache_control.as_ref(),
        },
    )?;

    let long_retention =
        cache_retention == CacheRetention::Long && compat.supports_long_cache_retention;
    let mut params = JsonObject::new();
    insert(&mut params, "model", json!(model.id));
    // `messages` is placed here and filled once cache marks are applied.
    insert(&mut params, "messages", JsonValue::Null);
    insert(&mut params, "stream", json!(true));
    if (model.base_url.contains("api.openai.com") && cache_retention != CacheRetention::None)
        || long_retention
    {
        if let Some(key) = clamp_openai_prompt_cache_key(stream_options.session_id.as_deref()) {
            insert(&mut params, "prompt_cache_key", json!(key));
        }
    }
    if long_retention {
        insert(&mut params, "prompt_cache_retention", json!("24h"));
    }

    if compat.supports_usage_in_streaming {
        insert(
            &mut params,
            "stream_options",
            json!({ "include_usage": true }),
        );
    }
    if compat.supports_store {
        insert(&mut params, "store", json!(false));
    }

    if let Some(max_tokens) = stream_options.max_tokens.filter(|tokens| *tokens != 0) {
        match compat.max_tokens_field {
            // Deprecated by OpenAI, but some OpenAI-compatible providers only accept max_tokens.
            MaxTokensField::MaxTokens => insert(&mut params, "max_tokens", json!(max_tokens)),
            MaxTokensField::MaxCompletionTokens => {
                insert(&mut params, "max_completion_tokens", json!(max_tokens));
            }
        }
    }

    if let Some(temperature) = stream_options.temperature {
        insert(
            &mut params,
            "temperature",
            crate::utils::js::js_number_value(temperature),
        );
    }

    let mut tools: Option<Vec<JsonValue>> = None;
    let mut tools_present = false;
    if !transcript_tools.request_tools.is_empty() {
        tools = Some(convert_tools(&transcript_tools.request_tools, compat)?);
        tools_present = true;
        insert(&mut params, "tools", JsonValue::Null);
        if compat.zai_tool_stream {
            insert(&mut params, "tool_stream", json!(true));
        }
    } else if has_tool_history(context.messages()) {
        // Anthropic (via LiteLLM/proxy) requires tools param when conversation has tool_calls/tool_results.
        tools = Some(Vec::new());
        tools_present = true;
        insert(&mut params, "tools", JsonValue::Null);
    }

    if let Some(cache_control) = &cache_control {
        apply_anthropic_cache_control(&mut messages, tools.as_mut(), cache_control);
    }
    insert(&mut params, "messages", JsonValue::Array(messages));
    if tools_present {
        insert(
            &mut params,
            "tools",
            JsonValue::Array(tools.unwrap_or_default()),
        );
    }

    if let Some(tool_choice) = options
        .tool_choice
        .as_ref()
        .filter(|choice| super::convert::js_truthy(Some(choice)))
    {
        insert(&mut params, "tool_choice", tool_choice.clone());
    }

    if let Some(priority) = compat.vllm_priority {
        insert(
            &mut params,
            "priority",
            crate::utils::js::js_number_value(priority),
        );
    }

    let thinking_token_budget_field = resolve_thinking_token_budget_field(compat);
    let thinking_budget = resolve_clamped_thinking_budget(model, options, &params);

    if model.reasoning {
        apply_thinking_format(model, options, compat, thinking_budget, &mut params);
    }

    // Cap reasoning with a top-level budget field. Independent of
    // thinkingFormat: reasoning and the answer share max_tokens here, so an
    // uncapped reasoning phase can consume the whole response.
    if let (Some(field), Some(budget)) = (thinking_token_budget_field, thinking_budget) {
        insert(&mut params, field.as_str(), json!(budget));
    }

    // eukhe addition: OpenAI and OpenRouter accept a top-level service_tier
    // (OpenRouter: flex and priority for every model). Other
    // OpenAI-compatible gateways may reject unknown fields, and Prime
    // Inference ignores it, so only those two receive it.
    if let Some(service_tier) = stream_options.service_tier {
        if model.provider == "openai" || model.provider == "openrouter" {
            insert(&mut params, "service_tier", json!(service_tier.as_str()));
        }
    }

    // OpenRouter provider routing preferences.
    if let Some(routing) =
        model_compat(model).and_then(|compat| compat.open_router_routing.as_ref())
    {
        insert(
            &mut params,
            "provider",
            serde_json::to_value(routing).map_err(crate::utils::diagnostics::thrown)?,
        );
    }

    // Vercel AI Gateway provider routing preferences.
    if let Some(routing) =
        model_compat(model).and_then(|compat| compat.vercel_gateway_routing.as_ref())
    {
        if routing.only.is_some() || routing.order.is_some() {
            let mut gateway = JsonObject::new();
            if let Some(only) = &routing.only {
                insert(&mut gateway, "only", json!(only));
            }
            if let Some(order) = &routing.order {
                insert(&mut gateway, "order", json!(order));
            }
            insert(
                &mut params,
                "providerOptions",
                json!({ "gateway": gateway }),
            );
        }
    }

    // Last so model and request sampling parameters override named request fields.
    let thinking_level = options
        .reasoning_effort
        .map_or(ModelThinkingLevel::Off, ModelThinkingLevel::from);
    if let Some(sampling_params) = resolve_sampling_params(
        model,
        thinking_level,
        stream_options.sampling_params.as_ref(),
    ) {
        for (key, value) in sampling_params {
            params.insert(key, value);
        }
    }

    Ok(params)
}

/// The `thinkingFormat` branches of `buildParams` (all require `model.reasoning`).
// One match arm per TS `thinkingFormat` branch.
#[allow(clippy::too_many_lines)]
fn apply_thinking_format(
    model: &Model,
    options: &OpenAICompletionsOptions,
    compat: &ResolvedCompat,
    thinking_budget: Option<u64>,
    params: &mut JsonObject,
) {
    let effort = options.reasoning_effort;
    match compat.thinking_format {
        ThinkingFormat::Zai => {
            insert(
                params,
                "thinking",
                if effort.is_some() {
                    json!({ "type": "enabled", "clear_thinking": false })
                } else {
                    json!({ "type": "disabled" })
                },
            );
            if let Some(effort) = effort.filter(|_| compat.supports_reasoning_effort) {
                let value = match level_map(model, effort.into()) {
                    None => Some(effort.as_str()),
                    Some(mapped) => mapped,
                };
                if let Some(value) = value {
                    insert(params, "reasoning_effort", json!(value));
                }
            }
        }
        ThinkingFormat::Qwen => {
            insert(params, "enable_thinking", json!(effort.is_some()));
            if let Some(effort) = effort.filter(|_| compat.supports_reasoning_effort) {
                insert(
                    params,
                    "reasoning_effort",
                    json!(mapped_effort_or_default(model, effort)),
                );
            }
        }
        ThinkingFormat::QwenChatTemplate => {
            insert(
                params,
                "chat_template_kwargs",
                json!({ "enable_thinking": effort.is_some(), "preserve_thinking": true }),
            );
        }
        ThinkingFormat::ChatTemplate => {
            if let Some(kwargs) = build_chat_template_values(
                model,
                options,
                &compat.chat_template_kwargs,
                thinking_budget,
            ) {
                insert(params, "chat_template_kwargs", JsonValue::Object(kwargs));
            }
        }
        ThinkingFormat::Baseten => {
            if let Some(args) = build_chat_template_values(
                model,
                options,
                &compat.chat_template_args,
                thinking_budget,
            ) {
                insert(params, "chat_template_args", JsonValue::Object(args));
            }
            if compat.supports_reasoning_effort {
                let mapped = match effort {
                    Some(effort) => level_map(model, effort.into()),
                    None => level_map(model, ModelThinkingLevel::Off),
                };
                let value = match mapped {
                    None => effort.map(ThinkingLevel::as_str),
                    Some(mapped) => mapped,
                };
                if let Some(value) = value {
                    insert(params, "reasoning_effort", json!(value));
                }
            }
        }
        ThinkingFormat::Deepseek => {
            if effort.is_some() {
                insert(params, "thinking", json!({ "type": "enabled" }));
            } else if level_map(model, ModelThinkingLevel::Off) != Some(None) {
                insert(params, "thinking", json!({ "type": "disabled" }));
            }
            if let Some(effort) = effort.filter(|_| compat.supports_reasoning_effort) {
                insert(
                    params,
                    "reasoning_effort",
                    json!(mapped_effort_or_default(model, effort)),
                );
            }
        }
        ThinkingFormat::OpenRouter => {
            // OpenRouter normalizes reasoning across providers via a nested reasoning object.
            if let Some(effort) = effort {
                insert(
                    params,
                    "reasoning",
                    json!({ "effort": mapped_effort_or_default(model, effort) }),
                );
            } else {
                let off = level_map(model, ModelThinkingLevel::Off);
                if off != Some(None) {
                    insert(
                        params,
                        "reasoning",
                        json!({ "effort": off.flatten().unwrap_or("none") }),
                    );
                }
            }
        }
        ThinkingFormat::AntLing => match effort {
            Some(effort) => {
                if let Some(Some(mapped)) = level_map(model, effort.into()) {
                    insert(params, "reasoning", json!({ "effort": mapped }));
                }
            }
            // TS: the ant-ling branch requires an effort; without one the
            // OpenAI-style fallback branches apply.
            None => apply_openai_reasoning_effort(model, None, compat, params),
        },
        ThinkingFormat::Together => {
            insert(params, "reasoning", json!({ "enabled": effort.is_some() }));
            if let Some(effort) = effort.filter(|_| compat.supports_reasoning_effort) {
                insert(
                    params,
                    "reasoning_effort",
                    json!(mapped_effort_or_default(model, effort)),
                );
            }
        }
        ThinkingFormat::StringThinking => {
            if let Some(effort) = effort {
                insert(
                    params,
                    "thinking",
                    json!(mapped_effort_or_default(model, effort)),
                );
            } else {
                let off = level_map(model, ModelThinkingLevel::Off);
                if off != Some(None) {
                    insert(params, "thinking", json!(off.flatten().unwrap_or("none")));
                }
            }
        }
        ThinkingFormat::OpenAI => apply_openai_reasoning_effort(model, effort, compat, params),
    }
}

/// The OpenAI-style `reasoning_effort` fallback branches of `buildParams`.
fn apply_openai_reasoning_effort(
    model: &Model,
    effort: Option<ThinkingLevel>,
    compat: &ResolvedCompat,
    params: &mut JsonObject,
) {
    if !compat.supports_reasoning_effort {
        return;
    }
    match effort {
        Some(effort) => {
            insert(
                params,
                "reasoning_effort",
                json!(mapped_effort_or_default(model, effort)),
            );
        }
        None => {
            if let Some(Some(off)) = level_map(model, ModelThinkingLevel::Off) {
                insert(params, "reasoning_effort", json!(off));
            }
        }
    }
}

/// TS `resolveThinkingTokenBudgetField`.
fn resolve_thinking_token_budget_field(
    compat: &ResolvedCompat,
) -> Option<ThinkingTokenBudgetField> {
    if compat.thinking_token_budget_field.is_some() {
        return compat.thinking_token_budget_field;
    }
    if compat.supports_thinking_token_budget == Some(true) {
        return Some(ThinkingTokenBudgetField::ThinkingTokenBudget);
    }
    None
}

/// TS `resolveClampedThinkingBudget`.
fn resolve_clamped_thinking_budget(
    model: &Model,
    options: &OpenAICompletionsOptions,
    params: &JsonObject,
) -> Option<u64> {
    let effort = options.reasoning_effort.filter(|_| model.reasoning)?;
    let ceiling = params
        .get("max_tokens")
        .and_then(JsonValue::as_u64)
        .or_else(|| {
            params
                .get("max_completion_tokens")
                .and_then(JsonValue::as_u64)
        })
        .unwrap_or(model.max_tokens);
    let budget = clamp_thinking_budget_to_answer_room(
        thinking_budget_for_level(effort, options.thinking_budgets.as_ref()),
        ceiling,
    );
    (budget > 0).then_some(budget)
}

/// TS `buildChatTemplateValues`.
fn build_chat_template_values(
    model: &Model,
    options: &OpenAICompletionsOptions,
    values: &IndexMap<String, ChatTemplateKwargValue>,
    thinking_budget: Option<u64>,
) -> Option<JsonObject> {
    let mut resolved_values = JsonObject::new();
    for (key, value) in values {
        if let Some(resolved) =
            resolve_chat_template_kwarg_value(model, options, value, thinking_budget)
        {
            resolved_values.insert(key.clone(), resolved);
        }
    }
    (!resolved_values.is_empty()).then_some(resolved_values)
}

/// TS `resolveChatTemplateKwargValue`; `None` is `undefined`.
fn resolve_chat_template_kwarg_value(
    model: &Model,
    options: &OpenAICompletionsOptions,
    value: &ChatTemplateKwargValue,
    thinking_budget: Option<u64>,
) -> Option<JsonValue> {
    let var = match value {
        ChatTemplateKwargValue::String(text) => return Some(json!(text)),
        ChatTemplateKwargValue::Number(number) => {
            return Some(crate::utils::js::js_number_value(*number));
        }
        ChatTemplateKwargValue::Bool(flag) => return Some(json!(flag)),
        ChatTemplateKwargValue::Null => return Some(JsonValue::Null),
        ChatTemplateKwargValue::Var(var) => var,
    };

    let reasoning_effort = options.reasoning_effort;
    if reasoning_effort.is_none() && var.omit_when_off == Some(true) {
        return None;
    }
    match var.var {
        ChatTemplateVar::ThinkingEnabled => Some(json!(reasoning_effort.is_some())),
        ChatTemplateVar::ThinkingBudget => thinking_budget.map(|budget| json!(budget)),
        ChatTemplateVar::ThinkingEffort => {
            let mapped = match reasoning_effort {
                Some(effort) => level_map(model, effort.into()),
                None => level_map(model, ModelThinkingLevel::Off),
            };
            match mapped {
                None => reasoning_effort.map(|effort| json!(effort.as_str())),
                Some(mapped) => mapped.map(|mapped| json!(mapped)),
            }
        }
    }
}

/// TS `getCompatCacheControl`: the `cache_control` mark, when the compat
/// uses Anthropic-format marks and caching is on.
pub(crate) fn get_compat_cache_control(
    compat: &ResolvedCompat,
    cache_retention: CacheRetention,
) -> Option<JsonValue> {
    if compat.cache_control_format != Some(CacheControlFormat::Anthropic)
        || cache_retention == CacheRetention::None
    {
        return None;
    }
    if cache_retention == CacheRetention::Long && compat.supports_long_cache_retention {
        return Some(json!({ "type": "ephemeral", "ttl": "1h" }));
    }
    Some(json!({ "type": "ephemeral" }))
}

/// TS `applyAnthropicCacheControl`: marks on the system prompt, the last
/// tool, and the last conversation message's text.
///
/// eukhe addition: the end mark is placed first and the system and tool
/// marks only take the slots the [`CacheMarkBudget`] has left after the
/// explicitly marked user blocks. Without marked blocks every mark fits and
/// the result equals the TS output.
fn apply_anthropic_cache_control(
    messages: &mut [JsonValue],
    tools: Option<&mut Vec<JsonValue>>,
    cache_control: &JsonValue,
) {
    add_cache_control_to_last_conversation_message(messages, cache_control);
    let mut budget = CacheMarkBudget::after_message_marks(messages, "cache_control");
    if let Some(system) = messages
        .iter_mut()
        .find(|message| matches!(role(message), Some("system" | "developer")))
    {
        if budget.take() {
            add_cache_control_to_text_content(system, cache_control);
        }
    }
    if let Some(last_tool) = tools.and_then(|tools| tools.last_mut()) {
        if budget.take() {
            if let Some(last_tool) = last_tool.as_object_mut() {
                last_tool.insert("cache_control".into(), cache_control.clone());
            }
        }
    }
}

fn role(message: &JsonValue) -> Option<&str> {
    message.get("role").and_then(JsonValue::as_str)
}

fn add_cache_control_to_last_conversation_message(
    messages: &mut [JsonValue],
    cache_control: &JsonValue,
) {
    for message in messages.iter_mut().rev() {
        if matches!(role(message), Some("user" | "assistant" | "tool"))
            && add_cache_control_to_text_content(message, cache_control)
        {
            return;
        }
    }
}

fn add_cache_control_to_text_content(message: &mut JsonValue, cache_control: &JsonValue) -> bool {
    let Some(message) = message.as_object_mut() else {
        return false;
    };
    match message.get_mut("content") {
        Some(JsonValue::String(content)) => {
            if content.is_empty() {
                return false;
            }
            let text = std::mem::take(content);
            message.insert(
                "content".into(),
                json!([{ "type": "text", "text": text, "cache_control": cache_control }]),
            );
            true
        }
        Some(JsonValue::Array(parts)) => {
            for part in parts.iter_mut().rev() {
                if part.get("type").and_then(JsonValue::as_str) == Some("text") {
                    if let Some(part) = part.as_object_mut() {
                        part.insert("cache_control".into(), cache_control.clone());
                    }
                    return true;
                }
            }
            false
        }
        _ => false,
    }
}
