//! Compatibility resolution: URL/provider auto-detection overridden by the
//! explicit `model.compat` (TS `detectCompat` / `getCompat`).

use crate::types::IndexMap;

use crate::types::{
    CacheControlFormat, ChatTemplateKwargValue, MaxTokensField, Model, ModelCompat,
    OpenAICompletionsCompat, SessionAffinityFormat, ThinkingFormat, ThinkingTokenBudgetField,
};

/// TS `ResolvedOpenAICompletionsCompat`: every setting resolved except the
/// ones TS keeps optional. The routing preferences are read from
/// `model.compat` directly where they are applied, as in TS.
#[derive(Debug, Clone, PartialEq)]
// Mirrors the TS compat record field by field; each flag is an independent setting.
#[allow(clippy::struct_excessive_bools)]
pub(crate) struct ResolvedCompat {
    pub(crate) supports_store: bool,
    pub(crate) supports_developer_role: bool,
    pub(crate) supports_reasoning_effort: bool,
    pub(crate) supports_usage_in_streaming: bool,
    pub(crate) supports_finish_reason: bool,
    pub(crate) max_tokens_field: MaxTokensField,
    pub(crate) requires_tool_result_name: bool,
    pub(crate) requires_assistant_after_tool_result: bool,
    pub(crate) requires_thinking_as_text: bool,
    pub(crate) requires_reasoning_content_on_assistant_messages: bool,
    pub(crate) thinking_format: ThinkingFormat,
    pub(crate) chat_template_kwargs: IndexMap<String, ChatTemplateKwargValue>,
    pub(crate) chat_template_args: IndexMap<String, ChatTemplateKwargValue>,
    pub(crate) zai_tool_stream: bool,
    pub(crate) supports_thinking_token_budget: Option<bool>,
    pub(crate) thinking_token_budget_field: Option<ThinkingTokenBudgetField>,
    pub(crate) supports_strict_mode: bool,
    pub(crate) supports_openai_grammar_tools: bool,
    pub(crate) supports_mid_convo_system_messages: Option<bool>,
    pub(crate) supports_mid_convo_tool_additions: Option<bool>,
    pub(crate) cache_control_format: Option<CacheControlFormat>,
    pub(crate) send_session_affinity_headers: bool,
    pub(crate) session_affinity_format: SessionAffinityFormat,
    pub(crate) supports_long_cache_retention: bool,
    pub(crate) vllm_priority: Option<f64>,
}

/// The model's explicit `openai-completions` compat block.
pub(crate) fn model_compat(model: &Model) -> Option<&OpenAICompletionsCompat> {
    match model.compat.as_ref()? {
        ModelCompat::OpenAICompletions(compat) => Some(compat),
        ModelCompat::OpenAIResponses(_)
        | ModelCompat::AnthropicMessages(_)
        | ModelCompat::Bedrock(_)
        | ModelCompat::MistralConversations(_)
        | ModelCompat::Other(_) => None,
    }
}

/// Auto-detect compatibility settings from provider name and baseUrl. Used
/// as the base when `model.compat` is not set; explicit entries override.
// One flat detection table, kept in TS order.
#[allow(clippy::too_many_lines)]
pub(crate) fn detect_compat(model: &Model) -> ResolvedCompat {
    let provider = model.provider.as_str();
    let base_url = model.base_url.as_str();

    let is_zai = provider == "zai"
        || provider == "zai-coding-cn"
        || base_url.contains("api.z.ai")
        || base_url.contains("open.bigmodel.cn");
    let is_together = provider == "together"
        || base_url.contains("api.together.ai")
        || base_url.contains("api.together.xyz");
    let is_moonshot = provider == "moonshotai"
        || provider == "moonshotai-cn"
        || base_url.contains("api.moonshot.");
    let is_open_router = provider == "openrouter" || base_url.contains("openrouter.ai");
    let is_cloudflare_workers_ai =
        provider == "cloudflare-workers-ai" || base_url.contains("api.cloudflare.com");
    let is_cloudflare_ai_gateway =
        provider == "cloudflare-ai-gateway" || base_url.contains("gateway.ai.cloudflare.com");
    let is_nvidia = provider == "nvidia" || base_url.contains("integrate.api.nvidia.com");
    let is_ant_ling = provider == "ant-ling" || base_url.contains("api.ant-ling.com");
    let is_cerebras = provider == "cerebras" || base_url.contains("cerebras.ai");
    let is_deep_seek = provider == "deepseek" || base_url.to_lowercase().contains("deepseek.com");
    // eukhe addition: the Prime Inference gateway is a non-standard
    // OpenAI-compatible endpoint that takes `max_tokens` and Anthropic-format
    // cache marks for Anthropic models.
    let is_prime_inference =
        provider == "prime-inference" || base_url.contains("api.pinference.ai");

    // eukhe addition: local OpenAI-compatible servers (llama.cpp, vLLM,
    // SGLang) reject unknown fields such as `store` with a 400. Omitting it
    // is correct for real OpenAI too, where the chat-completions default is
    // already false.
    let is_loopback = ["//localhost", "//127.0.0.1", "//[::1]", "//[0:0:0:0:0:0:0:1]"]
        .iter()
        .any(|host| base_url.contains(host));

    let is_non_standard = is_nvidia
        || is_cerebras
        || provider == "xai"
        || base_url.contains("api.x.ai")
        || is_together
        || base_url.contains("chutes.ai")
        || is_deep_seek
        || is_zai
        || is_moonshot
        || provider == "opencode"
        || base_url.contains("opencode.ai")
        || is_cloudflare_workers_ai
        || is_cloudflare_ai_gateway
        || is_ant_ling
        || is_prime_inference;

    let use_max_tokens = base_url.contains("chutes.ai")
        || is_deep_seek
        || is_moonshot
        || is_cloudflare_ai_gateway
        || is_together
        || is_nvidia
        || is_ant_ling
        || is_zai
        || is_prime_inference;

    let is_grok = provider == "xai" || base_url.contains("api.x.ai");
    let is_open_router_developer_role_model =
        is_open_router && (model.id.starts_with("anthropic/") || model.id.starts_with("openai/"));
    let cache_control_format = ((provider == "openrouter" || is_prime_inference)
        && model.id.starts_with("anthropic/"))
    .then_some(CacheControlFormat::Anthropic);

    let thinking_format = if is_deep_seek {
        ThinkingFormat::Deepseek
    } else if is_zai {
        ThinkingFormat::Zai
    } else if is_together {
        ThinkingFormat::Together
    } else if is_ant_ling {
        ThinkingFormat::AntLing
    } else if is_open_router {
        ThinkingFormat::OpenRouter
    } else {
        ThinkingFormat::OpenAI
    };

    ResolvedCompat {
        supports_store: !is_non_standard && !is_loopback,
        supports_developer_role: is_open_router_developer_role_model
            || (!is_non_standard && !is_open_router),
        supports_reasoning_effort: !is_grok
            && !is_zai
            && !is_moonshot
            && !is_together
            && !is_cloudflare_ai_gateway
            && !is_nvidia
            && !is_ant_ling,
        supports_usage_in_streaming: true,
        supports_finish_reason: true,
        max_tokens_field: if use_max_tokens {
            MaxTokensField::MaxTokens
        } else {
            MaxTokensField::MaxCompletionTokens
        },
        requires_tool_result_name: false,
        requires_assistant_after_tool_result: false,
        requires_thinking_as_text: false,
        requires_reasoning_content_on_assistant_messages: is_deep_seek,
        thinking_format,
        chat_template_kwargs: IndexMap::new(),
        chat_template_args: IndexMap::new(),
        zai_tool_stream: false,
        supports_thinking_token_budget: Some(false),
        thinking_token_budget_field: None,
        // OpenAI compatibility alone does not imply strict JSON-schema tool support.
        supports_strict_mode: false,
        supports_openai_grammar_tools: false,
        supports_mid_convo_system_messages: Some(false),
        supports_mid_convo_tool_additions: Some(false),
        cache_control_format,
        send_session_affinity_headers: is_open_router,
        session_affinity_format: if is_open_router {
            SessionAffinityFormat::OpenRouter
        } else {
            SessionAffinityFormat::OpenAI
        },
        supports_long_cache_retention: !(is_together
            || is_cloudflare_workers_ai
            || is_cloudflare_ai_gateway
            || is_nvidia
            || is_ant_ling),
        vllm_priority: None,
    }
}

/// Resolved compatibility settings: auto-detected, then overridden by the
/// explicit `model.compat`.
pub(crate) fn get_compat(model: &Model) -> ResolvedCompat {
    let detected = detect_compat(model);
    let Some(compat) = model_compat(model) else {
        return detected;
    };
    ResolvedCompat {
        supports_store: compat.supports_store.unwrap_or(detected.supports_store),
        supports_developer_role: compat
            .supports_developer_role
            .unwrap_or(detected.supports_developer_role),
        supports_reasoning_effort: compat
            .supports_reasoning_effort
            .unwrap_or(detected.supports_reasoning_effort),
        supports_usage_in_streaming: compat
            .supports_usage_in_streaming
            .unwrap_or(detected.supports_usage_in_streaming),
        supports_finish_reason: compat
            .supports_finish_reason
            .unwrap_or(detected.supports_finish_reason),
        max_tokens_field: compat.max_tokens_field.unwrap_or(detected.max_tokens_field),
        requires_tool_result_name: compat
            .requires_tool_result_name
            .unwrap_or(detected.requires_tool_result_name),
        requires_assistant_after_tool_result: compat
            .requires_assistant_after_tool_result
            .unwrap_or(detected.requires_assistant_after_tool_result),
        requires_thinking_as_text: compat
            .requires_thinking_as_text
            .unwrap_or(detected.requires_thinking_as_text),
        requires_reasoning_content_on_assistant_messages: compat
            .requires_reasoning_content_on_assistant_messages
            .unwrap_or(detected.requires_reasoning_content_on_assistant_messages),
        thinking_format: compat.thinking_format.unwrap_or(detected.thinking_format),
        chat_template_kwargs: compat
            .chat_template_kwargs
            .clone()
            .unwrap_or(detected.chat_template_kwargs),
        chat_template_args: compat
            .chat_template_args
            .clone()
            .unwrap_or(detected.chat_template_args),
        zai_tool_stream: compat.zai_tool_stream.unwrap_or(detected.zai_tool_stream),
        supports_thinking_token_budget: compat
            .supports_thinking_token_budget
            .or(detected.supports_thinking_token_budget),
        thinking_token_budget_field: compat
            .thinking_token_budget_field
            .or(detected.thinking_token_budget_field),
        supports_strict_mode: compat
            .supports_strict_mode
            .unwrap_or(detected.supports_strict_mode),
        supports_openai_grammar_tools: compat
            .supports_openai_grammar_tools
            .unwrap_or(detected.supports_openai_grammar_tools),
        supports_mid_convo_system_messages: compat
            .supports_mid_convo_system_messages
            .or(detected.supports_mid_convo_system_messages),
        supports_mid_convo_tool_additions: compat
            .supports_mid_convo_tool_additions
            .or(detected.supports_mid_convo_tool_additions),
        cache_control_format: compat
            .cache_control_format
            .or(detected.cache_control_format),
        send_session_affinity_headers: compat
            .send_session_affinity_headers
            .unwrap_or(detected.send_session_affinity_headers),
        session_affinity_format: compat
            .session_affinity_format
            .unwrap_or(detected.session_affinity_format),
        supports_long_cache_retention: compat
            .supports_long_cache_retention
            .unwrap_or(detected.supports_long_cache_retention),
        vllm_priority: compat.vllm_priority,
    }
}
