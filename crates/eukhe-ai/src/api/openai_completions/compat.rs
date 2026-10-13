//! Compatibility resolution: the model's compat with this API's defaults
//! (TS `getCompat`). Host and model facts live in the catalog data
//! (`providers/data`), never in name or URL checks here.

use crate::types::IndexMap;

use crate::types::{
    CacheControlFormat, ChatTemplateKwargValue, MaxTokensField, Model, ModelCompat,
    OpenAICompletionsCompat, ReasoningField, SessionAffinityFormat, ThinkingFormat,
    ThinkingTokenBudgetField,
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
    pub(crate) supports_strict_mode: Option<bool>,
    pub(crate) supports_openai_grammar_tools: Option<bool>,
    pub(crate) supports_mid_convo_system_messages: Option<bool>,
    pub(crate) supports_mid_convo_tool_additions: Option<bool>,
    pub(crate) cache_control_format: Option<CacheControlFormat>,
    pub(crate) send_session_affinity_headers: bool,
    pub(crate) session_affinity_format: SessionAffinityFormat,
    pub(crate) supports_long_cache_retention: bool,
    pub(crate) send_copilot_headers: bool,
    pub(crate) supports_service_tier: bool,
    pub(crate) bills_service_tier: bool,
    pub(crate) supports_prompt_cache_key: bool,
    pub(crate) max_tool_call_id_length: Option<usize>,
    pub(crate) replay_reasoning_as: Option<ReasoningField>,
    pub(crate) vllm_priority: Option<f64>,
}

/// The model's explicit `openai-completions` compat block.
pub(crate) fn model_compat(model: &Model) -> Option<&OpenAICompletionsCompat> {
    match model.compat.as_ref()? {
        ModelCompat::OpenAICompletions(compat) => Some(compat),
        ModelCompat::OpenAIResponses(_)
        | ModelCompat::AnthropicMessages(_)
        | ModelCompat::Bedrock(_)
        | ModelCompat::Google(_)
        | ModelCompat::MistralConversations(_)
        | ModelCompat::Other(_) => None,
    }
}

/// Resolved compatibility settings: the model's compat (catalog row over its
/// provider's defaults), with this API's defaults for the keys it leaves unset.
pub(crate) fn get_compat(model: &Model) -> ResolvedCompat {
    let compat = model_compat(model);
    let flag = |read: fn(&OpenAICompletionsCompat) -> Option<bool>, default: bool| {
        compat.and_then(read).unwrap_or(default)
    };
    let option = |read: fn(&OpenAICompletionsCompat) -> Option<bool>| compat.and_then(read);
    ResolvedCompat {
        supports_store: flag(|c| c.supports_store, false),
        supports_developer_role: flag(|c| c.supports_developer_role, false),
        supports_reasoning_effort: flag(|c| c.supports_reasoning_effort, true),
        supports_usage_in_streaming: flag(|c| c.supports_usage_in_streaming, true),
        supports_finish_reason: flag(|c| c.supports_finish_reason, true),
        max_tokens_field: compat
            .and_then(|c| c.max_tokens_field)
            .unwrap_or(MaxTokensField::MaxCompletionTokens),
        requires_tool_result_name: flag(|c| c.requires_tool_result_name, false),
        requires_assistant_after_tool_result: flag(
            |c| c.requires_assistant_after_tool_result,
            false,
        ),
        requires_thinking_as_text: flag(|c| c.requires_thinking_as_text, false),
        requires_reasoning_content_on_assistant_messages: flag(
            |c| c.requires_reasoning_content_on_assistant_messages,
            false,
        ),
        thinking_format: compat
            .and_then(|c| c.thinking_format)
            .unwrap_or(ThinkingFormat::OpenAI),
        chat_template_kwargs: compat
            .and_then(|c| c.chat_template_kwargs.clone())
            .unwrap_or_default(),
        chat_template_args: compat
            .and_then(|c| c.chat_template_args.clone())
            .unwrap_or_default(),
        zai_tool_stream: flag(|c| c.zai_tool_stream, false),
        supports_thinking_token_budget: option(|c| c.supports_thinking_token_budget),
        thinking_token_budget_field: compat.and_then(|c| c.thinking_token_budget_field),
        supports_strict_mode: option(|c| c.supports_strict_mode),
        supports_openai_grammar_tools: option(|c| c.supports_openai_grammar_tools),
        supports_mid_convo_system_messages: option(|c| c.supports_mid_convo_system_messages),
        supports_mid_convo_tool_additions: option(|c| c.supports_mid_convo_tool_additions),
        cache_control_format: compat.and_then(|c| c.cache_control_format),
        send_session_affinity_headers: flag(|c| c.send_session_affinity_headers, false),
        session_affinity_format: compat
            .and_then(|c| c.session_affinity_format)
            .unwrap_or(SessionAffinityFormat::OpenAI),
        supports_long_cache_retention: flag(|c| c.supports_long_cache_retention, true),
        send_copilot_headers: flag(|c| c.send_copilot_headers, false),
        supports_service_tier: flag(|c| c.supports_service_tier, false),
        bills_service_tier: flag(|c| c.bills_service_tier, false),
        supports_prompt_cache_key: flag(|c| c.supports_prompt_cache_key, false),
        max_tool_call_id_length: compat.and_then(|c| c.max_tool_call_id_length),
        replay_reasoning_as: compat.and_then(|c| c.replay_reasoning_as),
        vllm_priority: compat.and_then(|c| c.vllm_priority),
    }
}
