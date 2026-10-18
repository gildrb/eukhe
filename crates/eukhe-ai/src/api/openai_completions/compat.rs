//! Compatibility resolution: the quirks rulebook's host settings
//! overridden by the explicit `model.compat` (TS `detectCompat` /
//! `getCompat`).

use crate::quirks::{Lookup, Quirks};
use crate::types::{IndexMap, KnownProvider};

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
    /// The quirks rulebook's `strict_cap`: at most this many strict tools
    /// per request.
    pub(crate) strict_cap: Option<u32>,
    pub(crate) supports_openai_grammar_tools: bool,
    pub(crate) supports_mid_convo_system_messages: Option<bool>,
    pub(crate) supports_mid_convo_tool_additions: Option<bool>,
    pub(crate) cache_control_format: Option<CacheControlFormat>,
    pub(crate) send_session_affinity_headers: bool,
    pub(crate) session_affinity_format: SessionAffinityFormat,
    pub(crate) supports_long_cache_retention: bool,
    pub(crate) vllm_priority: Option<f64>,
    /// The quirks rulebook's `prompt_progress` (a capability lookup):
    /// request `return_progress` and read the `prompt_progress` chunks.
    pub(crate) supports_prompt_progress: bool,
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

/// eukhe addition: whether a reasoning model is a Qwen-family model (the
/// quirks rulebook's `qwen_chat_template`: `qwen3*`, `qwq`, ...) on a custom
/// provider with no explicit `thinkingFormat`, i.e. a self-hosted server
/// (llama.cpp, vLLM, `SGLang`) rendering the Qwen chat template. That
/// template thinks unless `chat_template_kwargs.enable_thinking` is
/// `false`, so `off` must be sent explicitly. Built-in providers keep their
/// catalog formats; set `compat.thinkingFormat` to opt a custom model out.
pub(crate) fn is_custom_qwen_template_model(model: &Model) -> bool {
    if !model.reasoning
        || KnownProvider::parse(&model.provider).is_some()
        || model_compat(model).is_some_and(|compat| compat.thinking_format.is_some())
    {
        return false;
    }
    Quirks::of(model).qwen_chat_template().unwrap_or(false)
}

/// Whether `model`'s id starts with one of `prefixes`.
fn id_has_prefix(model: &Model, prefixes: Option<&[String]>) -> bool {
    prefixes.is_some_and(|prefixes| {
        prefixes
            .iter()
            .any(|prefix| model.id.starts_with(prefix.as_str()))
    })
}

/// The settings the quirks rulebook gives the model's host (provider id,
/// else base URL); a setting no rule gives takes the standard
/// OpenAI-compatible default. Used as the base when `model.compat` is not
/// set; explicit entries override.
pub(crate) fn detect_compat(model: &Model) -> ResolvedCompat {
    let quirks = Quirks::of(model);
    let session_affinity_format = quirks
        .session_affinity_format()
        .unwrap_or(SessionAffinityFormat::OpenAI);
    ResolvedCompat {
        supports_store: quirks.store().unwrap_or(true),
        supports_developer_role: id_has_prefix(model, quirks.developer_role_prefixes())
            || quirks.developer_role().unwrap_or(true),
        supports_reasoning_effort: quirks.reasoning_effort().unwrap_or(true),
        supports_usage_in_streaming: true,
        supports_finish_reason: true,
        max_tokens_field: quirks
            .max_tokens_field()
            .unwrap_or(MaxTokensField::MaxCompletionTokens),
        requires_tool_result_name: false,
        requires_assistant_after_tool_result: false,
        requires_thinking_as_text: false,
        requires_reasoning_content_on_assistant_messages: quirks
            .reasoning_content_on_assistant()
            .unwrap_or(false),
        thinking_format: quirks.thinking_format().unwrap_or(ThinkingFormat::OpenAI),
        chat_template_kwargs: IndexMap::new(),
        chat_template_args: IndexMap::new(),
        zai_tool_stream: false,
        supports_thinking_token_budget: Some(false),
        thinking_token_budget_field: None,
        // OpenAI compatibility alone does not imply strict JSON-schema tool support.
        supports_strict_mode: quirks.strict_tools().unwrap_or(false),
        strict_cap: quirks.strict_cap(),
        supports_openai_grammar_tools: false,
        supports_mid_convo_system_messages: Some(false),
        supports_mid_convo_tool_additions: Some(false),
        cache_control_format: id_has_prefix(model, quirks.anthropic_cache_control_prefixes())
            .then_some(CacheControlFormat::Anthropic),
        send_session_affinity_headers: quirks.session_affinity_headers().unwrap_or(false),
        session_affinity_format,
        supports_long_cache_retention: quirks.long_cache_retention().unwrap_or(true),
        vllm_priority: None,
        supports_prompt_progress: Quirks::for_lookup(model, Lookup::Capabilities)
            .prompt_progress()
            .unwrap_or(false),
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
        strict_cap: detected.strict_cap,
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
        supports_prompt_progress: compat
            .supports_prompt_progress
            .unwrap_or(detected.supports_prompt_progress),
    }
}
