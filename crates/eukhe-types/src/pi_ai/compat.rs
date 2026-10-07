//! Per-API compatibility settings (`Model.compat`).

use indexmap::IndexMap;
use serde::{Deserialize, Serialize};

use super::model::ModelCost;
use super::routing::{OpenRouterRouting, VercelGatewayRouting};
use super::settings::{ChatTemplateKwargValue, SessionAffinityFormat, ThinkingTokenBudgetField};
use super::string_enum::string_enum;
use super::{JsonValue, ProviderId};

string_enum! {
    /// Which field carries max tokens on OpenAI-compatible completions APIs.
    pub enum MaxTokensField {
        MaxCompletionTokens => "max_completion_tokens",
        MaxTokens => "max_tokens",
    }
}

string_enum! {
    /// Format of the reasoning/thinking request parameter on OpenAI-compatible completions APIs.
    ///
    /// `openai` uses `reasoning_effort`, `openrouter` uses `reasoning: { effort }`,
    /// `deepseek` uses `thinking: { type }` plus `reasoning_effort` when supported,
    /// `together` uses `reasoning: { enabled }` plus `reasoning_effort` when supported,
    /// `baseten` uses configurable `chat_template_args` plus `reasoning_effort` when
    /// supported, `zai` uses `thinking: { type }`, `qwen` uses top-level
    /// `enable_thinking: boolean`, `qwen-chat-template` uses
    /// `chat_template_kwargs.enable_thinking` and `preserve_thinking`, `chat-template`
    /// uses configurable `chat_template_kwargs`, `string-thinking` uses top-level
    /// `thinking: string`, and `ant-ling` uses `reasoning: { effort }` only when the
    /// mapped effort is non-null. Default: `openai`.
    pub enum ThinkingFormat {
        OpenAI => "openai",
        OpenRouter => "openrouter",
        Deepseek => "deepseek",
        Together => "together",
        Baseten => "baseten",
        Zai => "zai",
        Qwen => "qwen",
        ChatTemplate => "chat-template",
        QwenChatTemplate => "qwen-chat-template",
        StringThinking => "string-thinking",
        AntLing => "ant-ling",
    }
}

string_enum! {
    /// Cache control convention for prompt caching on OpenAI-compatible completions APIs.
    pub enum CacheControlFormat {
        /// Anthropic-style `cache_control` markers on the system prompt, last tool
        /// definition, and last user, assistant, or tool-result text content.
        Anthropic => "anthropic",
    }
}

/// Compatibility settings for OpenAI-compatible completions APIs. Overrides
/// URL-based auto-detection for custom providers.
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OpenAICompletionsCompat {
    /// Whether the provider supports the `store` field. Default: auto-detected from URL.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_store: Option<bool>,
    /// Whether the provider supports the `developer` role (vs `system`). Default: auto-detected from URL.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_developer_role: Option<bool>,
    /// Whether the provider supports `reasoning_effort`. Default: auto-detected from URL.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_reasoning_effort: Option<bool>,
    /// Whether the provider supports `stream_options: { include_usage: true }`. Default: true.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_usage_in_streaming: Option<bool>,
    /// Whether streamed responses include `finish_reason`. When false, pi infers
    /// `stop` or `toolUse` when the stream ends. Default: true.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_finish_reason: Option<bool>,
    /// Which field to use for max tokens. Default: auto-detected from URL.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_tokens_field: Option<MaxTokensField>,
    /// Whether tool results require the `name` field. Default: auto-detected from URL.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub requires_tool_result_name: Option<bool>,
    /// Whether a user message after tool results requires an assistant message in between.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub requires_assistant_after_tool_result: Option<bool>,
    /// Whether thinking blocks must be converted to text blocks with `<thinking>` delimiters.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub requires_thinking_as_text: Option<bool>,
    /// Whether all replayed assistant messages must include an empty
    /// `reasoning_content` field when reasoning is enabled.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub requires_reasoning_content_on_assistant_messages: Option<bool>,
    /// Format for the reasoning/thinking parameter. Default: `openai`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thinking_format: Option<ThinkingFormat>,
    /// Kwargs sent as `chat_template_kwargs` when `thinking_format` is `chat-template`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub chat_template_kwargs: Option<IndexMap<String, ChatTemplateKwargValue>>,
    /// Arguments sent as `chat_template_args` when `thinking_format` is `baseten`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub chat_template_args: Option<IndexMap<String, ChatTemplateKwargValue>>,
    /// OpenRouter-compatible routing preferences sent as the `provider` request field.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub open_router_routing: Option<OpenRouterRouting>,
    /// Vercel AI Gateway routing preferences.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub vercel_gateway_routing: Option<VercelGatewayRouting>,
    /// Whether z.ai supports top-level `tool_stream: true`. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub zai_tool_stream: Option<bool>,
    /// Top-level request field used to cap reasoning tokens from `thinkingBudgets`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thinking_token_budget_field: Option<ThinkingTokenBudgetField>,
    /// Alias for `thinking_token_budget_field: thinking_token_budget` (vLLM). Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_thinking_token_budget: Option<bool>,
    /// Whether the provider supports `OpenAI` custom tools with Lark/regex grammar formats.
    #[serde(
        default,
        rename = "supportsOpenAIGrammarTools",
        skip_serializing_if = "Option::is_none"
    )]
    pub supports_openai_grammar_tools: Option<bool>,
    /// Whether the exact model accepts system or developer messages mid-conversation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_mid_convo_system_messages: Option<bool>,
    /// Whether system messages can introduce additional tools mid-conversation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_mid_convo_tool_additions: Option<bool>,
    /// Whether the provider supports the `strict` field in tool definitions. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_strict_mode: Option<bool>,
    /// Cache control convention for prompt caching.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cache_control_format: Option<CacheControlFormat>,
    /// Whether to send session-affinity data from `options.session_id`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub send_session_affinity_headers: Option<bool>,
    /// Session-affinity header format. Default: auto-detected.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub session_affinity_format: Option<SessionAffinityFormat>,
    /// Whether the provider supports long prompt cache retention. Default: true.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_long_cache_retention: Option<bool>,
    /// vLLM scheduler priority sent as the top-level `priority` request field.
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "super::js_number::option::serialize"
    )]
    pub vllm_priority: Option<f64>,
}

/// Compatibility settings for `OpenAI` Responses APIs.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct OpenAIResponsesCompat {
    /// Whether the provider supports the `developer` role (vs `system`). Default: true.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_developer_role: Option<bool>,
    /// Whether the exact model accepts developer or system messages mid-conversation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_mid_convo_system_messages: Option<bool>,
    /// Session-affinity header format. Default: auto-detected.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub session_affinity_format: Option<SessionAffinityFormat>,
    /// Whether the provider supports long prompt cache retention. Default: true.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_long_cache_retention: Option<bool>,
    /// Whether the provider supports strict JSON-schema function tools.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_strict_mode: Option<bool>,
    /// Whether to emit `OpenAI` custom tools with Lark/regex grammar formats.
    #[serde(
        default,
        rename = "supportsOpenAIGrammarTools",
        skip_serializing_if = "Option::is_none"
    )]
    pub supports_openai_grammar_tools: Option<bool>,
    /// Whether the model supports message-anchored `additional_tools` input items. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_additional_tools: Option<bool>,
    /// Whether the model supports client-executed tool search for transcript-anchored additions.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_tool_search: Option<bool>,
    /// Whether the model accepts `prompt_cache_options` (`OpenAI` GPT-5.6+). Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_explicit_prompt_cache_mode: Option<bool>,
    /// Whether the provider accepts the `max_output_tokens` parameter. Default: true.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_max_output_tokens: Option<bool>,
}

string_enum! {
    /// Session-affinity format of Anthropic Messages-compatible APIs.
    pub enum AnthropicSessionAffinityFormat {
        /// Sends `x-session-id`; when unset, `x-session-affinity` is sent.
        OpenRouter => "openrouter",
    }
}

/// A model Anthropic accepts in `fallbacks`, with local pricing metadata.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AnthropicAllowedFallbackModel {
    pub provider: ProviderId,
    pub model: String,
    pub cost: ModelCost,
}

/// Compatibility settings for Anthropic Messages-compatible APIs.
#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AnthropicMessagesCompat {
    /// Whether the provider accepts per-tool `eager_input_streaming`. Default: true.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_eager_tool_input_streaming: Option<bool>,
    /// Whether the provider supports `cache_control.ttl: "1h"`. Default: true.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_long_cache_retention: Option<bool>,
    /// Whether to send the `x-session-affinity` header from `options.session_id`
    /// when caching is enabled. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub send_session_affinity_headers: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub session_affinity_format: Option<AnthropicSessionAffinityFormat>,
    /// Whether the provider supports `cache_control` markers on tool definitions. Default: true.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_cache_control_on_tools: Option<bool>,
    /// Whether the model accepts the `temperature` request field. Default: true.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_temperature: Option<bool>,
    /// Whether to force adaptive thinking regardless of the model id. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub force_adaptive_thinking: Option<bool>,
    /// Whether to replay empty thinking signatures as `signature: ""`. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub allow_empty_signature: Option<bool>,
    /// Whether the provider supports Anthropic strict tool schemas. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_strict_tools: Option<bool>,
    /// Whether effort-only system messages and thinking binding controls are supported. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_mid_convo_effort: Option<bool>,
    /// Whether system-role messages are accepted inside the conversation. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_mid_convo_system_messages: Option<bool>,
    /// Whether mid-conversation `tool_addition`/`tool_removal` blocks are accepted. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_mid_convo_tool_changes: Option<bool>,
    /// Models Anthropic accepts in `fallbacks` for server-side refusal fallback.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub allowed_fallback_models: Option<Vec<AnthropicAllowedFallbackModel>>,
}

/// Compatibility settings for Amazon Bedrock models.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BedrockCompat {
    /// Whether the model supports Bedrock strict tool schemas. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_strict_mode: Option<bool>,
}

/// Compatibility settings for the Mistral chat API.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MistralConversationsCompat {
    /// Whether the exact model accepts system messages mid-conversation. Default: false.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub supports_mid_convo_system_messages: Option<bool>,
}

/// TS `Model<TApi>["compat"]`: the compat type is selected by the model's API.
///
/// Serialized untagged. [`super::Model`] deserializes `compat` according to
/// its `api`; APIs without a compat type keep the raw JSON in
/// [`ModelCompat::Other`] (TS types it `never` but carries it at runtime).
// Mirrors the TS union by value; compat blocks are read in place, not moved.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(untagged)]
pub enum ModelCompat {
    /// `openai-completions`.
    OpenAICompletions(OpenAICompletionsCompat),
    /// `openai-responses`, `azure-openai-responses`, `openai-codex-responses`.
    OpenAIResponses(OpenAIResponsesCompat),
    /// `anthropic-messages`.
    AnthropicMessages(AnthropicMessagesCompat),
    /// `bedrock-converse-stream`.
    Bedrock(BedrockCompat),
    /// `mistral-conversations`.
    MistralConversations(MistralConversationsCompat),
    /// Any other API.
    Other(JsonValue),
}

impl ModelCompat {
    /// Parse `compat` JSON for a model whose API is `api`.
    ///
    /// # Errors
    ///
    /// Returns the serde error when the JSON does not fit the API's compat type.
    pub fn from_json(api: &str, value: JsonValue) -> Result<Self, serde_json::Error> {
        Ok(match api {
            "openai-completions" => Self::OpenAICompletions(serde_json::from_value(value)?),
            "openai-responses" | "azure-openai-responses" | "openai-codex-responses" => {
                Self::OpenAIResponses(serde_json::from_value(value)?)
            }
            "anthropic-messages" => Self::AnthropicMessages(serde_json::from_value(value)?),
            "bedrock-converse-stream" => Self::Bedrock(serde_json::from_value(value)?),
            "mistral-conversations" => Self::MistralConversations(serde_json::from_value(value)?),
            _ => Self::Other(value),
        })
    }

    /// The `OpenAI` completions compat, when this is one.
    #[must_use]
    pub const fn as_openai_completions(&self) -> Option<&OpenAICompletionsCompat> {
        match self {
            Self::OpenAICompletions(compat) => Some(compat),
            Self::OpenAIResponses(_)
            | Self::AnthropicMessages(_)
            | Self::Bedrock(_)
            | Self::MistralConversations(_)
            | Self::Other(_) => None,
        }
    }

    /// The `OpenAI` responses compat, when this is one.
    #[must_use]
    pub const fn as_openai_responses(&self) -> Option<&OpenAIResponsesCompat> {
        match self {
            Self::OpenAIResponses(compat) => Some(compat),
            Self::OpenAICompletions(_)
            | Self::AnthropicMessages(_)
            | Self::Bedrock(_)
            | Self::MistralConversations(_)
            | Self::Other(_) => None,
        }
    }

    /// The Anthropic messages compat, when this is one.
    #[must_use]
    pub const fn as_anthropic_messages(&self) -> Option<&AnthropicMessagesCompat> {
        match self {
            Self::AnthropicMessages(compat) => Some(compat),
            Self::OpenAICompletions(_)
            | Self::OpenAIResponses(_)
            | Self::Bedrock(_)
            | Self::MistralConversations(_)
            | Self::Other(_) => None,
        }
    }

    /// The Bedrock compat, when this is one.
    #[must_use]
    pub const fn as_bedrock(&self) -> Option<&BedrockCompat> {
        match self {
            Self::Bedrock(compat) => Some(compat),
            Self::OpenAICompletions(_)
            | Self::OpenAIResponses(_)
            | Self::AnthropicMessages(_)
            | Self::MistralConversations(_)
            | Self::Other(_) => None,
        }
    }

    /// The Mistral compat, when this is one.
    #[must_use]
    pub const fn as_mistral_conversations(&self) -> Option<&MistralConversationsCompat> {
        match self {
            Self::MistralConversations(compat) => Some(compat),
            Self::OpenAICompletions(_)
            | Self::OpenAIResponses(_)
            | Self::AnthropicMessages(_)
            | Self::Bedrock(_)
            | Self::Other(_) => None,
        }
    }
}
