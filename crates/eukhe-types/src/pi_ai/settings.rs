//! Request vocabulary shared by models and stream options: thinking levels,
//! cache retention, transports, provider env/headers.

use indexmap::IndexMap;
use serde::{Deserialize, Serialize};

use super::string_enum::string_enum;
use super::JsonObject;

string_enum! {
    /// Provider-neutral tool selection for simple requests.
    pub enum ToolChoice {
        Auto => "auto",
        None => "none",
    }
}

string_enum! {
    /// Pi reasoning effort levels.
    pub enum ThinkingLevel {
        Minimal => "minimal",
        Low => "low",
        Medium => "medium",
        High => "high",
        Xhigh => "xhigh",
        Max => "max",
    }
}

string_enum! {
    /// TS `ModelThinkingLevel = "off" | ThinkingLevel`.
    pub enum ModelThinkingLevel {
        Off => "off",
        Minimal => "minimal",
        Low => "low",
        Medium => "medium",
        High => "high",
        Xhigh => "xhigh",
        Max => "max",
    }
}

impl From<ThinkingLevel> for ModelThinkingLevel {
    fn from(level: ThinkingLevel) -> Self {
        match level {
            ThinkingLevel::Minimal => Self::Minimal,
            ThinkingLevel::Low => Self::Low,
            ThinkingLevel::Medium => Self::Medium,
            ThinkingLevel::High => Self::High,
            ThinkingLevel::Xhigh => Self::Xhigh,
            ThinkingLevel::Max => Self::Max,
        }
    }
}

/// TS `Partial<Record<ModelThinkingLevel, string | null>>`: a missing key uses
/// the provider default, `None` marks the level unsupported.
pub type ThinkingLevelMap = IndexMap<ModelThinkingLevel, Option<String>>;

/// TS `SamplingParams = Record<string, unknown>`.
pub type SamplingParams = JsonObject;

/// TS `Partial<Record<ModelThinkingLevel, SamplingParams>>`.
pub type SamplingParamsByThinkingLevel = IndexMap<ModelThinkingLevel, SamplingParams>;

string_enum! {
    /// Pi-controlled thinking values a chat-template kwarg can reference.
    pub enum ChatTemplateVar {
        ThinkingEnabled => "thinking.enabled",
        ThinkingEffort => "thinking.effort",
        ThinkingBudget => "thinking.budget",
    }
}

/// `{ $var, omitWhenOff? }` member of [`ChatTemplateKwargValue`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ChatTemplateVarRef {
    #[serde(rename = "$var")]
    pub var: ChatTemplateVar,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub omit_when_off: Option<bool>,
}

/// TS `ChatTemplateKwargValue = string | number | boolean | null | { $var, omitWhenOff? }`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum ChatTemplateKwargValue {
    String(String),
    Number(#[serde(serialize_with = "super::js_number::serialize")] f64),
    Bool(bool),
    Null,
    Var(ChatTemplateVarRef),
}

string_enum! {
    /// Top-level request field used to cap reasoning tokens on OpenAI-compatible servers.
    pub enum ThinkingTokenBudgetField {
        ThinkingTokenBudget => "thinking_token_budget",
        ThinkingBudget => "thinking_budget",
        ThinkingBudgetTokens => "thinking_budget_tokens",
    }
}

/// Token budgets for each thinking level (token-based providers only).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ThinkingBudgets {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub minimal: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub low: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub medium: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub high: Option<u64>,
}

string_enum! {
    /// Prompt cache retention preference.
    pub enum CacheRetention {
        None => "none",
        Short => "short",
        Long => "long",
    }
}

/// Best-effort prompt cache lifetime in seconds for each retention tier a
/// request can ask for. A missing tier means the lifetime is unknown; pi does
/// not warm such caches.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct ModelPromptCache {
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "super::js_number::option::serialize"
    )]
    pub short: Option<f64>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "super::js_number::option::serialize"
    )]
    pub long: Option<f64>,
}

string_enum! {
    /// Preferred transport for providers that support several.
    pub enum Transport {
        Sse => "sse",
        Websocket => "websocket",
        WebsocketCached => "websocket-cached",
        Auto => "auto",
    }
}

/// Provider-scoped environment overrides. Values take precedence over the
/// process environment.
pub type ProviderEnv = IndexMap<String, String>;

/// Request headers; a `None` value suppresses a default header of that name.
pub type ProviderHeaders = IndexMap<String, Option<String>>;

string_enum! {
    /// Session-affinity header format.
    pub enum SessionAffinityFormat {
        OpenAI => "openai",
        OpenAINoSession => "openai-nosession",
        OpenRouter => "openrouter",
    }
}

/// HTTP response metadata handed to `onResponse`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProviderResponse {
    pub status: u16,
    pub headers: IndexMap<String, String>,
}

string_enum! {
    /// eukhe addition: `OpenAI` service tier requested through
    /// `StreamOptions::service_tier` (`"auto" | "default" | "flex" | "scale" | "priority"`).
    pub enum ServiceTier {
        Auto => "auto",
        Default => "default",
        Flex => "flex",
        Scale => "scale",
        Priority => "priority",
    }
}
