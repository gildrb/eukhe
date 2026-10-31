//! The provider capability surface: the typed operations a provider's own
//! API offers besides chat streaming.
//!
//! Each [`Capability`] is one operation: count the input tokens of a
//! request, list the provider's models, embed text, generate an image,
//! tokenize text, query account usage, run a provider-native web search,
//! and compact a conversation remotely. Whether a model's provider has an
//! operation, and which endpoint dialect ([`Dialect`]) serves it, is data in
//! the quirks rulebook: the directive named like the capability
//! (`count_tokens`, `list_models`, ...) gives the dialect per host or model
//! (`quirks/rulebook.json`). [`capabilities_of`] reads it.
//!
//! An operation of a capability the model's provider lacks fails with
//! [`CapabilityError::Unsupported`]. It never falls back to another provider
//! or to the local token estimate: a caller that wants the estimate asks for
//! it (`utils::estimate`).
//!
//! The operations run through [`Models`](crate::models::Models), which
//! resolves the provider's auth like a chat request
//! (`models/capabilities.rs`). Each dialect lives in its own module.

use std::fmt;

use eukhe_types::pi_ai::JsonValue;
use serde::Serialize;

use crate::quirks::{Lookup, Quirks};
use crate::types::{Model, ProviderRequestOptions};
use crate::utils::diagnostics::Thrown;

pub(crate) mod anthropic;
pub(crate) mod deepseek;
pub(crate) mod google;
pub(crate) mod http;
pub(crate) mod llama_cpp;
#[cfg(test)]
pub(crate) mod mock_server;
pub(crate) mod openai;
pub(crate) mod openrouter;
pub(crate) mod xai;

/// One operation of the provider capability surface.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Capability {
    /// Count the input tokens of a chat request.
    CountTokens,
    /// List the provider's models (model discovery).
    ListModels,
    /// Embed text.
    Embed,
    /// Generate images from a prompt.
    GenerateImage,
    /// Tokenize text into token ids.
    Tokenize,
    /// Query the account's usage, credits, or balance.
    Usage,
    /// Run a web search with the provider's own search tool.
    WebSearch,
    /// Compact a conversation on the provider.
    Compact,
}

impl Capability {
    /// Every capability, in declaration order.
    pub const ALL: [Self; 8] = [
        Self::CountTokens,
        Self::ListModels,
        Self::Embed,
        Self::GenerateImage,
        Self::Tokenize,
        Self::Usage,
        Self::WebSearch,
        Self::Compact,
    ];

    /// The name rules and the CLI use.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::CountTokens => "count_tokens",
            Self::ListModels => "list_models",
            Self::Embed => "embed",
            Self::GenerateImage => "generate_image",
            Self::Tokenize => "tokenize",
            Self::Usage => "usage",
            Self::WebSearch => "web_search",
            Self::Compact => "compact",
        }
    }
}

impl fmt::Display for Capability {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// The wire dialect of a capability endpoint: whose API shape a host
/// speaks for that operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Dialect {
    /// The Anthropic API (`/v1/...` under the base URL).
    Anthropic,
    /// The `OpenAI` API and the hosts that copy its shape (`/v1/...`).
    #[serde(rename = "openai")]
    OpenAi,
    /// The Gemini API (`generativelanguage`, the base URL names the version).
    Google,
    /// llama.cpp's `llama-server` native endpoints.
    LlamaCpp,
    /// The xAI API's own endpoints.
    Xai,
    /// The `OpenRouter` API's own endpoints.
    #[serde(rename = "openrouter")]
    OpenRouter,
    /// The `DeepSeek` API's own endpoints.
    #[serde(rename = "deepseek")]
    DeepSeek,
}

impl Dialect {
    /// Every dialect, in declaration order.
    pub const ALL: [Self; 7] = [
        Self::Anthropic,
        Self::OpenAi,
        Self::Google,
        Self::LlamaCpp,
        Self::Xai,
        Self::OpenRouter,
        Self::DeepSeek,
    ];

    /// The name rules use.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Anthropic => "anthropic",
            Self::OpenAi => "openai",
            Self::Google => "google",
            Self::LlamaCpp => "llama-cpp",
            Self::Xai => "xai",
            Self::OpenRouter => "openrouter",
            Self::DeepSeek => "deepseek",
        }
    }

    /// The dialect named `name`.
    #[must_use]
    pub fn parse(name: &str) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|dialect| dialect.as_str() == name)
    }

    /// The endpoint this dialect serves `capability` with (method and path
    /// under the dialect's root), or `None` when eukhe has no
    /// implementation of that pair. A rule that names a pair without one
    /// does not compile.
    #[must_use]
    pub const fn endpoint(self, capability: Capability) -> Option<&'static str> {
        match (self, capability) {
            (Self::Anthropic, Capability::CountTokens) => Some("POST /v1/messages/count_tokens"),
            (Self::Anthropic | Self::OpenAi, Capability::ListModels) => Some("GET /v1/models"),
            (Self::Anthropic, Capability::WebSearch) => {
                Some("POST /v1/messages (web_search_20250305 tool)")
            }
            (Self::OpenAi, Capability::CountTokens) => Some("POST /v1/responses/input_tokens"),
            (Self::OpenAi, Capability::Embed) => Some("POST /v1/embeddings"),
            (Self::OpenAi, Capability::GenerateImage) => Some("POST /v1/images/generations"),
            (Self::OpenAi, Capability::WebSearch) => Some("POST /v1/responses (web_search tool)"),
            (Self::OpenAi, Capability::Compact) => Some("POST /v1/responses/compact"),
            (Self::Google, Capability::CountTokens) => Some("POST /models/{model}:countTokens"),
            (Self::Google, Capability::ListModels) => Some("GET /models"),
            (Self::Google, Capability::Embed) => Some("POST /models/{model}:batchEmbedContents"),
            (Self::Google, Capability::WebSearch) => {
                Some("POST /models/{model}:generateContent (google_search tool)")
            }
            (Self::LlamaCpp, Capability::CountTokens) => {
                Some("POST /apply-template, POST /tokenize")
            }
            (Self::LlamaCpp, Capability::Tokenize) => Some("POST /tokenize"),
            (Self::Xai, Capability::Tokenize) => Some("POST /v1/tokenize-text"),
            (Self::OpenRouter, Capability::GenerateImage) => {
                Some("POST /v1/chat/completions (image models)")
            }
            (Self::OpenRouter, Capability::Usage) => Some("GET /v1/key"),
            (Self::DeepSeek, Capability::Usage) => Some("GET /user/balance"),
            (
                Self::Anthropic,
                Capability::Embed
                | Capability::GenerateImage
                | Capability::Tokenize
                | Capability::Usage
                | Capability::Compact,
            )
            | (Self::OpenAi, Capability::Tokenize | Capability::Usage)
            | (
                Self::Google,
                Capability::GenerateImage
                | Capability::Tokenize
                | Capability::Usage
                | Capability::Compact,
            )
            | (
                Self::LlamaCpp,
                Capability::ListModels
                | Capability::Embed
                | Capability::GenerateImage
                | Capability::Usage
                | Capability::WebSearch
                | Capability::Compact,
            )
            | (
                Self::Xai,
                Capability::CountTokens
                | Capability::ListModels
                | Capability::Embed
                | Capability::GenerateImage
                | Capability::Usage
                | Capability::WebSearch
                | Capability::Compact,
            )
            | (
                Self::OpenRouter,
                Capability::CountTokens
                | Capability::ListModels
                | Capability::Embed
                | Capability::Tokenize
                | Capability::WebSearch
                | Capability::Compact,
            )
            | (
                Self::DeepSeek,
                Capability::CountTokens
                | Capability::ListModels
                | Capability::Embed
                | Capability::GenerateImage
                | Capability::Tokenize
                | Capability::WebSearch
                | Capability::Compact,
            ) => None,
        }
    }
}

impl fmt::Display for Dialect {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// How a model's provider serves one capability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(tag = "support", rename_all = "snake_case")]
pub enum Support {
    /// The provider's own endpoint serves it.
    Native {
        dialect: Dialect,
        /// Method and path, as [`Dialect::endpoint`] gives them.
        endpoint: &'static str,
    },
    /// The provider's API has no such operation (or eukhe does not know of
    /// one).
    Unsupported,
}

/// One capability and its support.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub struct CapabilitySupport {
    pub capability: Capability,
    #[serde(flatten)]
    pub support: Support,
}

/// What one model's provider supports: one entry per [`Capability::ALL`],
/// in that order. Models of one provider that share an API and a base URL
/// share their capabilities.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Capabilities {
    pub provider: String,
    pub api: String,
    pub base_url: String,
    pub entries: Vec<CapabilitySupport>,
}

impl Capabilities {
    /// The support of `capability`.
    #[must_use]
    pub fn support(&self, capability: Capability) -> Support {
        self.entries
            .iter()
            .find(|entry| entry.capability == capability)
            .map_or(Support::Unsupported, |entry| entry.support)
    }
}

/// The capabilities of `model`'s provider, from the shipped quirks rulebook.
#[must_use]
pub fn capabilities_of(model: &Model) -> Capabilities {
    let quirks = Quirks::for_lookup(model, Lookup::Capabilities);
    Capabilities {
        provider: model.provider.clone(),
        api: model.api.clone(),
        base_url: model.base_url.clone(),
        entries: Capability::ALL
            .into_iter()
            .map(|capability| CapabilitySupport {
                capability,
                support: quirks
                    .endpoint(capability)
                    .and_then(|dialect| {
                        dialect
                            .endpoint(capability)
                            .map(|endpoint| Support::Native { dialect, endpoint })
                    })
                    .unwrap_or(Support::Unsupported),
            })
            .collect(),
    }
}

/// A capability the model's provider does not have.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("provider `{provider}` does not support {capability}")]
pub struct Unsupported {
    pub capability: Capability,
    pub provider: String,
}

/// Why a capability operation failed.
#[derive(Debug, Clone, thiserror::Error)]
pub enum CapabilityError {
    /// The provider has no such operation.
    #[error(transparent)]
    Unsupported(#[from] Unsupported),
    /// Setup (unknown provider, missing auth) or the request failed.
    #[error("{0}")]
    Request(Thrown),
}

impl From<Thrown> for CapabilityError {
    fn from(error: Thrown) -> Self {
        Self::Request(error)
    }
}

/// Options of a capability operation: auth, transport and lifecycle, like
/// a chat request's. `Models` resolves the provider's auth into it.
#[derive(Debug, Clone, Default)]
pub struct CapabilityOptions {
    pub request: ProviderRequestOptions,
}

/// The input-token count of a request.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TokenCount {
    pub input_tokens: u64,
}

/// One model a provider lists.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ListedModel {
    pub id: String,
    /// The display name, when the provider gives one.
    pub name: Option<String>,
    /// The context window in tokens, when the provider gives one.
    pub context_window: Option<u64>,
    /// The output cap in tokens, when the provider gives one.
    pub max_output_tokens: Option<u64>,
}

/// An embedding request: the embedding model and the texts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmbedRequest {
    /// The provider's embedding model id (not the chat model's).
    pub model: String,
    pub inputs: Vec<String>,
}

/// The vectors of an embedding request, one per input, in input order.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Embeddings {
    pub model: String,
    pub vectors: Vec<Vec<f64>>,
    /// Input tokens billed, when the provider reports them.
    pub input_tokens: Option<u64>,
}

/// An image-generation request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImageRequest {
    /// The provider's image model id.
    pub model: String,
    pub prompt: String,
    /// How many images; at least 1.
    pub count: u32,
}

/// One generated image.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum GeneratedImage {
    /// Inline image bytes, base64.
    Base64 {
        data: String,
        mime_type: Option<String>,
    },
    /// A URL the provider hosts the image at.
    Url { url: String },
}

/// The images of an image-generation request.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct GeneratedImages {
    pub images: Vec<GeneratedImage>,
}

/// Token ids of a text, in the model's vocabulary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Tokens {
    pub ids: Vec<u64>,
}

/// One currency balance of an account.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Balance {
    pub currency: String,
    /// Decimal strings, as the provider reports them.
    pub total: String,
    pub granted: String,
    pub topped_up: String,
}

/// An account usage query's answer, in the shape the provider reports.
#[derive(Debug, Clone, PartialEq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum AccountUsage {
    /// Credits spent against an optional limit (`OpenRouter` keys), in USD.
    Credits {
        label: Option<String>,
        used: f64,
        limit: Option<f64>,
        remaining: Option<f64>,
        free_tier: bool,
    },
    /// Prepaid balances (`DeepSeek`).
    Balance {
        available: bool,
        balances: Vec<Balance>,
    },
}

/// A provider-native web search request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WebSearchRequest {
    pub query: String,
    /// The most searches the provider may run for the query; the
    /// provider's default when absent.
    pub max_searches: Option<u32>,
}

/// One source a web search answer cites.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct WebSource {
    pub url: String,
    pub title: Option<String>,
}

/// A web search answer: the model's text and the sources it used, in
/// first-seen order without duplicate URLs.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct WebSearchResult {
    pub answer: String,
    pub sources: Vec<WebSource>,
}

/// A remotely compacted conversation: the provider's replacement items,
/// opaque (they may carry encrypted content), to send as the new input.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Compaction {
    pub items: Vec<JsonValue>,
}
