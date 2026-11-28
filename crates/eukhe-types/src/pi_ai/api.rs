//! API and provider identifiers (`KnownApi`, `KnownProvider`, ...).
//!
//! TS `Api = KnownApi | (string & {})` is an open string; the Rust aliases
//! are `String` and the `Known*` enums name the built-in members.

use super::string_enum::string_enum;

string_enum! {
    /// APIs with a built-in implementation module.
    pub enum KnownApi {
        OpenAICompletions => "openai-completions",
        MistralConversations => "mistral-conversations",
        OpenAIResponses => "openai-responses",
        AzureOpenAIResponses => "azure-openai-responses",
        OpenAICodexResponses => "openai-codex-responses",
        AnthropicMessages => "anthropic-messages",
        BedrockConverseStream => "bedrock-converse-stream",
        GoogleGenerativeAI => "google-generative-ai",
        GoogleVertex => "google-vertex",
        PiMessages => "pi-messages",
    }
}

/// TS `Api = KnownApi | (string & {})`: a known API, or any other wire
/// string kept in [`Api::Other`] so it round-trips.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Api {
    /// A built-in API.
    Known(KnownApi),
    /// Any other wire string.
    Other(String),
}

impl Api {
    /// The wire string.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::Known(api) => api.as_str(),
            Self::Other(api) => api,
        }
    }

    /// The API named by a wire string; unknown strings land in
    /// [`Self::Other`](enum@Self::Other).
    #[must_use]
    pub fn parse(value: &str) -> Self {
        KnownApi::parse(value).map_or_else(|| Self::Other(value.to_owned()), Self::Known)
    }
}

impl std::fmt::Display for Api {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self.as_str())
    }
}

impl From<KnownApi> for Api {
    fn from(api: KnownApi) -> Self {
        Self::Known(api)
    }
}

impl From<&str> for Api {
    fn from(api: &str) -> Self {
        Self::parse(api)
    }
}

impl serde::Serialize for Api {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

impl<'de> serde::Deserialize<'de> for Api {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(Self::parse(&String::deserialize(deserializer)?))
    }
}

string_enum! {
    /// Image-generation APIs with a built-in implementation module.
    pub enum KnownImageApi {
        OpenRouterImages => "openrouter-images",
    }
}

/// TS `ImageApi = KnownImageApi | (string & {})`.
pub type ImageApi = String;

string_enum! {
    /// Classifier APIs with a built-in implementation module.
    pub enum KnownClassifierApi {
        TypesafeSystemOne => "typesafe-system-one",
        CloudflareWorkersAISystemOne => "cloudflare-workers-ai-system-one",
        LlamaCppClassify => "llama-cpp-classify",
        OpenAIDecisions => "openai-decisions",
    }
}

/// TS `ClassifierApi = KnownClassifierApi | (string & {})`.
pub type ClassifierApi = String;

string_enum! {
    /// Providers with a built-in catalog.
    pub enum KnownProvider {
        AmazonBedrock => "amazon-bedrock",
        AntLing => "ant-ling",
        Anthropic => "anthropic",
        Google => "google",
        GoogleVertex => "google-vertex",
        OpenAI => "openai",
        Azure => "azure",
        OpenAICodex => "openai-codex",
        Radius => "radius",
        Typesafe => "typesafe",
        Nvidia => "nvidia",
        Deepseek => "deepseek",
        GithubCopilot => "github-copilot",
        Xai => "xai",
        Groq => "groq",
        Cerebras => "cerebras",
        OpenRouter => "openrouter",
        VercelAIGateway => "vercel-ai-gateway",
        Zai => "zai",
        ZaiCodingCn => "zai-coding-cn",
        Mistral => "mistral",
        Minimax => "minimax",
        MinimaxCn => "minimax-cn",
        MoonshotAI => "moonshotai",
        MoonshotAICn => "moonshotai-cn",
        Huggingface => "huggingface",
        Fireworks => "fireworks",
        Together => "together",
        Baseten => "baseten",
        Opencode => "opencode",
        OpencodeGo => "opencode-go",
        KimiCoding => "kimi-coding",
        Meta => "meta",
        CloudflareWorkersAI => "cloudflare-workers-ai",
        CloudflareAIGateway => "cloudflare-ai-gateway",
        QwenTokenPlan => "qwen-token-plan",
        QwenTokenPlanCn => "qwen-token-plan-cn",
        QwenTokenPlanIndividual => "qwen-token-plan-individual",
        Xiaomi => "xiaomi",
        XiaomiTokenPlanCn => "xiaomi-token-plan-cn",
        XiaomiTokenPlanAms => "xiaomi-token-plan-ams",
        XiaomiTokenPlanSgp => "xiaomi-token-plan-sgp",
    }
}

/// TS `ProviderId = KnownProvider | string`: a known provider, or any
/// other wire string kept in [`ProviderId::Other`] so it round-trips.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ProviderId {
    /// A provider with a built-in catalog.
    Known(KnownProvider),
    /// Any other wire string.
    Other(String),
}

impl ProviderId {
    /// The wire string.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::Known(provider) => provider.as_str(),
            Self::Other(provider) => provider,
        }
    }

    /// The provider named by a wire string; unknown strings land in
    /// [`Self::Other`](enum@Self::Other).
    #[must_use]
    pub fn parse(value: &str) -> Self {
        KnownProvider::parse(value).map_or_else(|| Self::Other(value.to_owned()), Self::Known)
    }
}

impl std::fmt::Display for ProviderId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self.as_str())
    }
}

impl From<KnownProvider> for ProviderId {
    fn from(provider: KnownProvider) -> Self {
        Self::Known(provider)
    }
}

impl From<&str> for ProviderId {
    fn from(provider: &str) -> Self {
        Self::parse(provider)
    }
}

impl serde::Serialize for ProviderId {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

impl<'de> serde::Deserialize<'de> for ProviderId {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(Self::parse(&String::deserialize(deserializer)?))
    }
}

#[cfg(test)]
mod tests {
    use super::{Api, KnownApi, ProviderId};

    #[test]
    fn api_round_trips_known_and_unknown_words() {
        let known: Api = serde_json::from_str("\"openai-completions\"").expect("known api");
        assert_eq!(known, Api::Known(KnownApi::OpenAICompletions));
        assert_eq!(
            serde_json::to_string(&known).expect("serialize"),
            "\"openai-completions\""
        );
        let unknown: Api = serde_json::from_str("\"my-proxy\"").expect("unknown api");
        assert_eq!(unknown, Api::Other("my-proxy".to_owned()));
        assert_eq!(
            serde_json::to_string(&unknown).expect("serialize"),
            "\"my-proxy\""
        );
    }

    #[test]
    fn provider_round_trips_known_and_unknown_words() {
        let known: ProviderId = serde_json::from_str("\"anthropic\"").expect("known provider");
        assert_eq!(
            serde_json::to_string(&known).expect("serialize"),
            "\"anthropic\""
        );
        let unknown: ProviderId = serde_json::from_str("\"my-gateway\"").expect("unknown provider");
        assert_eq!(unknown, ProviderId::Other("my-gateway".to_owned()));
        assert_eq!(
            serde_json::to_string(&unknown).expect("serialize"),
            "\"my-gateway\""
        );
    }
}
