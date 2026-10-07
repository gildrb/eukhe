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

/// TS `Api = KnownApi | (string & {})`.
pub type Api = String;

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
        /// eukhe addition: the Prime Inference provider.
        PrimeInference => "prime-inference",
    }
}

/// TS `ProviderId = KnownProvider | string`.
pub type ProviderId = String;
