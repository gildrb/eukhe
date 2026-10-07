//! The generated catalogs of every built-in provider, keyed by provider id.
//! Port of `models.generated.ts`.

use std::sync::LazyLock;

use eukhe_types::pi_ai::IndexMap;

use crate::model_catalog::{ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog};
use crate::providers::{
    amazon_bedrock_models, ant_ling_models, anthropic_models, azure_models, baseten_models,
    cerebras_models, cloudflare_ai_gateway_models, cloudflare_workers_ai_models, deepseek_models,
    fireworks_models, github_copilot_models, google_models, google_vertex_models, groq_models,
    huggingface_models, kimi_coding_models, meta_models, minimax_cn_models, minimax_models,
    mistral_models, moonshotai_cn_models, moonshotai_models, nvidia_models, openai_codex_models,
    openai_models, opencode_go_models, opencode_models, openrouter_models,
    qwen_token_plan_cn_models, qwen_token_plan_individual_models, qwen_token_plan_models,
    radius_models, together_models, typesafe_models, vercel_ai_gateway_models, xai_models,
    xiaomi_models, xiaomi_token_plan_ams_models, xiaomi_token_plan_cn_models,
    xiaomi_token_plan_sgp_models, zai_coding_cn_models, zai_models,
};

/// Chat models of every built-in provider, in provider order.
pub static MODELS: LazyLock<IndexMap<&'static str, &'static ChatModelCatalog>> =
    LazyLock::new(|| {
        IndexMap::from([
            (
                "amazon-bedrock",
                &*amazon_bedrock_models::AMAZON_BEDROCK_MODELS,
            ),
            ("ant-ling", &*ant_ling_models::ANT_LING_MODELS),
            ("anthropic", &*anthropic_models::ANTHROPIC_MODELS),
            ("azure", &*azure_models::AZURE_MODELS),
            ("baseten", &*baseten_models::BASETEN_MODELS),
            ("cerebras", &*cerebras_models::CEREBRAS_MODELS),
            (
                "cloudflare-ai-gateway",
                &*cloudflare_ai_gateway_models::CLOUDFLARE_AI_GATEWAY_MODELS,
            ),
            (
                "cloudflare-workers-ai",
                &*cloudflare_workers_ai_models::CLOUDFLARE_WORKERS_AI_MODELS,
            ),
            ("deepseek", &*deepseek_models::DEEPSEEK_MODELS),
            ("fireworks", &*fireworks_models::FIREWORKS_MODELS),
            (
                "github-copilot",
                &*github_copilot_models::GITHUB_COPILOT_MODELS,
            ),
            ("google", &*google_models::GOOGLE_MODELS),
            (
                "google-vertex",
                &*google_vertex_models::GOOGLE_VERTEX_MODELS,
            ),
            ("groq", &*groq_models::GROQ_MODELS),
            ("huggingface", &*huggingface_models::HUGGINGFACE_MODELS),
            ("kimi-coding", &*kimi_coding_models::KIMI_CODING_MODELS),
            ("meta", &*meta_models::META_MODELS),
            ("minimax", &*minimax_models::MINIMAX_MODELS),
            ("minimax-cn", &*minimax_cn_models::MINIMAX_CN_MODELS),
            ("mistral", &*mistral_models::MISTRAL_MODELS),
            ("moonshotai", &*moonshotai_models::MOONSHOTAI_MODELS),
            (
                "moonshotai-cn",
                &*moonshotai_cn_models::MOONSHOTAI_CN_MODELS,
            ),
            ("nvidia", &*nvidia_models::NVIDIA_MODELS),
            ("openai", &*openai_models::OPENAI_MODELS),
            ("openai-codex", &*openai_codex_models::OPENAI_CODEX_MODELS),
            ("opencode", &*opencode_models::OPENCODE_MODELS),
            ("opencode-go", &*opencode_go_models::OPENCODE_GO_MODELS),
            ("openrouter", &*openrouter_models::OPENROUTER_MODELS),
            (
                "qwen-token-plan",
                &*qwen_token_plan_models::QWEN_TOKEN_PLAN_MODELS,
            ),
            (
                "qwen-token-plan-cn",
                &*qwen_token_plan_cn_models::QWEN_TOKEN_PLAN_CN_MODELS,
            ),
            (
                "qwen-token-plan-individual",
                &*qwen_token_plan_individual_models::QWEN_TOKEN_PLAN_INDIVIDUAL_MODELS,
            ),
            ("radius", &*radius_models::RADIUS_MODELS),
            ("together", &*together_models::TOGETHER_MODELS),
            ("typesafe", &*typesafe_models::TYPESAFE_MODELS),
            (
                "vercel-ai-gateway",
                &*vercel_ai_gateway_models::VERCEL_AI_GATEWAY_MODELS,
            ),
            ("xai", &*xai_models::XAI_MODELS),
            ("xiaomi", &*xiaomi_models::XIAOMI_MODELS),
            (
                "xiaomi-token-plan-ams",
                &*xiaomi_token_plan_ams_models::XIAOMI_TOKEN_PLAN_AMS_MODELS,
            ),
            (
                "xiaomi-token-plan-cn",
                &*xiaomi_token_plan_cn_models::XIAOMI_TOKEN_PLAN_CN_MODELS,
            ),
            (
                "xiaomi-token-plan-sgp",
                &*xiaomi_token_plan_sgp_models::XIAOMI_TOKEN_PLAN_SGP_MODELS,
            ),
            ("zai", &*zai_models::ZAI_MODELS),
            (
                "zai-coding-cn",
                &*zai_coding_cn_models::ZAI_CODING_CN_MODELS,
            ),
        ])
    });

/// Image models of every built-in provider, in provider order.
pub static IMAGE_MODELS: LazyLock<IndexMap<&'static str, &'static ImageModelCatalog>> =
    LazyLock::new(|| {
        IndexMap::from([
            (
                "amazon-bedrock",
                &*amazon_bedrock_models::AMAZON_BEDROCK_IMAGE_MODELS,
            ),
            ("ant-ling", &*ant_ling_models::ANT_LING_IMAGE_MODELS),
            ("anthropic", &*anthropic_models::ANTHROPIC_IMAGE_MODELS),
            ("azure", &*azure_models::AZURE_IMAGE_MODELS),
            ("baseten", &*baseten_models::BASETEN_IMAGE_MODELS),
            ("cerebras", &*cerebras_models::CEREBRAS_IMAGE_MODELS),
            (
                "cloudflare-ai-gateway",
                &*cloudflare_ai_gateway_models::CLOUDFLARE_AI_GATEWAY_IMAGE_MODELS,
            ),
            (
                "cloudflare-workers-ai",
                &*cloudflare_workers_ai_models::CLOUDFLARE_WORKERS_AI_IMAGE_MODELS,
            ),
            ("deepseek", &*deepseek_models::DEEPSEEK_IMAGE_MODELS),
            ("fireworks", &*fireworks_models::FIREWORKS_IMAGE_MODELS),
            (
                "github-copilot",
                &*github_copilot_models::GITHUB_COPILOT_IMAGE_MODELS,
            ),
            ("google", &*google_models::GOOGLE_IMAGE_MODELS),
            (
                "google-vertex",
                &*google_vertex_models::GOOGLE_VERTEX_IMAGE_MODELS,
            ),
            ("groq", &*groq_models::GROQ_IMAGE_MODELS),
            (
                "huggingface",
                &*huggingface_models::HUGGINGFACE_IMAGE_MODELS,
            ),
            (
                "kimi-coding",
                &*kimi_coding_models::KIMI_CODING_IMAGE_MODELS,
            ),
            ("meta", &*meta_models::META_IMAGE_MODELS),
            ("minimax", &*minimax_models::MINIMAX_IMAGE_MODELS),
            ("minimax-cn", &*minimax_cn_models::MINIMAX_CN_IMAGE_MODELS),
            ("mistral", &*mistral_models::MISTRAL_IMAGE_MODELS),
            ("moonshotai", &*moonshotai_models::MOONSHOTAI_IMAGE_MODELS),
            (
                "moonshotai-cn",
                &*moonshotai_cn_models::MOONSHOTAI_CN_IMAGE_MODELS,
            ),
            ("nvidia", &*nvidia_models::NVIDIA_IMAGE_MODELS),
            ("openai", &*openai_models::OPENAI_IMAGE_MODELS),
            (
                "openai-codex",
                &*openai_codex_models::OPENAI_CODEX_IMAGE_MODELS,
            ),
            ("opencode", &*opencode_models::OPENCODE_IMAGE_MODELS),
            (
                "opencode-go",
                &*opencode_go_models::OPENCODE_GO_IMAGE_MODELS,
            ),
            ("openrouter", &*openrouter_models::OPENROUTER_IMAGE_MODELS),
            (
                "qwen-token-plan",
                &*qwen_token_plan_models::QWEN_TOKEN_PLAN_IMAGE_MODELS,
            ),
            (
                "qwen-token-plan-cn",
                &*qwen_token_plan_cn_models::QWEN_TOKEN_PLAN_CN_IMAGE_MODELS,
            ),
            (
                "qwen-token-plan-individual",
                &*qwen_token_plan_individual_models::QWEN_TOKEN_PLAN_INDIVIDUAL_IMAGE_MODELS,
            ),
            ("radius", &*radius_models::RADIUS_IMAGE_MODELS),
            ("together", &*together_models::TOGETHER_IMAGE_MODELS),
            ("typesafe", &*typesafe_models::TYPESAFE_IMAGE_MODELS),
            (
                "vercel-ai-gateway",
                &*vercel_ai_gateway_models::VERCEL_AI_GATEWAY_IMAGE_MODELS,
            ),
            ("xai", &*xai_models::XAI_IMAGE_MODELS),
            ("xiaomi", &*xiaomi_models::XIAOMI_IMAGE_MODELS),
            (
                "xiaomi-token-plan-ams",
                &*xiaomi_token_plan_ams_models::XIAOMI_TOKEN_PLAN_AMS_IMAGE_MODELS,
            ),
            (
                "xiaomi-token-plan-cn",
                &*xiaomi_token_plan_cn_models::XIAOMI_TOKEN_PLAN_CN_IMAGE_MODELS,
            ),
            (
                "xiaomi-token-plan-sgp",
                &*xiaomi_token_plan_sgp_models::XIAOMI_TOKEN_PLAN_SGP_IMAGE_MODELS,
            ),
            ("zai", &*zai_models::ZAI_IMAGE_MODELS),
            (
                "zai-coding-cn",
                &*zai_coding_cn_models::ZAI_CODING_CN_IMAGE_MODELS,
            ),
        ])
    });

/// Classifier models of every built-in provider, in provider order.
pub static CLASSIFIER_MODELS: LazyLock<IndexMap<&'static str, &'static ClassifierModelCatalog>> =
    LazyLock::new(|| {
        IndexMap::from([
            (
                "amazon-bedrock",
                &*amazon_bedrock_models::AMAZON_BEDROCK_CLASSIFIER_MODELS,
            ),
            ("ant-ling", &*ant_ling_models::ANT_LING_CLASSIFIER_MODELS),
            ("anthropic", &*anthropic_models::ANTHROPIC_CLASSIFIER_MODELS),
            ("azure", &*azure_models::AZURE_CLASSIFIER_MODELS),
            ("baseten", &*baseten_models::BASETEN_CLASSIFIER_MODELS),
            ("cerebras", &*cerebras_models::CEREBRAS_CLASSIFIER_MODELS),
            (
                "cloudflare-ai-gateway",
                &*cloudflare_ai_gateway_models::CLOUDFLARE_AI_GATEWAY_CLASSIFIER_MODELS,
            ),
            (
                "cloudflare-workers-ai",
                &*cloudflare_workers_ai_models::CLOUDFLARE_WORKERS_AI_CLASSIFIER_MODELS,
            ),
            ("deepseek", &*deepseek_models::DEEPSEEK_CLASSIFIER_MODELS),
            ("fireworks", &*fireworks_models::FIREWORKS_CLASSIFIER_MODELS),
            (
                "github-copilot",
                &*github_copilot_models::GITHUB_COPILOT_CLASSIFIER_MODELS,
            ),
            ("google", &*google_models::GOOGLE_CLASSIFIER_MODELS),
            (
                "google-vertex",
                &*google_vertex_models::GOOGLE_VERTEX_CLASSIFIER_MODELS,
            ),
            ("groq", &*groq_models::GROQ_CLASSIFIER_MODELS),
            (
                "huggingface",
                &*huggingface_models::HUGGINGFACE_CLASSIFIER_MODELS,
            ),
            (
                "kimi-coding",
                &*kimi_coding_models::KIMI_CODING_CLASSIFIER_MODELS,
            ),
            ("meta", &*meta_models::META_CLASSIFIER_MODELS),
            ("minimax", &*minimax_models::MINIMAX_CLASSIFIER_MODELS),
            (
                "minimax-cn",
                &*minimax_cn_models::MINIMAX_CN_CLASSIFIER_MODELS,
            ),
            ("mistral", &*mistral_models::MISTRAL_CLASSIFIER_MODELS),
            (
                "moonshotai",
                &*moonshotai_models::MOONSHOTAI_CLASSIFIER_MODELS,
            ),
            (
                "moonshotai-cn",
                &*moonshotai_cn_models::MOONSHOTAI_CN_CLASSIFIER_MODELS,
            ),
            ("nvidia", &*nvidia_models::NVIDIA_CLASSIFIER_MODELS),
            ("openai", &*openai_models::OPENAI_CLASSIFIER_MODELS),
            (
                "openai-codex",
                &*openai_codex_models::OPENAI_CODEX_CLASSIFIER_MODELS,
            ),
            ("opencode", &*opencode_models::OPENCODE_CLASSIFIER_MODELS),
            (
                "opencode-go",
                &*opencode_go_models::OPENCODE_GO_CLASSIFIER_MODELS,
            ),
            (
                "openrouter",
                &*openrouter_models::OPENROUTER_CLASSIFIER_MODELS,
            ),
            (
                "qwen-token-plan",
                &*qwen_token_plan_models::QWEN_TOKEN_PLAN_CLASSIFIER_MODELS,
            ),
            (
                "qwen-token-plan-cn",
                &*qwen_token_plan_cn_models::QWEN_TOKEN_PLAN_CN_CLASSIFIER_MODELS,
            ),
            (
                "qwen-token-plan-individual",
                &*qwen_token_plan_individual_models::QWEN_TOKEN_PLAN_INDIVIDUAL_CLASSIFIER_MODELS,
            ),
            ("radius", &*radius_models::RADIUS_CLASSIFIER_MODELS),
            ("together", &*together_models::TOGETHER_CLASSIFIER_MODELS),
            ("typesafe", &*typesafe_models::TYPESAFE_CLASSIFIER_MODELS),
            (
                "vercel-ai-gateway",
                &*vercel_ai_gateway_models::VERCEL_AI_GATEWAY_CLASSIFIER_MODELS,
            ),
            ("xai", &*xai_models::XAI_CLASSIFIER_MODELS),
            ("xiaomi", &*xiaomi_models::XIAOMI_CLASSIFIER_MODELS),
            (
                "xiaomi-token-plan-ams",
                &*xiaomi_token_plan_ams_models::XIAOMI_TOKEN_PLAN_AMS_CLASSIFIER_MODELS,
            ),
            (
                "xiaomi-token-plan-cn",
                &*xiaomi_token_plan_cn_models::XIAOMI_TOKEN_PLAN_CN_CLASSIFIER_MODELS,
            ),
            (
                "xiaomi-token-plan-sgp",
                &*xiaomi_token_plan_sgp_models::XIAOMI_TOKEN_PLAN_SGP_CLASSIFIER_MODELS,
            ),
            ("zai", &*zai_models::ZAI_CLASSIFIER_MODELS),
            (
                "zai-coding-cn",
                &*zai_coding_cn_models::ZAI_CODING_CN_CLASSIFIER_MODELS,
            ),
        ])
    });
