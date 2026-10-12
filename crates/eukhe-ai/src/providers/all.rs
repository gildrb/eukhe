//! Every built-in provider and typed reads of the generated catalog. Port of
//! `providers/all.ts`.

use eukhe_types::pi_ai::{AnyModel, ClassifierModel, ImageModel, Model};

use super::amazon_bedrock::amazon_bedrock_provider;
use super::ant_ling::ant_ling_provider;
use super::anthropic::anthropic_provider;
use super::azure::azure_provider;
use super::baseten::baseten_provider;
use super::cerebras::cerebras_provider;
use super::cloudflare_ai_gateway::cloudflare_ai_gateway_provider;
use super::cloudflare_workers_ai::cloudflare_workers_ai_provider;
use super::deepseek::deepseek_provider;
use super::fireworks::fireworks_provider;
use super::github_copilot::github_copilot_provider;
use super::google::google_provider;
use super::google_vertex::google_vertex_provider;
use super::groq::groq_provider;
use super::huggingface::huggingface_provider;
use super::kimi_coding::kimi_coding_provider;
use super::meta::meta_provider;
use super::minimax::minimax_provider;
use super::minimax_cn::minimax_cn_provider;
use super::mistral::mistral_provider;
use super::moonshotai::moonshotai_provider;
use super::moonshotai_cn::moonshotai_cn_provider;
use super::nvidia::nvidia_provider;
use super::openai::openai_provider;
use super::openai_codex::openai_codex_provider;
use super::opencode::opencode_provider;
use super::opencode_go::opencode_go_provider;
use super::openrouter::openrouter_provider;
use super::prime_inference::prime_inference_provider;
use super::qwen_token_plan::qwen_token_plan_provider;
use super::qwen_token_plan_cn::qwen_token_plan_cn_provider;
use super::qwen_token_plan_individual::qwen_token_plan_individual_provider;
pub use super::radius::radius_provider;
use super::radius::RadiusProviderOptions;
use super::together::together_provider;
use super::typesafe::typesafe_provider;
use super::vercel_ai_gateway::vercel_ai_gateway_provider;
use super::xai::xai_provider;
use super::xiaomi::xiaomi_provider;
use super::xiaomi_token_plan_ams::xiaomi_token_plan_ams_provider;
use super::xiaomi_token_plan_cn::xiaomi_token_plan_cn_provider;
use super::xiaomi_token_plan_sgp::xiaomi_token_plan_sgp_provider;
use super::zai::zai_provider;
use super::zai_coding_cn::zai_coding_cn_provider;
use crate::models::{create_models, CreateModelsOptions, Models, Provider};
use crate::models_generated::{CLASSIFIER_MODELS, IMAGE_MODELS, MODELS};

/// Typed read of one generated built-in chat model.
#[must_use]
pub fn get_builtin_model(provider: &str, model_id: &str) -> Option<Model> {
    MODELS.get(provider)?.get(model_id).cloned()
}

/// Typed read of one generated built-in image model.
#[must_use]
pub fn get_builtin_image_model(provider: &str, model_id: &str) -> Option<ImageModel> {
    IMAGE_MODELS.get(provider)?.get(model_id).cloned()
}

/// Typed read of one generated built-in classifier model.
#[must_use]
pub fn get_builtin_classifier_model(provider: &str, model_id: &str) -> Option<ClassifierModel> {
    CLASSIFIER_MODELS.get(provider)?.get(model_id).cloned()
}

/// Providers present in the generated catalog. Purely dynamic providers
/// without a static catalog entry are not listed.
#[must_use]
pub fn get_builtin_providers() -> Vec<&'static str> {
    MODELS.keys().copied().collect()
}

/// Generated chat models of a built-in provider (none for unknown ids).
#[must_use]
pub fn get_builtin_models(provider: &str) -> Vec<Model> {
    MODELS
        .get(provider)
        .map(|models| models.values().cloned().collect())
        .unwrap_or_default()
}

/// Generated image models of a built-in provider.
#[must_use]
pub fn get_builtin_image_models(provider: &str) -> Vec<ImageModel> {
    IMAGE_MODELS
        .get(provider)
        .map(|models| models.values().cloned().collect())
        .unwrap_or_default()
}

/// Generated classifier models of a built-in provider.
#[must_use]
pub fn get_builtin_classifier_models(provider: &str) -> Vec<ClassifierModel> {
    CLASSIFIER_MODELS
        .get(provider)
        .map(|models| models.values().cloned().collect())
        .unwrap_or_default()
}

/// Generated models of every type of a built-in provider.
#[must_use]
pub fn get_all_builtin_models(provider: &str) -> Vec<AnyModel> {
    let mut models: Vec<AnyModel> = get_builtin_models(provider)
        .into_iter()
        .map(AnyModel::Chat)
        .collect();
    models.extend(
        get_builtin_image_models(provider)
            .into_iter()
            .map(AnyModel::Image),
    );
    models.extend(
        get_builtin_classifier_models(provider)
            .into_iter()
            .map(AnyModel::Classifier),
    );
    models
}

/// All built-in providers, freshly constructed. Includes the eukhe
/// `prime-inference` provider.
#[must_use]
pub fn builtin_providers() -> Vec<Provider> {
    vec![
        amazon_bedrock_provider(),
        ant_ling_provider(),
        anthropic_provider(),
        azure_provider(),
        baseten_provider(),
        cerebras_provider(),
        cloudflare_ai_gateway_provider(),
        cloudflare_workers_ai_provider(),
        deepseek_provider(),
        fireworks_provider(),
        github_copilot_provider(),
        google_provider(),
        google_vertex_provider(),
        groq_provider(),
        huggingface_provider(),
        kimi_coding_provider(),
        meta_provider(),
        minimax_provider(),
        minimax_cn_provider(),
        mistral_provider(),
        moonshotai_provider(),
        moonshotai_cn_provider(),
        nvidia_provider(),
        openai_provider(),
        openai_codex_provider(),
        opencode_provider(),
        opencode_go_provider(),
        openrouter_provider(),
        // eukhe addition: the Prime Inference provider.
        prime_inference_provider(),
        qwen_token_plan_provider(),
        qwen_token_plan_cn_provider(),
        qwen_token_plan_individual_provider(),
        radius_provider(RadiusProviderOptions::default()),
        together_provider(),
        typesafe_provider(),
        vercel_ai_gateway_provider(),
        xai_provider(),
        xiaomi_provider(),
        xiaomi_token_plan_ams_provider(),
        xiaomi_token_plan_cn_provider(),
        xiaomi_token_plan_sgp_provider(),
        zai_provider(),
        zai_coding_cn_provider(),
    ]
}

/// A `Models` collection with every built-in provider registered.
#[must_use]
pub fn builtin_models(options: CreateModelsOptions) -> Models {
    let models = create_models(options);
    for provider in builtin_providers() {
        models.set_provider(provider);
    }
    models
}
