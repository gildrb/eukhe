//! Built-in provider factories, their generated model catalogs, and the
//! provider helpers they share (port of `src/providers/`).

pub mod all;
pub mod amazon_bedrock;
pub mod amazon_bedrock_models;
pub mod ant_ling;
pub mod ant_ling_models;
pub mod anthropic;
pub mod anthropic_models;
pub mod azure;
pub mod azure_models;
pub mod baseten;
pub mod baseten_models;
pub mod cerebras;
pub mod cerebras_models;
pub mod cloudflare_ai_gateway;
pub mod cloudflare_ai_gateway_models;
pub mod cloudflare_auth;
pub mod cloudflare_stream;
pub mod cloudflare_workers_ai;
pub mod cloudflare_workers_ai_models;
pub mod deepseek;
pub mod deepseek_models;
pub mod faux;
pub mod faux_script;
pub mod fireworks;
pub mod fireworks_models;
pub mod github_copilot;
pub mod github_copilot_models;
pub mod google;
pub mod google_models;
pub mod google_vertex;
pub mod google_vertex_models;
pub mod groq;
pub mod groq_models;
pub mod huggingface;
pub mod huggingface_models;
pub mod images;
pub mod kimi_coding;
pub mod kimi_coding_models;
pub mod meta;
pub mod meta_models;
pub mod minimax;
pub mod minimax_cn;
pub mod minimax_cn_models;
pub mod minimax_models;
pub mod mistral;
pub mod mistral_models;
pub mod moonshotai;
pub mod moonshotai_cn;
pub mod moonshotai_cn_models;
pub mod moonshotai_models;
pub mod nvidia;
pub mod nvidia_models;
pub mod openai;
pub mod openai_codex;
pub mod openai_codex_models;
pub mod openai_models;
pub mod opencode;
pub mod opencode_go;
pub mod opencode_go_models;
pub mod opencode_headers;
pub mod opencode_models;
pub mod openrouter;
pub mod openrouter_models;
pub mod prime_inference;
pub mod prime_inference_models;
pub mod qwen_token_plan;
pub mod qwen_token_plan_cn;
pub mod qwen_token_plan_cn_models;
pub mod qwen_token_plan_individual;
pub mod qwen_token_plan_individual_models;
pub mod qwen_token_plan_models;
pub mod radius;
pub mod radius_config;
pub mod radius_models;
pub mod together;
pub mod together_models;
pub mod typesafe;
pub mod typesafe_models;
pub mod vercel_ai_gateway;
pub mod vercel_ai_gateway_models;
pub mod xai;
pub mod xai_models;
pub mod xiaomi;
pub mod xiaomi_models;
pub mod xiaomi_token_plan_ams;
pub mod xiaomi_token_plan_ams_models;
pub mod xiaomi_token_plan_cn;
pub mod xiaomi_token_plan_cn_models;
pub mod xiaomi_token_plan_sgp;
pub mod xiaomi_token_plan_sgp_models;
pub mod zai;
pub mod zai_coding_cn;
pub mod zai_coding_cn_models;
pub mod zai_models;

use eukhe_types::pi_ai::AnyModel;

use crate::model_catalog::{ChatModelCatalog, ClassifierModelCatalog, ImageModelCatalog};

/// A generated chat catalog as provider models (TS
/// `Object.values(X_MODELS)`).
pub(crate) fn chat_models(catalog: &ChatModelCatalog) -> Vec<AnyModel> {
    catalog.values().cloned().map(AnyModel::Chat).collect()
}

/// A generated image catalog as provider models.
pub(crate) fn image_models(catalog: &ImageModelCatalog) -> Vec<AnyModel> {
    catalog.values().cloned().map(AnyModel::Image).collect()
}

/// A generated classifier catalog as provider models.
pub(crate) fn classifier_models(catalog: &ClassifierModelCatalog) -> Vec<AnyModel> {
    catalog
        .values()
        .cloned()
        .map(AnyModel::Classifier)
        .collect()
}
