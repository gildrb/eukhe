//! The `cloudflare-workers-ai` provider. Port of
//! `providers/cloudflare-workers-ai.ts`.

use eukhe_types::pi_ai::IndexMap;

use super::cloudflare_auth::cloudflare_workers_ai_auth;
use super::cloudflare_stream::{cloudflare_classifier, cloudflare_streams};
use super::cloudflare_workers_ai_models::{
    CLOUDFLARE_WORKERS_AI_CLASSIFIER_MODELS, CLOUDFLARE_WORKERS_AI_MODELS,
};
use super::{chat_models, classifier_models};
use crate::api::builtin::{cloudflare_workers_ai_system_one_api, openai_completions_api};
use crate::auth::ProviderAuth;
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `cloudflareWorkersAIProvider()`.
#[must_use]
pub fn cloudflare_workers_ai_provider() -> Provider {
    let mut models = chat_models(&CLOUDFLARE_WORKERS_AI_MODELS);
    models.extend(classifier_models(&CLOUDFLARE_WORKERS_AI_CLASSIFIER_MODELS));
    build_provider(CreateProviderOptions {
        id: "cloudflare-workers-ai".to_owned(),
        name: Some("Cloudflare Workers AI".to_owned()),
        auth: ProviderAuth {
            api_key: Some(cloudflare_workers_ai_auth()),
            oauth: None,
        },
        models,
        api: Some(ProviderApi::Single(cloudflare_streams(
            openai_completions_api(),
        ))),
        classifiers: Some(IndexMap::from([(
            "cloudflare-workers-ai-system-one".to_owned(),
            cloudflare_classifier(cloudflare_workers_ai_system_one_api()),
        )])),
        ..CreateProviderOptions::default()
    })
}
