//! The `openai` provider. Port of `providers/openai.ts`.

use std::sync::Arc;

use eukhe_types::pi_ai::{IndexMap, ModelType};

use super::openai_models::{OPENAI_CLASSIFIER_MODELS, OPENAI_MODELS};
use super::{chat_models, classifier_models};
use crate::api::builtin::{openai_decisions_api, openai_responses_api};
use crate::auth::oauth::load_openai_chatgpt_oauth;
use crate::auth::{env_api_key_auth, lazy_oauth, Credential, LazyOAuthInput, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};
use crate::utils::model_operations::is_model_type;

/// TS `openaiProvider()`.
#[must_use]
pub fn openai_provider() -> Provider {
    let mut models = chat_models(&OPENAI_MODELS);
    models.extend(classifier_models(&OPENAI_CLASSIFIER_MODELS));
    build_provider(CreateProviderOptions {
        id: "openai".to_owned(),
        name: Some("OpenAI".to_owned()),
        base_url: Some("https://api.openai.com/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("OpenAI API key", &["OPENAI_API_KEY"])),
            oauth: Some(lazy_oauth(LazyOAuthInput {
                name: "OpenAI (ChatGPT subscription)".to_owned(),
                is_subscription: Some(true),
                login_label: Some("Sign in with ChatGPT".to_owned()),
                load: Arc::new(load_openai_chatgpt_oauth),
            })),
        },
        models,
        // Sign in with ChatGPT tokens only reach the Responses API; the Decisions API rejects them.
        filter_all_models: Some(Arc::new(|models, credential| match credential {
            Some(Credential::OAuth(_)) => models
                .into_iter()
                .filter(|model| !is_model_type(model, ModelType::Classifier))
                .collect(),
            Some(Credential::ApiKey(_)) | None => models,
        })),
        api: Some(ProviderApi::Single(openai_responses_api())),
        classifiers: Some(IndexMap::from([(
            "openai-decisions".to_owned(),
            openai_decisions_api(),
        )])),
        ..CreateProviderOptions::default()
    })
}
