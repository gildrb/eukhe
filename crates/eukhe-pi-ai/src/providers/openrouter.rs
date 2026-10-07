//! The `openrouter` provider. Port of `providers/openrouter.ts`.

use std::sync::Arc;

use eukhe_types::pi_ai::IndexMap;

use super::openrouter_models::{
    OPENROUTER_CLASSIFIER_MODELS, OPENROUTER_IMAGE_MODELS, OPENROUTER_MODELS,
};
use super::{chat_models, classifier_models, image_models};
use crate::api::builtin::{
    anthropic_messages_api, openai_completions_api, openrouter_images_api, typesafe_system_one_api,
};
use crate::auth::oauth::load_openrouter_oauth;
use crate::auth::{env_api_key_auth, lazy_oauth, LazyOAuthInput, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `openrouterProvider()`.
#[must_use]
pub fn openrouter_provider() -> Provider {
    let mut models = chat_models(&OPENROUTER_MODELS);
    models.extend(image_models(&OPENROUTER_IMAGE_MODELS));
    models.extend(classifier_models(&OPENROUTER_CLASSIFIER_MODELS));
    build_provider(CreateProviderOptions {
        id: "openrouter".to_owned(),
        name: Some("OpenRouter".to_owned()),
        base_url: Some("https://openrouter.ai/api/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "OpenRouter API key",
                &["OPENROUTER_API_KEY"],
            )),
            oauth: Some(lazy_oauth(LazyOAuthInput {
                name: "OpenRouter OAuth".to_owned(),
                is_subscription: None,
                login_label: Some("Sign in with OpenRouter".to_owned()),
                load: Arc::new(load_openrouter_oauth),
            })),
        },
        models,
        api: Some(ProviderApi::ByApi(IndexMap::from([
            ("anthropic-messages".to_owned(), anthropic_messages_api()),
            ("openai-completions".to_owned(), openai_completions_api()),
        ]))),
        images: Some(IndexMap::from([(
            "openrouter-images".to_owned(),
            openrouter_images_api(),
        )])),
        // OpenRouter serves TypeSafe's System One protocol at /api/v1/systemone.
        classifiers: Some(IndexMap::from([(
            "typesafe-system-one".to_owned(),
            typesafe_system_one_api(),
        )])),
        ..CreateProviderOptions::default()
    })
}
