//! The `baseten` provider. Port of `providers/baseten.ts`.

use super::baseten_models::BASETEN_MODELS;
use super::chat_models;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `basetenProvider()`.
#[must_use]
pub fn baseten_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "baseten".to_owned(),
        name: Some("Baseten".to_owned()),
        base_url: Some("https://inference.baseten.co/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Baseten API key", &["BASETEN_API_KEY"])),
            oauth: None,
        },
        models: chat_models(&BASETEN_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
