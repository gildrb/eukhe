//! The `mistral` provider. Port of `providers/mistral.ts`.

use super::chat_models;
use super::mistral_models::MISTRAL_MODELS;
use crate::api::builtin::mistral_conversations_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `mistralProvider()`.
#[must_use]
pub fn mistral_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "mistral".to_owned(),
        name: Some("Mistral".to_owned()),
        base_url: Some("https://api.mistral.ai".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Mistral API key", &["MISTRAL_API_KEY"])),
            oauth: None,
        },
        models: chat_models(&MISTRAL_MODELS),
        api: Some(ProviderApi::Single(mistral_conversations_api())),
        ..CreateProviderOptions::default()
    })
}
