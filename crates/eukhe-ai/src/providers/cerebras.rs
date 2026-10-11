//! The `cerebras` provider. Port of `providers/cerebras.ts`.

use super::cerebras_models::CEREBRAS_MODELS;
use super::chat_models;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `cerebrasProvider()`.
#[must_use]
pub fn cerebras_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "cerebras".to_owned(),
        name: Some("Cerebras".to_owned()),
        base_url: Some("https://api.cerebras.ai/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Cerebras API key", &["CEREBRAS_API_KEY"])),
            oauth: None,
        },
        models: chat_models(&CEREBRAS_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
