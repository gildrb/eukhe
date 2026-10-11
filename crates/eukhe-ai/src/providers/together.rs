//! The `together` provider. Port of `providers/together.ts`.

use super::chat_models;
use super::together_models::TOGETHER_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `togetherProvider()`.
#[must_use]
pub fn together_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "together".to_owned(),
        name: Some("Together".to_owned()),
        base_url: Some("https://api.together.ai/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Together API key", &["TOGETHER_API_KEY"])),
            oauth: None,
        },
        models: chat_models(&TOGETHER_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
