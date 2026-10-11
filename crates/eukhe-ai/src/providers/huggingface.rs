//! The `huggingface` provider. Port of `providers/huggingface.ts`.

use super::chat_models;
use super::huggingface_models::HUGGINGFACE_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `huggingfaceProvider()`.
#[must_use]
pub fn huggingface_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "huggingface".to_owned(),
        name: Some("Hugging Face".to_owned()),
        base_url: Some("https://router.huggingface.co/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Hugging Face token", &["HF_TOKEN"])),
            oauth: None,
        },
        models: chat_models(&HUGGINGFACE_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
