//! The `xiaomi` provider. Port of `providers/xiaomi.ts`.

use super::xiaomi_models::XIAOMI_MODELS;
use super::{builtin_baseline, chat_models};
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `xiaomiProvider()`.
#[must_use]
pub fn xiaomi_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "xiaomi".to_owned(),
        name: Some("Xiaomi".to_owned()),
        base_url: Some("https://api.xiaomimimo.com/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Xiaomi API key", &["XIAOMI_API_KEY"])),
            oauth: None,
        },
        models: builtin_baseline("xiaomi", || chat_models(&XIAOMI_MODELS)),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
