//! The `kimi-coding` provider. Port of `providers/kimi-coding.ts`.

use std::sync::Arc;

use super::chat_models;
use super::kimi_coding_models::KIMI_CODING_MODELS;
use crate::api::builtin::anthropic_messages_api;
use crate::auth::oauth::load_kimi_coding_oauth;
use crate::auth::{env_api_key_auth, lazy_oauth, LazyOAuthInput, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `kimiCodingProvider()`.
#[must_use]
pub fn kimi_coding_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "kimi-coding".to_owned(),
        name: Some("Kimi For Coding".to_owned()),
        base_url: Some("https://api.kimi.com/coding".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Kimi API key", &["KIMI_API_KEY"])),
            oauth: Some(lazy_oauth(LazyOAuthInput {
                name: "Kimi Code (subscription)".to_owned(),
                is_subscription: Some(true),
                login_label: Some("Sign in with Kimi Code".to_owned()),
                load: Arc::new(load_kimi_coding_oauth),
            })),
        },
        models: chat_models(&KIMI_CODING_MODELS),
        api: Some(ProviderApi::Single(anthropic_messages_api())),
        ..CreateProviderOptions::default()
    })
}
