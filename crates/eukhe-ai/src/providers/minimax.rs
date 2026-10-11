//! The `minimax` provider. Port of `providers/minimax.ts`.

use super::chat_models;
use super::minimax_models::MINIMAX_MODELS;
use crate::api::builtin::anthropic_messages_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `minimaxProvider()`.
#[must_use]
pub fn minimax_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "minimax".to_owned(),
        name: Some("MiniMax".to_owned()),
        base_url: Some("https://api.minimax.io/anthropic".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("MiniMax API key", &["MINIMAX_API_KEY"])),
            oauth: None,
        },
        models: chat_models(&MINIMAX_MODELS),
        api: Some(ProviderApi::Single(anthropic_messages_api())),
        ..CreateProviderOptions::default()
    })
}
