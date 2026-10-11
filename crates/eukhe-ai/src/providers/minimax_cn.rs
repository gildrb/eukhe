//! The `minimax-cn` provider. Port of `providers/minimax-cn.ts`.

use super::chat_models;
use super::minimax_cn_models::MINIMAX_CN_MODELS;
use crate::api::builtin::anthropic_messages_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `minimaxCnProvider()`.
#[must_use]
pub fn minimax_cn_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "minimax-cn".to_owned(),
        name: Some("MiniMax CN".to_owned()),
        base_url: Some("https://api.minimaxi.com/anthropic".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "MiniMax CN API key",
                &["MINIMAX_CN_API_KEY"],
            )),
            oauth: None,
        },
        models: chat_models(&MINIMAX_CN_MODELS),
        api: Some(ProviderApi::Single(anthropic_messages_api())),
        ..CreateProviderOptions::default()
    })
}
