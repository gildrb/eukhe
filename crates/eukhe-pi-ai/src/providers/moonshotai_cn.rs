//! The `moonshotai-cn` provider. Port of `providers/moonshotai-cn.ts`.

use super::chat_models;
use super::moonshotai_cn_models::MOONSHOTAI_CN_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `moonshotaiCnProvider()`.
#[must_use]
pub fn moonshotai_cn_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "moonshotai-cn".to_owned(),
        name: Some("Moonshot AI CN".to_owned()),
        base_url: Some("https://api.moonshot.cn/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "Moonshot AI API key",
                &["MOONSHOT_API_KEY"],
            )),
            oauth: None,
        },
        models: chat_models(&MOONSHOTAI_CN_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
