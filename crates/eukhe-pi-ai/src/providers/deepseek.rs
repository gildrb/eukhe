//! The `deepseek` provider. Port of `providers/deepseek.ts`.

use super::chat_models;
use super::deepseek_models::DEEPSEEK_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `deepseekProvider()`.
#[must_use]
pub fn deepseek_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "deepseek".to_owned(),
        name: Some("DeepSeek".to_owned()),
        base_url: Some("https://api.deepseek.com".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("DeepSeek API key", &["DEEPSEEK_API_KEY"])),
            oauth: None,
        },
        models: chat_models(&DEEPSEEK_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
