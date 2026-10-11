//! The `ant-ling` provider. Port of `providers/ant-ling.ts`.

use super::ant_ling_models::ANT_LING_MODELS;
use super::chat_models;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `antLingProvider()`.
#[must_use]
pub fn ant_ling_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "ant-ling".to_owned(),
        name: Some("Ant Ling".to_owned()),
        base_url: Some("https://api.ant-ling.com/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Ant Ling API key", &["ANT_LING_API_KEY"])),
            oauth: None,
        },
        models: chat_models(&ANT_LING_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
