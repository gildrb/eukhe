//! The `zai` provider. Port of `providers/zai.ts`.

use super::chat_models;
use super::zai_models::ZAI_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `zaiProvider()`.
#[must_use]
pub fn zai_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "zai".to_owned(),
        name: Some("Z.AI".to_owned()),
        base_url: Some("https://api.z.ai/api/coding/paas/v4".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Z.AI API key", &["ZAI_API_KEY"])),
            oauth: None,
        },
        models: chat_models(&ZAI_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
