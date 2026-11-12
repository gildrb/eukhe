//! The `zai` provider. Port of `providers/zai.ts`. GLM rides Z.AI's
//! Anthropic endpoint (`https://api.z.ai/api/anthropic`); GLM-5.3-Flash and
//! the high-speed lanes ride its `OpenAI`-compatible coding endpoint.

use eukhe_types::pi_ai::IndexMap;

use super::zai_models::ZAI_MODELS;
use super::{builtin_baseline, chat_models};
use crate::api::builtin::{anthropic_messages_api, openai_completions_api};
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
        models: builtin_baseline("zai", || chat_models(&ZAI_MODELS)),
        api: Some(ProviderApi::ByApi(IndexMap::from([
            ("anthropic-messages".to_owned(), anthropic_messages_api()),
            ("openai-completions".to_owned(), openai_completions_api()),
        ]))),
        ..CreateProviderOptions::default()
    })
}
