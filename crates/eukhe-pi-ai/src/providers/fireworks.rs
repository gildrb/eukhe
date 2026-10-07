//! The `fireworks` provider. Port of `providers/fireworks.ts`.

use eukhe_types::pi_ai::IndexMap;

use super::chat_models;
use super::fireworks_models::FIREWORKS_MODELS;
use crate::api::builtin::{anthropic_messages_api, openai_completions_api};
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `fireworksProvider()`.
#[must_use]
pub fn fireworks_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "fireworks".to_owned(),
        name: Some("Fireworks".to_owned()),
        base_url: Some("https://api.fireworks.ai/inference".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "Fireworks API key",
                &["FIREWORKS_API_KEY"],
            )),
            oauth: None,
        },
        models: chat_models(&FIREWORKS_MODELS),
        api: Some(ProviderApi::ByApi(IndexMap::from([
            ("anthropic-messages".to_owned(), anthropic_messages_api()),
            ("openai-completions".to_owned(), openai_completions_api()),
        ]))),
        ..CreateProviderOptions::default()
    })
}
