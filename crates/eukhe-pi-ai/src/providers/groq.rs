//! The `groq` provider. Port of `providers/groq.ts`.

use super::chat_models;
use super::groq_models::GROQ_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `groqProvider()`.
#[must_use]
pub fn groq_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "groq".to_owned(),
        name: Some("Groq".to_owned()),
        base_url: Some("https://api.groq.com/openai/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Groq API key", &["GROQ_API_KEY"])),
            oauth: None,
        },
        models: chat_models(&GROQ_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
