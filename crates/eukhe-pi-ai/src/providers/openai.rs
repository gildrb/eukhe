//! The `openai` provider. Port of `providers/openai.ts`.

use std::sync::Arc;

use super::chat_models;
use super::openai_models::OPENAI_MODELS;
use crate::api::builtin::openai_responses_api;
use crate::auth::oauth::load_openai_chatgpt_oauth;
use crate::auth::{env_api_key_auth, lazy_oauth, LazyOAuthInput, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `openaiProvider()`.
#[must_use]
pub fn openai_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "openai".to_owned(),
        name: Some("OpenAI".to_owned()),
        base_url: Some("https://api.openai.com/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("OpenAI API key", &["OPENAI_API_KEY"])),
            oauth: Some(lazy_oauth(LazyOAuthInput {
                name: "OpenAI (ChatGPT subscription)".to_owned(),
                is_subscription: Some(true),
                login_label: Some("Sign in with ChatGPT".to_owned()),
                load: Arc::new(load_openai_chatgpt_oauth),
            })),
        },
        models: chat_models(&OPENAI_MODELS),
        api: Some(ProviderApi::Single(openai_responses_api())),
        ..CreateProviderOptions::default()
    })
}
