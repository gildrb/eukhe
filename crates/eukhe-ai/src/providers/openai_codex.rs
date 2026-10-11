//! The `openai-codex` provider. Port of `providers/openai-codex.ts`.

use std::sync::Arc;

use super::chat_models;
use super::openai_codex_models::OPENAI_CODEX_MODELS;
use crate::api::builtin::openai_codex_responses_api;
use crate::auth::oauth::load_openai_codex_oauth;
use crate::auth::{lazy_oauth, LazyOAuthInput, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `openaiCodexProvider()`.
#[must_use]
pub fn openai_codex_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "openai-codex".to_owned(),
        name: Some("OpenAI Codex (legacy)".to_owned()),
        base_url: Some("https://chatgpt.com/backend-api".to_owned()),
        auth: ProviderAuth {
            api_key: None,
            oauth: Some(lazy_oauth(LazyOAuthInput {
                name: "OpenAI (ChatGPT Plus/Pro)".to_owned(),
                is_subscription: Some(true),
                login_label: None,
                load: Arc::new(load_openai_codex_oauth),
            })),
        },
        models: chat_models(&OPENAI_CODEX_MODELS),
        api: Some(ProviderApi::Single(openai_codex_responses_api())),
        ..CreateProviderOptions::default()
    })
}
