//! The `xai` provider. Port of `providers/xai.ts`.

use std::sync::Arc;

use super::chat_models;
use super::xai_models::XAI_MODELS;
use crate::api::builtin::openai_responses_api;
use crate::auth::oauth::load_xai_oauth;
use crate::auth::{env_api_key_auth, lazy_oauth, LazyOAuthInput, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `xaiProvider()`.
#[must_use]
pub fn xai_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "xai".to_owned(),
        name: Some("xAI".to_owned()),
        base_url: Some("https://api.x.ai/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("xAI API key", &["XAI_API_KEY"])),
            oauth: Some(lazy_oauth(LazyOAuthInput {
                name: "xAI (Grok/X subscription)".to_owned(),
                is_subscription: Some(true),
                login_label: Some("Sign in with SuperGrok or X Premium".to_owned()),
                load: Arc::new(load_xai_oauth),
            })),
        },
        models: chat_models(&XAI_MODELS),
        api: Some(ProviderApi::Single(openai_responses_api())),
        ..CreateProviderOptions::default()
    })
}
