//! The `meta` provider. Port of `providers/meta.ts`.

use std::sync::Arc;

use super::chat_models;
use super::meta_models::META_MODELS;
use crate::api::builtin::openai_responses_api;
use crate::auth::oauth::load_meta_oauth;
use crate::auth::{env_api_key_auth, lazy_oauth, LazyOAuthInput, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `metaProvider()`.
#[must_use]
pub fn meta_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "meta".to_owned(),
        name: Some("Meta".to_owned()),
        base_url: Some("https://api.meta.ai/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Meta Model API key", &["META_API_KEY"])),
            oauth: Some(lazy_oauth(LazyOAuthInput {
                name: "Meta (Muse subscription)".to_owned(),
                is_subscription: Some(true),
                login_label: Some("Sign in with Meta".to_owned()),
                load: Arc::new(load_meta_oauth),
            })),
        },
        models: chat_models(&META_MODELS),
        api: Some(ProviderApi::Single(openai_responses_api())),
        ..CreateProviderOptions::default()
    })
}
