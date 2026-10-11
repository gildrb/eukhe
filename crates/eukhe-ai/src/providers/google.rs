//! The `google` provider. Port of `providers/google.ts`.

use super::chat_models;
use super::google_models::GOOGLE_MODELS;
use crate::api::builtin::google_generative_ai_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `googleProvider()`.
#[must_use]
pub fn google_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "google".to_owned(),
        name: Some("Google".to_owned()),
        base_url: Some("https://generativelanguage.googleapis.com/v1beta".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("Gemini API key", &["GEMINI_API_KEY"])),
            oauth: None,
        },
        models: chat_models(&GOOGLE_MODELS),
        api: Some(ProviderApi::Single(google_generative_ai_api())),
        ..CreateProviderOptions::default()
    })
}
