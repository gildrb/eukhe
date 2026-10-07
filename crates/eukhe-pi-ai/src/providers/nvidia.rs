//! The `nvidia` provider. Port of `providers/nvidia.ts`.

use super::chat_models;
use super::nvidia_models::NVIDIA_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `nvidiaProvider()`.
#[must_use]
pub fn nvidia_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "nvidia".to_owned(),
        name: Some("NVIDIA".to_owned()),
        base_url: Some("https://integrate.api.nvidia.com/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("NVIDIA API key", &["NVIDIA_API_KEY"])),
            oauth: None,
        },
        models: chat_models(&NVIDIA_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
