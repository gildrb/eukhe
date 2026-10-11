//! The `xiaomi-token-plan-sgp` provider. Port of `providers/xiaomi-token-plan-sgp.ts`.

use super::chat_models;
use super::xiaomi_token_plan_sgp_models::XIAOMI_TOKEN_PLAN_SGP_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `xiaomiTokenPlanSgpProvider()`.
#[must_use]
pub fn xiaomi_token_plan_sgp_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "xiaomi-token-plan-sgp".to_owned(),
        name: Some("Xiaomi Token Plan SGP".to_owned()),
        base_url: Some("https://token-plan-sgp.xiaomimimo.com/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "Xiaomi Token Plan SGP API key",
                &["XIAOMI_TOKEN_PLAN_SGP_API_KEY"],
            )),
            oauth: None,
        },
        models: chat_models(&XIAOMI_TOKEN_PLAN_SGP_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
