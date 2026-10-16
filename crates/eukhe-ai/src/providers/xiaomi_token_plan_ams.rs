//! The `xiaomi-token-plan-ams` provider. Port of `providers/xiaomi-token-plan-ams.ts`.

use super::xiaomi_token_plan_ams_models::XIAOMI_TOKEN_PLAN_AMS_MODELS;
use super::{builtin_baseline, chat_models};
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `xiaomiTokenPlanAmsProvider()`.
#[must_use]
pub fn xiaomi_token_plan_ams_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "xiaomi-token-plan-ams".to_owned(),
        name: Some("Xiaomi Token Plan AMS".to_owned()),
        base_url: Some("https://token-plan-ams.xiaomimimo.com/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "Xiaomi Token Plan AMS API key",
                &["XIAOMI_TOKEN_PLAN_AMS_API_KEY"],
            )),
            oauth: None,
        },
        models: builtin_baseline("xiaomi-token-plan-ams", || {
            chat_models(&XIAOMI_TOKEN_PLAN_AMS_MODELS)
        }),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
