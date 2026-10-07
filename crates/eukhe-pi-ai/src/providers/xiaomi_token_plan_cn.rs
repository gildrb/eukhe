//! The `xiaomi-token-plan-cn` provider. Port of `providers/xiaomi-token-plan-cn.ts`.

use super::chat_models;
use super::xiaomi_token_plan_cn_models::XIAOMI_TOKEN_PLAN_CN_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `xiaomiTokenPlanCnProvider()`.
#[must_use]
pub fn xiaomi_token_plan_cn_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "xiaomi-token-plan-cn".to_owned(),
        name: Some("Xiaomi Token Plan CN".to_owned()),
        base_url: Some("https://token-plan-cn.xiaomimimo.com/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "Xiaomi Token Plan CN API key",
                &["XIAOMI_TOKEN_PLAN_CN_API_KEY"],
            )),
            oauth: None,
        },
        models: chat_models(&XIAOMI_TOKEN_PLAN_CN_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
