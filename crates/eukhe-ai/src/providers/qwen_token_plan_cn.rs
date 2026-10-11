//! The `qwen-token-plan-cn` provider. Port of `providers/qwen-token-plan-cn.ts`.

use super::chat_models;
use super::qwen_token_plan_cn_models::QWEN_TOKEN_PLAN_CN_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `qwenTokenPlanCnProvider()`.
#[must_use]
pub fn qwen_token_plan_cn_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "qwen-token-plan-cn".to_owned(),
        name: Some("Qwen Token Plan CN".to_owned()),
        base_url: Some(
            "https://token-plan.cn-beijing.maas.aliyuncs.com/compatible-mode/v1".to_owned(),
        ),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "Qwen Token Plan CN API key",
                &["QWEN_TOKEN_PLAN_CN_API_KEY"],
            )),
            oauth: None,
        },
        models: chat_models(&QWEN_TOKEN_PLAN_CN_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
