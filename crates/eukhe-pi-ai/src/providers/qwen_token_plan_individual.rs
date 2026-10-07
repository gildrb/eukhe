//! The `qwen-token-plan-individual` provider. Port of `providers/qwen-token-plan-individual.ts`.

use super::chat_models;
use super::qwen_token_plan_individual_models::QWEN_TOKEN_PLAN_INDIVIDUAL_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `qwenTokenPlanIndividualProvider()`.
#[must_use]
pub fn qwen_token_plan_individual_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "qwen-token-plan-individual".to_owned(),
        name: Some("Qwen Token Plan Individual".to_owned()),
        base_url: Some(
            "https://token-plan.ap-southeast-1.maas.aliyuncs.com/compatible-mode/v1".to_owned(),
        ),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "Qwen Token Plan Individual API key",
                &["QWEN_TOKEN_PLAN_API_KEY"],
            )),
            oauth: None,
        },
        models: chat_models(&QWEN_TOKEN_PLAN_INDIVIDUAL_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
