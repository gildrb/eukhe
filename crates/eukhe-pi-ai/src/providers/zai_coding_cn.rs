//! The `zai-coding-cn` provider. Port of `providers/zai-coding-cn.ts`.

use super::chat_models;
use super::zai_coding_cn_models::ZAI_CODING_CN_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `zaiCodingCnProvider()`.
#[must_use]
pub fn zai_coding_cn_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "zai-coding-cn".to_owned(),
        name: Some("Z.AI Coding CN".to_owned()),
        base_url: Some("https://open.bigmodel.cn/api/coding/paas/v4".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "Z.AI Coding CN API key",
                &["ZAI_CODING_CN_API_KEY"],
            )),
            oauth: None,
        },
        models: chat_models(&ZAI_CODING_CN_MODELS),
        api: Some(ProviderApi::Single(openai_completions_api())),
        ..CreateProviderOptions::default()
    })
}
