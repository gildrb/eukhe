//! The `cloudflare-ai-gateway` provider. Port of
//! `providers/cloudflare-ai-gateway.ts`.

use eukhe_types::pi_ai::IndexMap;

use super::chat_models;
use super::cloudflare_ai_gateway_models::CLOUDFLARE_AI_GATEWAY_MODELS;
use super::cloudflare_auth::cloudflare_ai_gateway_auth;
use super::cloudflare_stream::cloudflare_streams;
use crate::api::builtin::{anthropic_messages_api, openai_completions_api, openai_responses_api};
use crate::auth::ProviderAuth;
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `cloudflareAIGatewayProvider()`.
///
/// The api map is pinned to all three APIs: models.dev's gateway catalog
/// drops and restores `workers-ai/*` (openai-completions) entries over time,
/// and inference from `models` alone would otherwise reject the
/// openai-completions entry whenever the generated catalog contains none.
#[must_use]
pub fn cloudflare_ai_gateway_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "cloudflare-ai-gateway".to_owned(),
        name: Some("Cloudflare AI Gateway".to_owned()),
        auth: ProviderAuth {
            api_key: Some(cloudflare_ai_gateway_auth()),
            oauth: None,
        },
        models: chat_models(&CLOUDFLARE_AI_GATEWAY_MODELS),
        api: Some(ProviderApi::ByApi(IndexMap::from([
            (
                "anthropic-messages".to_owned(),
                cloudflare_streams(anthropic_messages_api()),
            ),
            (
                "openai-completions".to_owned(),
                cloudflare_streams(openai_completions_api()),
            ),
            (
                "openai-responses".to_owned(),
                cloudflare_streams(openai_responses_api()),
            ),
        ]))),
        ..CreateProviderOptions::default()
    })
}
