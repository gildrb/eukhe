//! The `cloudflare-ai-gateway` provider. Port of
//! `providers/cloudflare-ai-gateway.ts`.

use eukhe_types::pi_ai::IndexMap;

use super::api_route::moved_streams;
use super::cloudflare_ai_gateway_models::CLOUDFLARE_AI_GATEWAY_MODELS;
use super::cloudflare_auth::cloudflare_ai_gateway_auth;
use super::cloudflare_stream::cloudflare_streams;
use super::{builtin_baseline, chat_models};
use crate::api::builtin::{anthropic_messages_api, openai_completions_api};
use crate::auth::ProviderAuth;
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};
use crate::types::{MaxTokensField, Model, ModelCompat, OpenAICompletionsCompat};

/// The API route of `cloudflare-ai-gateway`: the gateway's `openai/`
/// namespace rides chat completions (the `openai/` prefix stripped) at the
/// `OpenAI` endpoint. The
/// catalog's `OpenAI` models (bare ids at `/openai`) name `openai-responses`;
/// every request of them goes out as an `OpenAI` chat-completions request:
/// `store: false`, `reasoning_effort`, `max_completion_tokens`, the
/// `system` role.
fn openai_chat_completions(model: &Model) -> Model {
    let mut routed = model.clone();
    "openai-completions".clone_into(&mut routed.api);
    routed.compat = Some(ModelCompat::OpenAICompletions(OpenAICompletionsCompat {
        supports_store: Some(true),
        supports_developer_role: Some(false),
        supports_reasoning_effort: Some(true),
        max_tokens_field: Some(MaxTokensField::MaxCompletionTokens),
        ..OpenAICompletionsCompat::default()
    }));
    routed
}

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
        models: builtin_baseline("cloudflare-ai-gateway", || {
            chat_models(&CLOUDFLARE_AI_GATEWAY_MODELS)
        }),
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
                cloudflare_streams(moved_streams(
                    openai_completions_api(),
                    openai_chat_completions,
                )),
            ),
        ]))),
        ..CreateProviderOptions::default()
    })
}
