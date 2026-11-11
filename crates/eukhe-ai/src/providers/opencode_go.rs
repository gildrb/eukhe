//! The `opencode-go` provider. Port of `providers/opencode-go.ts`.

use eukhe_types::pi_ai::IndexMap;

use super::api_route::routed_streams;
use super::opencode_go_models::OPENCODE_GO_MODELS;
use super::opencode_headers::with_opencode_session_header;
use super::{builtin_baseline, chat_models};
use crate::api::builtin::{anthropic_messages_api, openai_completions_api, openai_responses_api};
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};
use crate::types::{Model, ModelCompat, OpenAIResponsesCompat};

/// omp's `api-routes provider="opencode-go"` (`route "openai-responses"
/// exact="deepseek-v4-flash"`, `catalog/src/compat/rules/runtime/behavior.kdl:294-304`,
/// gateway-verified 2026-08-08): `DeepSeek` V4 Flash rides the gateway's
/// Responses endpoint, whatever API its catalog entry names.
fn responses_route(model: &Model) -> Option<Model> {
    if model.id != "deepseek-v4-flash" {
        return None;
    }
    let mut routed = model.clone();
    "openai-responses".clone_into(&mut routed.api);
    routed.compat = Some(ModelCompat::OpenAIResponses(OpenAIResponsesCompat {
        supports_developer_role: Some(false),
        ..OpenAIResponsesCompat::default()
    }));
    Some(routed)
}

/// TS `opencodeGoProvider()`.
#[must_use]
pub fn opencode_go_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "opencode-go".to_owned(),
        name: Some("OpenCode Go".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("OpenCode API key", &["OPENCODE_API_KEY"])),
            oauth: None,
        },
        models: builtin_baseline("opencode-go", || chat_models(&OPENCODE_GO_MODELS)),
        api: Some(ProviderApi::ByApi(IndexMap::from([
            (
                "anthropic-messages".to_owned(),
                with_opencode_session_header(anthropic_messages_api()),
            ),
            (
                "openai-completions".to_owned(),
                with_opencode_session_header(routed_streams(
                    openai_completions_api(),
                    openai_responses_api(),
                    responses_route,
                )),
            ),
            (
                "openai-responses".to_owned(),
                with_opencode_session_header(openai_responses_api()),
            ),
        ]))),
        ..CreateProviderOptions::default()
    })
}
