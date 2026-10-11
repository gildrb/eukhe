//! The `opencode-go` provider. Port of `providers/opencode-go.ts`.

use eukhe_types::pi_ai::IndexMap;

use super::chat_models;
use super::opencode_go_models::OPENCODE_GO_MODELS;
use super::opencode_headers::with_opencode_session_header;
use crate::api::builtin::{anthropic_messages_api, openai_completions_api, openai_responses_api};
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

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
        models: chat_models(&OPENCODE_GO_MODELS),
        api: Some(ProviderApi::ByApi(IndexMap::from([
            (
                "anthropic-messages".to_owned(),
                with_opencode_session_header(anthropic_messages_api()),
            ),
            (
                "openai-completions".to_owned(),
                with_opencode_session_header(openai_completions_api()),
            ),
            (
                "openai-responses".to_owned(),
                with_opencode_session_header(openai_responses_api()),
            ),
        ]))),
        ..CreateProviderOptions::default()
    })
}
