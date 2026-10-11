//! The `opencode` provider. Port of `providers/opencode.ts`.

use eukhe_types::pi_ai::IndexMap;

use super::opencode_headers::with_opencode_session_header;
use super::opencode_models::{OPENCODE_CLASSIFIER_MODELS, OPENCODE_MODELS};
use super::{chat_models, classifier_models};
use crate::api::builtin::{
    anthropic_messages_api, google_generative_ai_api, openai_completions_api, openai_responses_api,
    typesafe_system_one_api,
};
use crate::auth::{env_api_key_auth, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// TS `opencodeProvider()`.
#[must_use]
pub fn opencode_provider() -> Provider {
    let mut models = chat_models(&OPENCODE_MODELS);
    models.extend(classifier_models(&OPENCODE_CLASSIFIER_MODELS));
    build_provider(CreateProviderOptions {
        id: "opencode".to_owned(),
        name: Some("OpenCode Zen".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth("OpenCode API key", &["OPENCODE_API_KEY"])),
            oauth: None,
        },
        models,
        api: Some(ProviderApi::ByApi(IndexMap::from([
            (
                "anthropic-messages".to_owned(),
                with_opencode_session_header(anthropic_messages_api()),
            ),
            (
                "google-generative-ai".to_owned(),
                with_opencode_session_header(google_generative_ai_api()),
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
        // OpenCode Zen serves TypeSafe's System One protocol at /zen/v1/systemone.
        classifiers: Some(IndexMap::from([(
            "typesafe-system-one".to_owned(),
            typesafe_system_one_api(),
        )])),
        ..CreateProviderOptions::default()
    })
}
