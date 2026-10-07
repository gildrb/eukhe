//! The `github-copilot` provider. Port of `providers/github-copilot.ts`.

use std::sync::Arc;

use eukhe_types::pi_ai::{IndexMap, JsonValue, Model};

use super::chat_models;
use super::github_copilot_models::GITHUB_COPILOT_MODELS;
use crate::api::builtin::{anthropic_messages_api, openai_completions_api, openai_responses_api};
use crate::auth::oauth::load_github_copilot_oauth;
use crate::auth::{env_api_key_auth, lazy_oauth, Credential, LazyOAuthInput, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};

/// OAuth credentials carry `availableModelIds`; models outside the list are
/// unavailable. Any other credential, or a malformed list, keeps every model.
fn filter_models(models: Vec<Model>, credential: Option<&Credential>) -> Vec<Model> {
    let Some(Credential::OAuth(credential)) = credential else {
        return models;
    };
    let Some(JsonValue::Array(available_model_ids)) = credential.extra.get("availableModelIds")
    else {
        return models;
    };
    let Some(available) = available_model_ids
        .iter()
        .map(JsonValue::as_str)
        .collect::<Option<Vec<&str>>>()
    else {
        return models;
    };
    models
        .into_iter()
        .filter(|model| available.contains(&model.id.as_str()))
        .collect()
}

/// TS `githubCopilotProvider()`.
#[must_use]
pub fn github_copilot_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "github-copilot".to_owned(),
        name: Some("GitHub Copilot".to_owned()),
        base_url: Some("https://api.individual.githubcopilot.com".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "GitHub Copilot token",
                &["COPILOT_GITHUB_TOKEN"],
            )),
            oauth: Some(lazy_oauth(LazyOAuthInput {
                name: "GitHub Copilot".to_owned(),
                is_subscription: Some(true),
                login_label: None,
                load: Arc::new(load_github_copilot_oauth),
            })),
        },
        models: chat_models(&GITHUB_COPILOT_MODELS),
        filter_models: Some(Arc::new(filter_models)),
        api: Some(ProviderApi::ByApi(IndexMap::from([
            ("anthropic-messages".to_owned(), anthropic_messages_api()),
            ("openai-completions".to_owned(), openai_completions_api()),
            ("openai-responses".to_owned(), openai_responses_api()),
        ]))),
        ..CreateProviderOptions::default()
    })
}
