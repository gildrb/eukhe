//! The `openrouter` provider. Port of `providers/openrouter.ts`.

use std::sync::Arc;

use eukhe_types::pi_ai::IndexMap;

use super::api_route::moved_streams;
use super::openrouter_models::{
    OPENROUTER_CLASSIFIER_MODELS, OPENROUTER_IMAGE_MODELS, OPENROUTER_MODELS,
};
use super::{builtin_baseline, chat_models, classifier_models, image_models};
use crate::api::builtin::{openai_responses_api, openrouter_images_api, typesafe_system_one_api};
use crate::api::openai_completions::compat::get_compat;
use crate::auth::oauth::load_openrouter_oauth;
use crate::auth::{env_api_key_auth, lazy_oauth, LazyOAuthInput, ProviderAuth};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};
use crate::types::{Model, ModelCompat, OpenAIResponsesCompat};

/// omp streams every `OpenRouter` chat model over `OpenRouter`'s Responses API
/// (`ai/src/stream.ts:925`, `api === "openrouter"` → `streamOpenAIResponses`
/// unless `PI_OPENROUTER_RESPONSES=0`), the Anthropic models included. The
/// catalog names chat completions, or Anthropic Messages at `/api` for the
/// `anthropic/` models; every request goes out as a Responses request at
/// `/api/v1`, with the settings the catalog and the rulebook give the model
/// (developer role, strict tools, mid-conversation system messages, session
/// affinity, long cache retention).
fn openrouter_responses(model: &Model) -> Model {
    let compat = get_compat(model);
    let mut routed = model.clone();
    "openai-responses".clone_into(&mut routed.api);
    let base_url = routed.base_url.trim_end_matches('/');
    if base_url.ends_with("/api") {
        routed.base_url = format!("{base_url}/v1");
    }
    routed.compat = Some(ModelCompat::OpenAIResponses(OpenAIResponsesCompat {
        supports_developer_role: Some(compat.supports_developer_role),
        supports_mid_convo_system_messages: compat.supports_mid_convo_system_messages,
        session_affinity_format: Some(compat.session_affinity_format),
        supports_long_cache_retention: Some(compat.supports_long_cache_retention),
        supports_strict_mode: Some(compat.supports_strict_mode),
        ..OpenAIResponsesCompat::default()
    }));
    routed
}

/// TS `openrouterProvider()`.
#[must_use]
pub fn openrouter_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "openrouter".to_owned(),
        name: Some("OpenRouter".to_owned()),
        base_url: Some("https://openrouter.ai/api/v1".to_owned()),
        auth: ProviderAuth {
            api_key: Some(env_api_key_auth(
                "OpenRouter API key",
                &["OPENROUTER_API_KEY"],
            )),
            oauth: Some(lazy_oauth(LazyOAuthInput {
                name: "OpenRouter OAuth".to_owned(),
                is_subscription: None,
                login_label: Some("Sign in with OpenRouter".to_owned()),
                load: Arc::new(load_openrouter_oauth),
            })),
        },
        models: builtin_baseline("openrouter", || {
            let mut models = chat_models(&OPENROUTER_MODELS);
            models.extend(image_models(&OPENROUTER_IMAGE_MODELS));
            models.extend(classifier_models(&OPENROUTER_CLASSIFIER_MODELS));
            models
        }),
        api: Some(ProviderApi::ByApi(IndexMap::from([
            (
                "anthropic-messages".to_owned(),
                moved_streams(openai_responses_api(), openrouter_responses),
            ),
            (
                "openai-completions".to_owned(),
                moved_streams(openai_responses_api(), openrouter_responses),
            ),
        ]))),
        images: Some(IndexMap::from([(
            "openrouter-images".to_owned(),
            openrouter_images_api(),
        )])),
        // OpenRouter serves TypeSafe's System One protocol at /api/v1/systemone.
        classifiers: Some(IndexMap::from([(
            "typesafe-system-one".to_owned(),
            typesafe_system_one_api(),
        )])),
        ..CreateProviderOptions::default()
    })
}
