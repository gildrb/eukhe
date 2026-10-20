//! The `prime-inference` provider (eukhe addition; ported from
//! `crates/eukhe-ai` and `crates/eukhe-models`).
//!
//! An `openai-completions` provider with a static catalog: the compiled
//! entries of `prime_inference_models`. The provider does not fetch a model
//! list.

use std::sync::Arc;

use eukhe_types::pi_ai::{AnyModel, ProviderHeaders};
use futures::future::BoxFuture;

use super::prime_inference_models::PRIME_INFERENCE_MODELS;
use crate::api::builtin::openai_completions_api;
use crate::auth::{
    ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, AuthPrompt, AuthPromptKind, AuthResult,
    ModelAuth, ProviderAuth, ProviderAuthInteraction,
};
use crate::models::Provider;
use crate::types::ProviderEnv;
use crate::utils::diagnostics::Thrown;

/// The provider id.
pub const PRIME_INFERENCE_PROVIDER_ID: &str = "prime-inference";

/// The Prime Inference API base URL.
pub const PRIME_INFERENCE_BASE_URL: &str = "https://api.pinference.ai/api/v1";

/// API key environment variable.
pub const PRIME_API_KEY_ENV: &str = "PRIME_API_KEY";

/// Team environment variable / credential env key; sent as `X-Prime-Team-ID`.
pub const PRIME_TEAM_ID_ENV: &str = "PRIME_TEAM_ID";

/// Api-key auth: stored key or `PRIME_API_KEY`; the team (stored
/// `PRIME_TEAM_ID` env or the ambient variable) becomes the
/// `X-Prime-Team-ID` header and travels in the resolved env.
struct PrimeInferenceAuth;

impl ApiKeyAuth for PrimeInferenceAuth {
    // The trait returns a borrowed name; this one is a literal.
    #[allow(clippy::unnecessary_literal_bound)]
    fn name(&self) -> &str {
        "Prime Inference API key"
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
    ) -> Option<BoxFuture<'_, Result<ApiKeyCredential, Thrown>>> {
        Some(Box::pin(async move {
            interaction.signal.throw_if_aborted()?;
            let key = interaction
                .prompt(AuthPrompt::new(AuthPromptKind::Secret {
                    message: "Enter Prime Inference API key".to_owned(),
                    placeholder: None,
                }))
                .await?;
            interaction.signal.throw_if_aborted()?;
            Ok(ApiKeyCredential::with_key(key))
        }))
    }

    fn resolve(
        &self,
        input: ApiKeyResolveInput,
    ) -> BoxFuture<'_, Result<Option<AuthResult>, Thrown>> {
        Box::pin(async move {
            let ApiKeyResolveInput {
                ctx,
                credential,
                signal,
            } = input;
            signal.throw_if_aborted()?;
            let stored_key = credential
                .as_ref()
                .and_then(|credential| credential.key.clone())
                .filter(|key| !key.is_empty());
            let (key, source) = if let Some(key) = stored_key {
                (key, "stored credential")
            } else {
                let ambient = ctx
                    .env(PRIME_API_KEY_ENV)
                    .await
                    .filter(|key| !key.is_empty());
                signal.throw_if_aborted()?;
                let Some(key) = ambient else { return Ok(None) };
                (key, PRIME_API_KEY_ENV)
            };
            let mut env: Option<ProviderEnv> = credential
                .as_ref()
                .and_then(|credential| credential.env.clone());
            let stored_team = env
                .as_ref()
                .and_then(|env| env.get(PRIME_TEAM_ID_ENV))
                .filter(|team| !team.is_empty())
                .cloned();
            let team = if stored_team.is_some() {
                stored_team
            } else {
                let ambient = ctx
                    .env(PRIME_TEAM_ID_ENV)
                    .await
                    .filter(|team| !team.is_empty());
                signal.throw_if_aborted()?;
                ambient
            };
            let headers = team.map(|team| {
                env.get_or_insert_with(ProviderEnv::new)
                    .insert(PRIME_TEAM_ID_ENV.to_owned(), team.clone());
                ProviderHeaders::from([("X-Prime-Team-ID".to_owned(), Some(team))])
            });
            Ok(Some(AuthResult {
                auth: ModelAuth {
                    api_key: Some(key),
                    headers,
                    base_url: None,
                },
                env,
                source: Some(source.to_owned()),
            }))
        })
    }
}

/// The Prime Inference provider (eukhe addition).
#[must_use]
pub fn prime_inference_provider() -> Provider {
    let models: Arc<[AnyModel]> = PRIME_INFERENCE_MODELS
        .values()
        .cloned()
        .map(AnyModel::Chat)
        .collect();
    let streams = openai_completions_api();
    Provider {
        id: PRIME_INFERENCE_PROVIDER_ID.to_owned(),
        name: "Prime Inference".to_owned(),
        base_url: Some(PRIME_INFERENCE_BASE_URL.to_owned()),
        headers: None,
        auth: ProviderAuth {
            api_key: Some(Arc::new(PrimeInferenceAuth)),
            oauth: None,
        },
        get_models: Arc::new(move || Ok(Arc::clone(&models))),
        refresh_models: None,
        filter_models: None,
        filter_all_models: None,
        stream: streams.stream,
        stream_simple: streams.stream_simple,
        fetch_deferred: None,
        cancel_deferred: None,
        generate_images: None,
        classify: None,
    }
}
