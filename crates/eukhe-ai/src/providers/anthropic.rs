//! The `anthropic` provider. Port of `providers/anthropic.ts`.

use std::sync::Arc;

use eukhe_types::pi_ai::ProviderHeaders;
use futures::future::BoxFuture;

use super::anthropic_models::ANTHROPIC_MODELS;
use super::chat_models;
use crate::api::builtin::anthropic_messages_api;
use crate::auth::oauth::load_anthropic_oauth;
use crate::auth::{
    lazy_oauth, ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, AuthPrompt, AuthPromptKind,
    AuthResult, LazyOAuthInput, ModelAuth, ProviderAuth, ProviderAuthInteraction,
};
use crate::env_api_keys::{
    ANTHROPIC_API_KEY_ENV, ANTHROPIC_AUTH_TOKEN_ENV, ANTHROPIC_FEDERATION_RULE_ID_ENV,
    ANTHROPIC_IDENTITY_TOKEN_FILE_ENV, ANTHROPIC_OAUTH_TOKEN_ENV, ANTHROPIC_ORGANIZATION_ID_ENV,
    ANTHROPIC_SERVICE_ACCOUNT_ID_ENV, ANTHROPIC_WORKSPACE_ID_ENV,
};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};
use crate::types::ProviderEnv;
use crate::utils::diagnostics::Thrown;

struct AnthropicApiKeyAuth;

impl ApiKeyAuth for AnthropicApiKeyAuth {
    // The trait returns a borrowed name; this one is a literal.
    #[allow(clippy::unnecessary_literal_bound)]
    fn name(&self) -> &str {
        "Anthropic API key"
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
    ) -> Option<BoxFuture<'_, Result<ApiKeyCredential, Thrown>>> {
        Some(Box::pin(async move {
            interaction.signal.throw_if_aborted()?;
            let key = interaction
                .prompt(AuthPrompt::new(AuthPromptKind::Secret {
                    message: "Enter Anthropic API key".to_owned(),
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
            if let Some(credential) = &credential {
                if let Some(key) = credential.key.as_ref().filter(|key| !key.is_empty()) {
                    return Ok(Some(AuthResult {
                        auth: ModelAuth {
                            api_key: Some(key.clone()),
                            ..ModelAuth::default()
                        },
                        env: credential.env.clone(),
                        source: Some("stored credential".to_owned()),
                    }));
                }
            }

            let auth_token = ctx.env(ANTHROPIC_AUTH_TOKEN_ENV).await;
            signal.throw_if_aborted()?;
            if let Some(auth_token) = auth_token.filter(|token| !token.is_empty()) {
                let headers: ProviderHeaders = [(
                    "Authorization".to_owned(),
                    Some(format!("Bearer {auth_token}")),
                )]
                .into_iter()
                .collect();
                return Ok(Some(AuthResult {
                    auth: ModelAuth {
                        headers: Some(headers),
                        ..ModelAuth::default()
                    },
                    env: None,
                    source: Some(ANTHROPIC_AUTH_TOKEN_ENV.to_owned()),
                }));
            }

            for env_var in [ANTHROPIC_OAUTH_TOKEN_ENV, ANTHROPIC_API_KEY_ENV] {
                let api_key = ctx.env(env_var).await;
                signal.throw_if_aborted()?;
                if let Some(api_key) = api_key.filter(|key| !key.is_empty()) {
                    return Ok(Some(AuthResult {
                        auth: ModelAuth {
                            api_key: Some(api_key),
                            ..ModelAuth::default()
                        },
                        env: None,
                        source: Some(env_var.to_owned()),
                    }));
                }
            }

            // Workload identity federation: the Anthropic SDK exchanges the
            // identity token for a short-lived access token and refreshes it
            // itself. Last in line so keys and ANTHROPIC_AUTH_TOKEN keep
            // winning, as in the SDK. The ids are provider config rather than
            // auth, so they travel in `env`.
            let mut federation = ProviderEnv::new();
            for env_var in [
                ANTHROPIC_FEDERATION_RULE_ID_ENV,
                ANTHROPIC_ORGANIZATION_ID_ENV,
                ANTHROPIC_IDENTITY_TOKEN_FILE_ENV,
            ] {
                let value = ctx.env(env_var).await;
                signal.throw_if_aborted()?;
                let Some(value) = value.filter(|value| !value.is_empty()) else {
                    return Ok(None);
                };
                federation.insert(env_var.to_owned(), value);
            }
            for env_var in [ANTHROPIC_SERVICE_ACCOUNT_ID_ENV, ANTHROPIC_WORKSPACE_ID_ENV] {
                let value = ctx.env(env_var).await;
                signal.throw_if_aborted()?;
                if let Some(value) = value.filter(|value| !value.is_empty()) {
                    federation.insert(env_var.to_owned(), value);
                }
            }
            Ok(Some(AuthResult {
                auth: ModelAuth::default(),
                env: Some(federation),
                source: Some("workload identity federation".to_owned()),
            }))
        })
    }
}

/// TS `anthropicProvider()`.
#[must_use]
pub fn anthropic_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "anthropic".to_owned(),
        name: Some("Anthropic".to_owned()),
        base_url: Some("https://api.anthropic.com".to_owned()),
        auth: ProviderAuth {
            api_key: Some(Arc::new(AnthropicApiKeyAuth)),
            oauth: Some(lazy_oauth(LazyOAuthInput {
                name: "Anthropic (Claude Pro/Max)".to_owned(),
                is_subscription: Some(true),
                login_label: None,
                load: Arc::new(load_anthropic_oauth),
            })),
        },
        models: chat_models(&ANTHROPIC_MODELS),
        api: Some(ProviderApi::Single(anthropic_messages_api())),
        ..CreateProviderOptions::default()
    })
}
