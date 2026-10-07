//! The `amazon-bedrock` provider. Port of `providers/amazon-bedrock.ts`.

use std::sync::Arc;

use futures::future::BoxFuture;

use super::amazon_bedrock_models::AMAZON_BEDROCK_MODELS;
use super::chat_models;
use crate::api::builtin::bedrock_converse_stream_api;
use crate::auth::{
    ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, AuthEvent, AuthInfoLink, AuthPrompt,
    AuthPromptKind, AuthResult, AuthSelectOption, ModelAuth, ProviderAuth, ProviderAuthInteraction,
};
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};
use crate::types::ProviderEnv;
use crate::utils::diagnostics::{ErrorObject, Thrown};

/// Bedrock accepts a bearer token or the AWS SDK's default credential chain.
/// The login flow can store a token/profile choice; resolve also detects
/// ambient AWS credentials without copying them into pi's credential store.
struct BedrockAuth;

fn text_prompt(message: &str) -> AuthPrompt {
    AuthPrompt::new(AuthPromptKind::Text {
        message: message.to_owned(),
        placeholder: None,
    })
}

fn result(source: &str, env: Option<ProviderEnv>) -> AuthResult {
    AuthResult {
        auth: ModelAuth::default(),
        env,
        source: Some(source.to_owned()),
    }
}

impl ApiKeyAuth for BedrockAuth {
    // The trait returns a borrowed name; this one is a literal.
    #[allow(clippy::unnecessary_literal_bound)]
    fn name(&self) -> &str {
        "AWS credentials or bearer token"
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
    ) -> Option<BoxFuture<'_, Result<ApiKeyCredential, Thrown>>> {
        Some(Box::pin(async move {
            interaction.signal.throw_if_aborted()?;
            let method = interaction
                .prompt(AuthPrompt::new(AuthPromptKind::Select {
                    message: "Select Amazon Bedrock authentication method:".to_owned(),
                    options: vec![
                        AuthSelectOption::new("bearer-token", "Bearer token"),
                        AuthSelectOption::new("aws-profile", "AWS profile"),
                        AuthSelectOption::new("credential-chain", "Existing AWS credential chain"),
                    ],
                }))
                .await?;
            interaction.signal.throw_if_aborted()?;
            if method == "bearer-token" {
                let key = interaction
                    .prompt(AuthPrompt::new(AuthPromptKind::Secret {
                        message: "Enter Amazon Bedrock bearer token".to_owned(),
                        placeholder: None,
                    }))
                    .await?;
                return Ok(ApiKeyCredential::with_key(key));
            }
            interaction.notify(AuthEvent::Info {
                message: "Amazon Bedrock supports AWS profiles, IAM credentials, and role-based credentials."
                    .to_owned(),
                links: Some(vec![AuthInfoLink {
                    url: "https://docs.aws.amazon.com/sdkref/latest/guide/standardized-credentials.html"
                        .to_owned(),
                    label: Some("AWS credential provider chain".to_owned()),
                }]),
            });
            if method == "aws-profile" {
                let profile = interaction
                    .prompt(text_prompt("Enter AWS profile name"))
                    .await?;
                return Ok(ApiKeyCredential {
                    env: Some(ProviderEnv::from([("AWS_PROFILE".to_owned(), profile)])),
                    ..ApiKeyCredential::default()
                });
            }
            if method != "credential-chain" {
                return Err(ErrorObject::new(format!(
                    "Unknown Amazon Bedrock auth method: {method}"
                ))
                .thrown());
            }
            interaction
                .prompt(text_prompt(
                    "Configure AWS credentials, then press Enter to continue",
                ))
                .await?;
            Ok(ApiKeyCredential::default())
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
            let env = |name: &'static str| {
                let ctx = Arc::clone(&ctx);
                let signal = signal.clone();
                async move {
                    signal.throw_if_aborted()?;
                    let value = ctx.env(name).await.filter(|value| !value.is_empty());
                    signal.throw_if_aborted()?;
                    Ok::<_, Thrown>(value)
                }
            };
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
            if env("AWS_BEARER_TOKEN_BEDROCK").await?.is_some() {
                return Ok(Some(result("AWS_BEARER_TOKEN_BEDROCK", None)));
            }
            let stored_profile = credential
                .as_ref()
                .and_then(|credential| credential.env.as_ref())
                .and_then(|env| env.get("AWS_PROFILE"))
                .cloned();
            // TS `??`: an empty stored profile still wins over the env lookup.
            let profile = match &stored_profile {
                Some(profile) => Some(profile.clone()),
                None => env("AWS_PROFILE").await?,
            };
            if profile.is_some_and(|profile| !profile.is_empty()) {
                let stored_env = credential
                    .as_ref()
                    .and_then(|credential| credential.env.clone());
                let source = if stored_profile.is_some_and(|profile| !profile.is_empty()) {
                    "stored credential"
                } else {
                    "AWS_PROFILE"
                };
                return Ok(Some(result(source, stored_env)));
            }
            if env("AWS_ACCESS_KEY_ID").await?.is_some()
                && env("AWS_SECRET_ACCESS_KEY").await?.is_some()
            {
                return Ok(Some(result("AWS access keys", None)));
            }
            if env("AWS_CONTAINER_CREDENTIALS_RELATIVE_URI")
                .await?
                .is_some()
            {
                return Ok(Some(result("ECS task role", None)));
            }
            if env("AWS_CONTAINER_CREDENTIALS_FULL_URI").await?.is_some() {
                return Ok(Some(result("ECS task role", None)));
            }
            if env("AWS_WEB_IDENTITY_TOKEN_FILE").await?.is_some() {
                return Ok(Some(result("web identity token", None)));
            }
            Ok(None)
        })
    }
}

/// TS `amazonBedrockProvider()`.
#[must_use]
pub fn amazon_bedrock_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "amazon-bedrock".to_owned(),
        name: Some("Amazon Bedrock".to_owned()),
        auth: ProviderAuth {
            api_key: Some(Arc::new(BedrockAuth)),
            oauth: None,
        },
        models: chat_models(&AMAZON_BEDROCK_MODELS),
        api: Some(ProviderApi::Single(bedrock_converse_stream_api())),
        ..CreateProviderOptions::default()
    })
}
