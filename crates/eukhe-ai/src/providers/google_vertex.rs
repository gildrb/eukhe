//! The `google-vertex` provider. Port of `providers/google-vertex.ts`.

use std::sync::Arc;

use futures::future::BoxFuture;

use super::google_vertex_models::GOOGLE_VERTEX_MODELS;
use super::{builtin_baseline, chat_models};
use crate::api::builtin::google_vertex_api;
use crate::auth::{
    ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, AuthEvent, AuthInfoLink, AuthPrompt,
    AuthPromptKind, AuthResult, AuthSelectOption, ModelAuth, ProviderAuth, ProviderAuthInteraction,
};
use crate::env_api_keys::GOOGLE_APPLICATION_CREDENTIALS_ENV;
use crate::models::{build_provider, CreateProviderOptions, Provider, ProviderApi};
use crate::types::ProviderEnv;
use crate::utils::diagnostics::{ErrorObject, Thrown};

const VERTEX_ADC_PATH: &str = "~/.config/gcloud/application_default_credentials.json";

/// Vertex accepts an explicit API key or Application Default Credentials
/// (`gcloud auth application-default login`). ADC additionally requires
/// project and location env vars, which the implementation reads itself.
struct VertexAuth;

/// A login method of the select prompt.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AuthMethod {
    ApiKey,
    Adc,
    ServiceAccount,
}

impl AuthMethod {
    const ALL: [Self; 3] = [Self::ApiKey, Self::Adc, Self::ServiceAccount];

    const fn as_str(self) -> &'static str {
        match self {
            Self::ApiKey => "api-key",
            Self::Adc => "adc",
            Self::ServiceAccount => "service-account",
        }
    }

    const fn label(self) -> &'static str {
        match self {
            Self::ApiKey => "Google Cloud API key",
            Self::Adc => "Application Default Credentials",
            Self::ServiceAccount => "Service account credentials file",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|method| method.as_str() == value)
    }
}

fn text_prompt(message: &str) -> AuthPrompt {
    AuthPrompt::new(AuthPromptKind::Text {
        message: message.to_owned(),
        placeholder: None,
    })
}

impl ApiKeyAuth for VertexAuth {
    // The trait returns a borrowed name; this one is a literal.
    #[allow(clippy::unnecessary_literal_bound)]
    fn name(&self) -> &str {
        "Google Cloud credentials"
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
    ) -> Option<BoxFuture<'_, Result<ApiKeyCredential, Thrown>>> {
        Some(Box::pin(async move {
            interaction.signal.throw_if_aborted()?;
            let method = interaction
                .prompt(AuthPrompt::new(AuthPromptKind::Select {
                    message: "Select Google Vertex AI authentication method:".to_owned(),
                    options: AuthMethod::ALL
                        .into_iter()
                        .map(|method| AuthSelectOption::new(method.as_str(), method.label()))
                        .collect(),
                }))
                .await?;
            interaction.signal.throw_if_aborted()?;
            let Some(method) = AuthMethod::parse(&method) else {
                return Err(ErrorObject::new(format!(
                    "Unknown Google Vertex AI auth method: {method}"
                ))
                .thrown());
            };
            if method == AuthMethod::ApiKey {
                let key = interaction
                    .prompt(AuthPrompt::new(AuthPromptKind::Secret {
                        message: "Enter Google Cloud API key".to_owned(),
                        placeholder: None,
                    }))
                    .await?;
                return Ok(ApiKeyCredential::with_key(key));
            }
            interaction.notify(AuthEvent::Info {
                message: if method == AuthMethod::Adc {
                    "Run `gcloud auth application-default login`, then provide the project and location."
                } else {
                    "Provide a service account credentials file, project, and location."
                }
                .to_owned(),
                links: Some(vec![AuthInfoLink {
                    url: "https://cloud.google.com/docs/authentication/provide-credentials-adc"
                        .to_owned(),
                    label: Some("Application Default Credentials".to_owned()),
                }]),
            });
            let project = interaction
                .prompt(text_prompt("Enter Google Cloud project ID"))
                .await?;
            let location = interaction
                .prompt(text_prompt("Enter Google Cloud location"))
                .await?;
            let credentials_path = if method == AuthMethod::ServiceAccount {
                Some(
                    interaction
                        .prompt(text_prompt("Enter service account credentials file path"))
                        .await?,
                )
            } else {
                None
            };
            let mut env = ProviderEnv::from([
                ("GOOGLE_CLOUD_PROJECT".to_owned(), project),
                ("GOOGLE_CLOUD_LOCATION".to_owned(), location),
            ]);
            if let Some(path) = credentials_path.filter(|path| !path.is_empty()) {
                env.insert(GOOGLE_APPLICATION_CREDENTIALS_ENV.to_owned(), path);
            }
            Ok(ApiKeyCredential {
                env: Some(env),
                ..ApiKeyCredential::default()
            })
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
                    let value = ctx.env(name).await;
                    signal.throw_if_aborted()?;
                    Ok::<_, Thrown>(value)
                }
            };
            let stored_env = |name: &str| {
                credential
                    .as_ref()
                    .and_then(|credential| credential.env.as_ref())
                    .and_then(|env| env.get(name))
                    .cloned()
            };
            let stored_key = credential
                .as_ref()
                .and_then(|credential| credential.key.clone());
            // TS `credential?.key ?? env(...)`, then a truthiness check.
            let key = match &stored_key {
                Some(key) => Some(key.clone()),
                None => env("GOOGLE_CLOUD_API_KEY").await?,
            };
            if let Some(key) = key.filter(|key| !key.is_empty()) {
                return Ok(Some(AuthResult {
                    auth: ModelAuth {
                        api_key: Some(key),
                        ..ModelAuth::default()
                    },
                    env: None,
                    source: Some(
                        if stored_key.is_some_and(|key| !key.is_empty()) {
                            "stored credential"
                        } else {
                            "GOOGLE_CLOUD_API_KEY"
                        }
                        .to_owned(),
                    ),
                }));
            }

            let adc_path = match stored_env(GOOGLE_APPLICATION_CREDENTIALS_ENV) {
                Some(path) => Some(path),
                None => env(GOOGLE_APPLICATION_CREDENTIALS_ENV).await?,
            };
            signal.throw_if_aborted()?;
            let has_credentials = ctx
                .file_exists(adc_path.as_deref().unwrap_or(VERTEX_ADC_PATH))
                .await;
            signal.throw_if_aborted()?;
            let project = match stored_env("GOOGLE_CLOUD_PROJECT") {
                Some(project) => Some(project),
                None => match env("GOOGLE_CLOUD_PROJECT").await? {
                    Some(project) => Some(project),
                    None => env("GCLOUD_PROJECT").await?,
                },
            };
            let location = match stored_env("GOOGLE_CLOUD_LOCATION") {
                Some(location) => Some(location),
                None => env("GOOGLE_CLOUD_LOCATION").await?,
            };
            let truthy = |value: Option<String>| value.is_some_and(|value| !value.is_empty());
            if has_credentials && truthy(project) && truthy(location) {
                return Ok(Some(AuthResult {
                    auth: ModelAuth::default(),
                    env: credential
                        .as_ref()
                        .and_then(|credential| credential.env.clone()),
                    source: Some(
                        if credential.is_some() {
                            "stored credential"
                        } else {
                            "gcloud application default credentials"
                        }
                        .to_owned(),
                    ),
                }));
            }
            Ok(None)
        })
    }
}

/// TS `googleVertexProvider()`.
#[must_use]
pub fn google_vertex_provider() -> Provider {
    build_provider(CreateProviderOptions {
        id: "google-vertex".to_owned(),
        name: Some("Google Vertex AI".to_owned()),
        auth: ProviderAuth {
            api_key: Some(Arc::new(VertexAuth)),
            oauth: None,
        },
        models: builtin_baseline("google-vertex", || chat_models(&GOOGLE_VERTEX_MODELS)),
        api: Some(ProviderApi::Single(google_vertex_api())),
        ..CreateProviderOptions::default()
    })
}
