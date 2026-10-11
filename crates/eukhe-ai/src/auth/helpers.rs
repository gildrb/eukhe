//! Standard api-key auth and the lazy OAuth wrapper. Port of `auth/helpers.ts`.

use std::sync::Arc;

use futures::future::BoxFuture;
use tokio::sync::OnceCell;

use super::types::{
    ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, AuthPrompt, AuthPromptKind, AuthResult,
    LoginOptions, ModelAuth, OAuthAuth, OAuthCredential, ProviderAuthInteraction,
};
use crate::utils::diagnostics::Thrown;

struct EnvApiKeyAuth {
    name: String,
    env_vars: Vec<String>,
}

impl ApiKeyAuth for EnvApiKeyAuth {
    fn name(&self) -> &str {
        &self.name
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
    ) -> Option<BoxFuture<'_, Result<ApiKeyCredential, Thrown>>> {
        Some(Box::pin(async move {
            interaction.signal.throw_if_aborted()?;
            let key = interaction
                .prompt(AuthPrompt::new(AuthPromptKind::Secret {
                    message: format!("Enter {}", self.name),
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
            input.signal.throw_if_aborted()?;
            if let Some(credential) = &input.credential {
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
            for env_var in &self.env_vars {
                let value = input.ctx.env(env_var).await;
                input.signal.throw_if_aborted()?;
                if let Some(value) = value.filter(|value| !value.is_empty()) {
                    return Ok(Some(AuthResult {
                        auth: ModelAuth {
                            api_key: Some(value),
                            ..ModelAuth::default()
                        },
                        env: None,
                        source: Some(env_var.clone()),
                    }));
                }
            }
            Ok(None)
        })
    }
}

/// Standard api-key auth: a stored credential key wins, otherwise the first
/// set env var resolves. Includes a `login` that prompts for the key.
/// Providers with non-standard resolution write their own [`ApiKeyAuth`].
#[must_use]
pub fn env_api_key_auth(name: &str, env_vars: &[&str]) -> Arc<dyn ApiKeyAuth> {
    Arc::new(EnvApiKeyAuth {
        name: name.to_owned(),
        env_vars: env_vars.iter().map(|&var| var.to_owned()).collect(),
    })
}

/// Loads an [`OAuthAuth`] on first use.
pub type OAuthLoader =
    Arc<dyn Fn() -> BoxFuture<'static, Result<Arc<dyn OAuthAuth>, Thrown>> + Send + Sync>;

/// Input of [`lazy_oauth`].
pub struct LazyOAuthInput {
    pub name: String,
    pub is_subscription: Option<bool>,
    pub login_label: Option<String>,
    pub load: OAuthLoader,
}

struct LazyOAuth {
    name: String,
    is_subscription: Option<bool>,
    login_label: Option<String>,
    load: OAuthLoader,
    loaded: OnceCell<Result<Arc<dyn OAuthAuth>, Thrown>>,
}

impl LazyOAuth {
    /// `promise ??= input.load()`: the first load, failed or not, is cached.
    async fn loaded(&self) -> Result<Arc<dyn OAuthAuth>, Thrown> {
        self.loaded.get_or_init(|| (self.load)()).await.clone()
    }
}

impl OAuthAuth for LazyOAuth {
    fn name(&self) -> &str {
        &self.name
    }

    fn is_subscription(&self) -> Option<bool> {
        self.is_subscription
    }

    fn login_label(&self) -> Option<&str> {
        self.login_label.as_deref()
    }

    fn login(
        &self,
        interaction: ProviderAuthInteraction,
        options: Option<LoginOptions>,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { self.loaded().await?.login(interaction, options).await })
    }

    fn refresh(
        &self,
        credential: OAuthCredential,
        signal: eukhe_chord::context::AbortSignal,
    ) -> BoxFuture<'_, Result<OAuthCredential, Thrown>> {
        Box::pin(async move { self.loaded().await?.refresh(credential, signal).await })
    }

    fn to_auth<'a>(
        &'a self,
        credential: &'a OAuthCredential,
    ) -> BoxFuture<'a, Result<ModelAuth, Thrown>> {
        Box::pin(async move { self.loaded().await?.to_auth(credential).await })
    }
}

/// Wraps a lazily loaded [`OAuthAuth`] so provider definitions can advertise
/// OAuth without constructing the implementation. The flow loads on first
/// `login`/`refresh`/`to_auth` call.
#[must_use]
pub fn lazy_oauth(input: LazyOAuthInput) -> Arc<dyn OAuthAuth> {
    Arc::new(LazyOAuth {
        name: input.name,
        is_subscription: input.is_subscription,
        login_label: input.login_label,
        load: input.load,
        loaded: OnceCell::new(),
    })
}
