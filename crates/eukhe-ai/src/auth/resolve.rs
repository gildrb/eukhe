//! Auth resolution shared by all operations in a `Models` collection. Port of
//! `auth/resolve.ts`.

use std::sync::Arc;

use eukhe_chord::context::{AbortController, AbortSignal};
use eukhe_types::pi_ai::ProviderEnv;
use futures::future::BoxFuture;
use tokio_util::sync::CancellationToken;

use super::errors::{date_now, timeout_signal};
use super::types::{
    ApiKeyAuth, ApiKeyCredential, ApiKeyResolveInput, ApiKeyType, AuthContext,
    AuthOperationOptions, AuthResult, Credential, CredentialStore, ModifyFn, OAuthAuth,
    OAuthCredential, ProviderAuth,
};
use crate::utils::abort::{operation_signal, race_with_abort_signal};
use crate::utils::diagnostics::Thrown;
use crate::utils::models_error::{ModelsError, ModelsErrorCode};

/// Per-call overrides of [`resolve_provider_auth`].
#[derive(Debug, Clone, Default)]
pub struct AuthResolutionOverrides {
    pub api_key: Option<String>,
    pub env: Option<ProviderEnv>,
    /// Require this much remaining OAuth-token validity; defaults to five minutes.
    pub min_oauth_validity_ms: Option<f64>,
    pub signal: Option<AbortSignal>,
}

fn models_error(code: ModelsErrorCode, message: String, cause: Thrown) -> Thrown {
    Arc::new(ModelsError::with_cause(code, message, cause))
}

/// Auth resolution shared by all operations in a `Models` collection.
/// A stored credential owns the provider: ambient/env is consulted only when
/// nothing is stored. No silent env fallback after a failed refresh or for a
/// credential type without a matching handler.
///
/// # Errors
///
/// `ModelsError` ("auth"/"oauth") on store, resolver, or refresh failure; the
/// abort reason when `overrides.signal` aborts.
pub async fn resolve_provider_auth(
    provider_id: &str,
    auth: &ProviderAuth,
    credentials: &Arc<dyn CredentialStore>,
    auth_context: &Arc<dyn AuthContext>,
    overrides: AuthResolutionOverrides,
) -> Result<Option<AuthResult>, Thrown> {
    let signal = operation_signal(overrides.signal.clone());
    let provider_id = provider_id.to_owned();
    let auth = auth.clone();
    let credentials = Arc::clone(credentials);
    let auth_context = Arc::clone(auth_context);
    let operation_signal = signal.clone();
    race_with_abort_signal(
        async move {
            resolve_provider_auth_with_signal(
                &provider_id,
                &auth,
                credentials,
                auth_context,
                &overrides,
                operation_signal,
            )
            .await
        },
        &signal,
    )
    .await
}

async fn resolve_provider_auth_with_signal(
    provider_id: &str,
    auth: &ProviderAuth,
    credentials: Arc<dyn CredentialStore>,
    auth_context: Arc<dyn AuthContext>,
    overrides: &AuthResolutionOverrides,
    signal: AbortSignal,
) -> Result<Option<AuthResult>, Thrown> {
    signal.throw_if_aborted()?;
    let request_auth_context: Arc<dyn AuthContext> = match &overrides.env {
        Some(env) => Arc::new(OverlayEnvAuthContext {
            base: Arc::clone(&auth_context),
            env: env.clone(),
        }),
        None => auth_context,
    };

    if let (Some(api_key), Some(api_key_auth)) = (&overrides.api_key, &auth.api_key) {
        return resolve_api_key(
            request_auth_context,
            api_key_auth.as_ref(),
            provider_id,
            Some(ApiKeyCredential {
                kind: ApiKeyType::ApiKey,
                key: Some(api_key.clone()),
                env: overrides.env.clone(),
            }),
            signal,
        )
        .await;
    }

    let stored = read_credential(credentials.as_ref(), provider_id, &signal).await?;
    if let Some(stored) = stored {
        return match (stored, &auth.oauth, &auth.api_key) {
            (Credential::OAuth(stored), Some(oauth), _) => {
                resolve_stored_oauth(
                    credentials.as_ref(),
                    provider_id,
                    oauth,
                    stored,
                    &signal,
                    overrides.min_oauth_validity_ms,
                )
                .await
            }
            (Credential::ApiKey(stored), _, Some(api_key_auth)) => {
                let credential = match &overrides.env {
                    Some(env) => {
                        let mut merged = stored.env.clone().unwrap_or_default();
                        for (name, value) in env {
                            merged.insert(name.clone(), value.clone());
                        }
                        ApiKeyCredential {
                            env: Some(merged),
                            ..stored
                        }
                    }
                    None => stored,
                };
                resolve_api_key(
                    request_auth_context,
                    api_key_auth.as_ref(),
                    provider_id,
                    Some(credential),
                    signal,
                )
                .await
            }
            (Credential::OAuth(_), None, _) | (Credential::ApiKey(_), _, None) => Ok(None),
        };
    }

    // Ambient (env vars, AWS profiles, ADC files).
    match &auth.api_key {
        Some(api_key_auth) => {
            resolve_api_key(
                request_auth_context,
                api_key_auth.as_ref(),
                provider_id,
                None,
                signal,
            )
            .await
        }
        None => Ok(None),
    }
}

/// Request env overrides first (non-empty values), then the base context.
struct OverlayEnvAuthContext {
    base: Arc<dyn AuthContext>,
    env: ProviderEnv,
}

impl AuthContext for OverlayEnvAuthContext {
    fn env<'a>(&'a self, name: &'a str) -> BoxFuture<'a, Option<String>> {
        Box::pin(async move {
            match self.env.get(name) {
                Some(value) if !value.is_empty() => Some(value.clone()),
                _ => self.base.env(name).await,
            }
        })
    }

    fn file_exists<'a>(&'a self, path: &'a str) -> BoxFuture<'a, bool> {
        self.base.file_exists(path)
    }
}

const DEFAULT_OAUTH_MINIMUM_VALIDITY_MS: f64 = 5.0 * 60.0 * 1000.0;
const DEFAULT_OAUTH_REFRESH_TIMEOUT_MS: u64 = 15_000;

/// Refresh a stored OAuth credential under the credential-store lock and
/// persist the result before the lock is released. `needs_refresh` is
/// re-checked under the lock, so concurrent callers and processes refresh
/// only once.
///
/// `signal` cancels only the wait for the lock. Once a refresh starts, the
/// provider may already have rotated the refresh token, so the refresh and
/// its persistence ignore `signal` and are bounded only by a timeout.
/// Callers that must return promptly on cancellation race this with their
/// signal.
///
/// Resolves with the stored OAuth credential after the operation, or `None`
/// when the provider no longer has an OAuth credential.
///
/// # Errors
///
/// `ModelsError` "oauth" when the refresh fails, "auth" when the store
/// fails; the abort reason when `signal` aborts while waiting for the lock.
pub async fn refresh_stored_oauth_credential<F>(
    credentials: &dyn CredentialStore,
    provider_id: &str,
    oauth: &Arc<dyn OAuthAuth>,
    needs_refresh: F,
    signal: &AbortSignal,
) -> Result<Option<OAuthCredential>, Thrown>
where
    F: Fn(&OAuthCredential) -> bool + Send + Sync + 'static,
{
    let lock_wait = AbortController::new();
    let stop_forwarding = CancellationToken::new();
    if let Some(reason) = signal.reason() {
        lock_wait.abort(Some(reason));
    } else {
        let forward_signal = signal.clone();
        let forward_controller = lock_wait.clone();
        let stop = stop_forwarding.clone();
        tokio::spawn(async move {
            tokio::select! {
                reason = forward_signal.cancelled() => forward_controller.abort(Some(reason)),
                () = stop.cancelled() => {}
            }
        });
    }

    let fn_signal = signal.clone();
    let fn_stop = stop_forwarding.clone();
    let fn_oauth = Arc::clone(oauth);
    let fn_provider_id = provider_id.to_owned();
    let modify: ModifyFn = Box::new(move |current| {
        Box::pin(async move {
            fn_stop.cancel();
            fn_signal.throw_if_aborted()?;
            let Some(Credential::OAuth(current)) = current else {
                return Ok(None); // logged out meanwhile
            };
            if !needs_refresh(&current) {
                return Ok(None); // another process/request refreshed
            }
            match fn_oauth
                .refresh(current, timeout_signal(DEFAULT_OAUTH_REFRESH_TIMEOUT_MS))
                .await
            {
                Ok(refreshed) => Ok(Some(Credential::OAuth(refreshed))),
                Err(error) => Err(models_error(
                    ModelsErrorCode::Oauth,
                    format!("OAuth refresh failed for {fn_provider_id}"),
                    error,
                )),
            }
        })
    });

    let result = credentials
        .modify(
            provider_id,
            modify,
            AuthOperationOptions::with_signal(lock_wait.signal()),
        )
        .await;
    stop_forwarding.cancel();
    match result {
        Ok(Some(Credential::OAuth(post))) => Ok(Some(post)),
        Ok(Some(Credential::ApiKey(_)) | None) => Ok(None),
        Err(error) => {
            if error.downcast_ref::<ModelsError>().is_some() {
                return Err(error);
            }
            signal.throw_if_aborted()?;
            Err(models_error(
                ModelsErrorCode::Auth,
                format!("Credential store modify failed for {provider_id}"),
                error,
            ))
        }
    }
}

/// OAuth resolution with double-checked locking: tokens with less than five
/// minutes remaining are refreshed through [`refresh_stored_oauth_credential`].
async fn resolve_stored_oauth(
    credentials: &dyn CredentialStore,
    provider_id: &str,
    oauth: &Arc<dyn OAuthAuth>,
    stored: OAuthCredential,
    signal: &AbortSignal,
    min_oauth_validity_ms: Option<f64>,
) -> Result<Option<AuthResult>, Thrown> {
    let minimum_validity_ms =
        DEFAULT_OAUTH_MINIMUM_VALIDITY_MS.max(min_oauth_validity_ms.unwrap_or(0.0));
    let expires_soon =
        move |credential: &OAuthCredential| date_now() + minimum_validity_ms >= credential.expires;
    let mut credential = stored;

    if expires_soon(&credential) {
        // Optimistic check said expired; the authoritative check runs under the lock.
        let post =
            refresh_stored_oauth_credential(credentials, provider_id, oauth, expires_soon, signal)
                .await?;
        let Some(post) = post else {
            return Ok(None); // logged out meanwhile
        };
        credential = post;
        // The normal five-minute window triggers a refresh but does not impose a
        // provider contract. Explicit callers (such as bearer-token export) do
        // require the requested minimum after the refresh.
        if min_oauth_validity_ms.is_some() && expires_soon(&credential) {
            return Err(Arc::new(ModelsError::new(
                ModelsErrorCode::Oauth,
                format!("OAuth refresh returned a token that expires too soon for {provider_id}"),
            )));
        }
    }

    match oauth.to_auth(&credential).await {
        Ok(auth) => Ok(Some(AuthResult {
            auth,
            env: None,
            source: Some("OAuth".to_owned()),
        })),
        Err(error) => Err(models_error(
            ModelsErrorCode::Oauth,
            format!("OAuth auth derivation failed for {provider_id}"),
            error,
        )),
    }
}

async fn resolve_api_key(
    auth_context: Arc<dyn AuthContext>,
    api_key: &dyn ApiKeyAuth,
    provider_id: &str,
    credential: Option<ApiKeyCredential>,
    signal: AbortSignal,
) -> Result<Option<AuthResult>, Thrown> {
    api_key
        .resolve(ApiKeyResolveInput {
            ctx: auth_context,
            credential,
            signal,
        })
        .await
        .map_err(|error| {
            models_error(
                ModelsErrorCode::Auth,
                format!("API key auth failed for provider {provider_id}"),
                error,
            )
        })
}

async fn read_credential(
    credentials: &dyn CredentialStore,
    provider_id: &str,
    signal: &AbortSignal,
) -> Result<Option<Credential>, Thrown> {
    credentials
        .read(
            provider_id,
            AuthOperationOptions::with_signal(signal.clone()),
        )
        .await
        .map_err(|error| {
            models_error(
                ModelsErrorCode::Auth,
                format!("Credential store read failed for {provider_id}"),
                error,
            )
        })
}
