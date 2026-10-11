//! The [`Models`] collection: provider registry, model listing, and auth.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::{AbortController, AbortSignal};
use eukhe_types::pi_ai::IndexMap;
use eukhe_types::pi_ai::{AnyModel, Model, ModelType};
use futures::future::try_join_all;

use super::provider::Provider;
use super::{merge_headers, model_headers_as_provider_headers, CatalogModel};
use crate::auth::{
    default_provider_auth_context, refresh_stored_oauth_credential, resolve_provider_auth,
    ApiKeyCredential, ApiKeyResolveInput, AuthCheck, AuthContext, AuthInteraction,
    AuthOperationOptions, AuthResolutionOverrides, AuthResult, AuthType, Credential,
    CredentialStore, InMemoryCredentialStore, LoginOptions, OAuthCredential,
    ProviderAuthInteraction,
};
use crate::models_store::{InMemoryModelsStore, ModelsStore};
use crate::utils::abort::{operation_signal, race_with_abort_signal};
use crate::utils::diagnostics::Thrown;
use crate::utils::model_operations::is_model_type;
use crate::utils::models_error::{ModelsError, ModelsErrorCode};

pub(super) fn models_error(code: ModelsErrorCode, message: String) -> Thrown {
    Arc::new(ModelsError::new(code, message))
}

pub(super) fn models_error_with_cause(
    code: ModelsErrorCode,
    message: String,
    cause: Thrown,
) -> Thrown {
    Arc::new(ModelsError::with_cause(code, message, cause))
}

/// Options of [`create_models`]: TS `CreateModelsOptions`.
#[derive(Clone, Default)]
pub struct CreateModelsOptions {
    pub credentials: Option<Arc<dyn CredentialStore>>,
    pub models_store: Option<Arc<dyn ModelsStore>>,
    pub auth_context: Option<Arc<dyn AuthContext>>,
}

/// Per-provider refresh bookkeeping.
#[derive(Default)]
pub(super) struct RefreshState {
    pub(super) generations: HashMap<String, u64>,
    pub(super) controllers: IndexMap<String, AbortController>,
}

pub(super) struct ModelsInner {
    pub(super) providers: Mutex<IndexMap<String, Arc<Provider>>>,
    pub(super) credentials: Arc<dyn CredentialStore>,
    pub(super) models_store: Arc<dyn ModelsStore>,
    pub(super) auth_context: Arc<dyn AuthContext>,
    pub(super) refresh: Mutex<RefreshState>,
    /// Per-provider publication serialization: the TS publication chains.
    pub(super) publication_locks: Mutex<HashMap<String, Arc<tokio::sync::Mutex<()>>>>,
}

/// Runtime collection of providers plus auth application and request
/// convenience. Providers own request behavior; `Models` resolves auth and
/// delegates each request to the provider that owns the model. TS `Models`
/// and `MutableModels` in one handle; clones share the collection.
///
/// Read accessors come in three flavors: the unqualified ones (`get_models`,
/// `get_model`, `get_available`) return chat models, the `*_of_type`
/// accessors return one model type, and `get_all_models` /
/// `get_all_available` return every type.
#[derive(Clone)]
pub struct Models {
    pub(super) inner: Arc<ModelsInner>,
}

/// Creates an empty collection.
#[must_use]
pub fn create_models(options: CreateModelsOptions) -> Models {
    Models {
        inner: Arc::new(ModelsInner {
            providers: Mutex::new(IndexMap::new()),
            credentials: options
                .credentials
                .unwrap_or_else(|| Arc::new(InMemoryCredentialStore::new())),
            models_store: options
                .models_store
                .unwrap_or_else(|| Arc::new(InMemoryModelsStore::new())),
            auth_context: options
                .auth_context
                .unwrap_or_else(default_provider_auth_context),
            refresh: Mutex::new(RefreshState::default()),
            publication_locks: Mutex::new(HashMap::new()),
        }),
    }
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// One provider with its stored credential and configured auth.
pub(super) struct AuthenticatedProvider {
    pub(super) provider: Arc<Provider>,
    pub(super) credential: Option<Credential>,
}

impl Models {
    pub(super) fn providers_lock(&self) -> MutexGuard<'_, IndexMap<String, Arc<Provider>>> {
        lock(&self.inner.providers)
    }

    pub(super) fn refresh_lock(&self) -> MutexGuard<'_, RefreshState> {
        lock(&self.inner.refresh)
    }

    pub(super) fn publication_locks(
        &self,
    ) -> MutexGuard<'_, HashMap<String, Arc<tokio::sync::Mutex<()>>>> {
        lock(&self.inner.publication_locks)
    }

    /// Upsert/replace by `provider.id`. Provider ids are unique.
    pub fn set_provider(&self, provider: Provider) {
        self.supersede_provider_refresh(&provider.id);
        self.providers_lock()
            .insert(provider.id.clone(), Arc::new(provider));
    }

    pub fn delete_provider(&self, id: &str) {
        self.supersede_provider_refresh(id);
        self.providers_lock().shift_remove(id);
    }

    pub fn clear_providers(&self) {
        let mut ids: Vec<String> = self.providers_lock().keys().cloned().collect();
        for id in self.refresh_lock().controllers.keys() {
            if !ids.contains(id) {
                ids.push(id.clone());
            }
        }
        for id in &ids {
            self.supersede_provider_refresh(id);
        }
        self.providers_lock().clear();
    }

    #[must_use]
    pub fn get_providers(&self) -> Vec<Arc<Provider>> {
        self.providers_lock().values().cloned().collect()
    }

    #[must_use]
    pub fn get_provider(&self, id: &str) -> Option<Arc<Provider>> {
        self.providers_lock().get(id).cloned()
    }

    /// Sync read of last-known chat models from one provider or all
    /// providers. Best-effort: a provider whose `get_models` fails yields no
    /// models.
    #[must_use]
    pub fn get_models(&self, provider: Option<&str>) -> Vec<Model> {
        if let Some(provider) = provider {
            let Some(entry) = self.get_provider(provider) else {
                return Vec::new();
            };
            return (entry.get_models)().unwrap_or_default();
        }
        self.get_providers()
            .iter()
            .flat_map(|entry| (entry.get_models)().unwrap_or_default())
            .collect()
    }

    fn provider_all_models(provider: &Provider) -> Result<Vec<AnyModel>, Thrown> {
        match &provider.get_all_models {
            Some(get_all_models) => get_all_models(),
            None => (provider.get_models)()
                .map(|models| models.into_iter().map(AnyModel::Chat).collect()),
        }
    }

    /// Sync read of last-known models of every type from one provider or all
    /// providers. Best-effort like [`Models::get_models`].
    #[must_use]
    pub fn get_all_models(&self, provider: Option<&str>) -> Vec<AnyModel> {
        if let Some(provider) = provider {
            let Some(entry) = self.get_provider(provider) else {
                return Vec::new();
            };
            return Self::provider_all_models(&entry).unwrap_or_default();
        }
        self.get_providers()
            .iter()
            .flat_map(|entry| Self::provider_all_models(entry).unwrap_or_default())
            .collect()
    }

    /// Sync read of last-known models of one type.
    #[must_use]
    pub fn get_models_of_type(
        &self,
        model_type: ModelType,
        provider: Option<&str>,
    ) -> Vec<AnyModel> {
        self.get_all_models(provider)
            .into_iter()
            .filter(|model| is_model_type(model, model_type))
            .collect()
    }

    /// Sync runtime chat model lookup against last-known lists.
    #[must_use]
    pub fn get_model(&self, provider: &str, id: &str) -> Option<Model> {
        self.get_models(Some(provider))
            .into_iter()
            .find(|model| model.id == id)
    }

    /// Sync runtime lookup of a model of one type against last-known lists.
    #[must_use]
    pub fn get_model_of_type(
        &self,
        model_type: ModelType,
        provider: &str,
        id: &str,
    ) -> Option<AnyModel> {
        self.get_models_of_type(model_type, Some(provider))
            .into_iter()
            .find(|model| model.id() == id)
    }

    pub(super) fn supersede_provider_refresh(&self, provider_id: &str) -> u64 {
        let (generation, previous) = {
            let mut state = self.refresh_lock();
            let generation = state.generations.get(provider_id).copied().unwrap_or(0) + 1;
            state.generations.insert(provider_id.to_owned(), generation);
            (generation, state.controllers.shift_remove(provider_id))
        };
        if let Some(previous) = previous {
            previous.abort(None);
        }
        generation
    }

    pub(super) async fn read_credential(
        &self,
        provider_id: &str,
        signal: &AbortSignal,
    ) -> Result<Option<Credential>, Thrown> {
        self.inner
            .credentials
            .read(
                provider_id,
                AuthOperationOptions::with_signal(signal.clone()),
            )
            .await
            .map_err(|error| {
                models_error_with_cause(
                    ModelsErrorCode::Auth,
                    format!("Credential store read failed for {provider_id}"),
                    error,
                )
            })
    }

    pub(super) async fn resolve_refresh_credential(
        &self,
        provider: &Provider,
        stored: Option<Credential>,
        signal: &AbortSignal,
    ) -> Result<Option<Credential>, Thrown> {
        if let Some(Credential::OAuth(stored)) = &stored {
            let Some(oauth) = &provider.auth.oauth else {
                return Ok(None);
            };
            if super::date_now() < stored.expires {
                return Ok(Some(Credential::OAuth(stored.clone())));
            }
            if signal.aborted() {
                return Ok(None);
            }
            // A refresh that has started survives cancellation or a
            // superseding model refresh, so a rotated refresh token is always
            // persisted. A newer refresh then sees the fresh credential.
            return refresh_stored_oauth_credential(
                self.inner.credentials.as_ref(),
                &provider.id,
                oauth,
                |current: &OAuthCredential| super::date_now() >= current.expires,
                signal,
            )
            .await
            .map(|credential| credential.map(Credential::OAuth));
        }

        let Some(api_key) = &provider.auth.api_key else {
            return Ok(None);
        };
        let credential = match stored {
            Some(Credential::ApiKey(credential)) => Some(credential),
            Some(Credential::OAuth(_)) | None => None,
        };
        let result = api_key
            .resolve(ApiKeyResolveInput {
                ctx: Arc::clone(&self.inner.auth_context),
                credential,
                signal: signal.clone(),
            })
            .await?;
        Ok(result.map(|result| {
            Credential::ApiKey(ApiKeyCredential {
                key: result.auth.api_key,
                env: result.env,
                ..ApiKeyCredential::default()
            })
        }))
    }

    async fn check_provider_auth(
        &self,
        provider: &Provider,
        credential: Option<&Credential>,
        signal: &AbortSignal,
    ) -> Result<Option<AuthCheck>, Thrown> {
        if let Some(Credential::OAuth(_)) = credential {
            return Ok(provider.auth.oauth.as_ref().map(|_| AuthCheck {
                source: Some("OAuth".to_owned()),
                kind: AuthType::OAuth,
            }));
        }
        let Some(api_key) = &provider.auth.api_key else {
            return Ok(None);
        };
        let api_key_credential = match credential {
            Some(Credential::ApiKey(credential)) => Some(credential.clone()),
            Some(Credential::OAuth(_)) | None => None,
        };
        let input = ApiKeyResolveInput {
            ctx: Arc::clone(&self.inner.auth_context),
            credential: api_key_credential,
            signal: signal.clone(),
        };
        if let Some(check) = api_key.check(input) {
            return check.await.map_err(|error| {
                models_error_with_cause(
                    ModelsErrorCode::Auth,
                    format!("API key auth check failed for provider {}", provider.id),
                    error,
                )
            });
        }

        let resolution = resolve_provider_auth(
            &provider.id,
            &provider.auth,
            &self.inner.credentials,
            &self.inner.auth_context,
            AuthResolutionOverrides {
                signal: Some(signal.clone()),
                ..AuthResolutionOverrides::default()
            },
        )
        .await?;
        Ok(resolution.map(|resolution| AuthCheck {
            source: resolution.source,
            kind: AuthType::ApiKey,
        }))
    }

    /// Check whether a provider has complete auth configuration without
    /// refreshing OAuth. `None` for unknown or unconfigured providers.
    ///
    /// # Errors
    ///
    /// `ModelsError` "auth" on credential-store or check failure; the abort
    /// reason when the signal aborts.
    pub async fn check_auth(
        &self,
        provider_id: &str,
        options: AuthOperationOptions,
    ) -> Result<Option<AuthCheck>, Thrown> {
        let signal = operation_signal(options.signal);
        let this = self.clone();
        let provider_id = provider_id.to_owned();
        let check_signal = signal.clone();
        race_with_abort_signal(
            async move {
                check_signal.throw_if_aborted()?;
                let Some(provider) = this.get_provider(&provider_id) else {
                    return Ok(None);
                };
                let credential = this.read_credential(&provider_id, &check_signal).await?;
                this.check_provider_auth(&provider, credential.as_ref(), &check_signal)
                    .await
            },
            &signal,
        )
        .await
    }

    async fn get_authenticated_providers(
        &self,
        provider_id: Option<&str>,
        signal: &AbortSignal,
    ) -> Result<Vec<AuthenticatedProvider>, Thrown> {
        signal.throw_if_aborted()?;
        let providers: Vec<Arc<Provider>> = match provider_id {
            Some(provider_id) => self.get_provider(provider_id).into_iter().collect(),
            None => self.get_providers(),
        };
        let checks = try_join_all(providers.into_iter().map(|provider| async move {
            let credential = self.read_credential(&provider.id, signal).await?;
            let auth = self
                .check_provider_auth(&provider, credential.as_ref(), signal)
                .await?;
            Ok::<_, Thrown>(auth.map(|_| AuthenticatedProvider {
                provider,
                credential,
            }))
        }))
        .await?;
        Ok(checks.into_iter().flatten().collect())
    }

    /// Chat models whose providers have complete auth configuration, after
    /// each provider's credential-specific filter.
    ///
    /// # Errors
    ///
    /// Auth-check failures, a provider's `get_models` failure, or the abort
    /// reason when the signal aborts.
    pub async fn get_available(
        &self,
        provider_id: Option<&str>,
        options: AuthOperationOptions,
    ) -> Result<Vec<Model>, Thrown> {
        let signal = operation_signal(options.signal);
        let this = self.clone();
        let provider_id = provider_id.map(str::to_owned);
        let available_signal = signal.clone();
        race_with_abort_signal(
            async move {
                let providers = this
                    .get_authenticated_providers(provider_id.as_deref(), &available_signal)
                    .await?;
                let mut available = Vec::new();
                for AuthenticatedProvider {
                    provider,
                    credential,
                } in providers
                {
                    let models = (provider.get_models)()?;
                    available.extend(match &provider.filter_models {
                        Some(filter) => filter(models, credential.as_ref()),
                        None => models,
                    });
                }
                Ok(available)
            },
            &signal,
        )
        .await
    }

    /// Models of one type whose providers have complete auth configuration.
    ///
    /// # Errors
    ///
    /// Like [`Models::get_all_available`].
    pub async fn get_available_of_type(
        &self,
        model_type: ModelType,
        provider_id: Option<&str>,
        options: AuthOperationOptions,
    ) -> Result<Vec<AnyModel>, Thrown> {
        Ok(self
            .get_all_available(provider_id, options)
            .await?
            .into_iter()
            .filter(|model| is_model_type(model, model_type))
            .collect())
    }

    /// Models of every type whose providers have complete auth
    /// configuration.
    ///
    /// # Errors
    ///
    /// Auth-check failures, a provider's model-listing failure, or the abort
    /// reason when the signal aborts.
    pub async fn get_all_available(
        &self,
        provider_id: Option<&str>,
        options: AuthOperationOptions,
    ) -> Result<Vec<AnyModel>, Thrown> {
        let signal = operation_signal(options.signal);
        let this = self.clone();
        let provider_id = provider_id.map(str::to_owned);
        let available_signal = signal.clone();
        race_with_abort_signal(
            async move {
                let providers = this
                    .get_authenticated_providers(provider_id.as_deref(), &available_signal)
                    .await?;
                let mut available = Vec::new();
                for AuthenticatedProvider {
                    provider,
                    credential,
                } in providers
                {
                    let models = Self::provider_all_models(&provider)?;
                    if let Some(filter_all) = &provider.filter_all_models {
                        available.extend(filter_all(models, credential.as_ref()));
                        continue;
                    }
                    let Some(filter) = &provider.filter_models else {
                        available.extend(models);
                        continue;
                    };
                    let available_chat_ids: Vec<String> =
                        filter((provider.get_models)()?, credential.as_ref())
                            .into_iter()
                            .map(|model| model.id)
                            .collect();
                    available.extend(models.into_iter().filter(|model| {
                        !is_model_type(model, ModelType::Chat)
                            || available_chat_ids.iter().any(|id| id == model.id())
                    }));
                }
                Ok(available)
            },
            &signal,
        )
        .await
    }

    /// Resolve provider-scoped auth by provider id, with a source label for
    /// status UI. `None` when the provider is unknown or unconfigured.
    ///
    /// # Errors
    ///
    /// `ModelsError` "oauth" when a token refresh fails (the stored credential
    /// is preserved for retry), "auth" when api-key resolution or the
    /// credential store fails; the abort reason when the signal aborts.
    pub async fn get_auth(
        &self,
        provider_id: &str,
        overrides: AuthResolutionOverrides,
    ) -> Result<Option<AuthResult>, Thrown> {
        let signal = operation_signal(overrides.signal.clone());
        let Some(provider) = self.get_provider(provider_id) else {
            return Ok(None);
        };
        resolve_provider_auth(
            &provider.id,
            &provider.auth,
            &self.inner.credentials,
            &self.inner.auth_context,
            AuthResolutionOverrides {
                signal: Some(signal),
                ..overrides
            },
        )
        .await
    }

    /// Provider auth for `model`'s provider plus the model's static headers
    /// (model headers override auth headers case-insensitively).
    ///
    /// # Errors
    ///
    /// Like [`Models::get_auth`].
    pub async fn get_auth_for_model<M: CatalogModel>(
        &self,
        model: &M,
        overrides: AuthResolutionOverrides,
    ) -> Result<Option<AuthResult>, Thrown> {
        let result = self.get_auth(model.provider_id(), overrides).await?;
        let (Some(mut result), Some(model_headers)) = (result.clone(), model.model_headers())
        else {
            return Ok(result);
        };
        result.auth.headers = merge_headers(
            result.auth.headers.as_ref(),
            Some(&model_headers_as_provider_headers(model_headers)),
        );
        Ok(Some(result))
    }

    /// Run a provider-owned login flow and persist its returned credential.
    ///
    /// # Errors
    ///
    /// `ModelsError` "provider" for an unknown provider, "auth" when the
    /// provider has no login for `auth_type` or the credential store fails;
    /// the login flow's failure; the abort reason when the signal aborts
    /// before the credential write starts.
    pub async fn login(
        &self,
        provider_id: &str,
        auth_type: AuthType,
        interaction: Arc<dyn AuthInteraction>,
        options: Option<LoginOptions>,
    ) -> Result<Credential, Thrown> {
        let signal = operation_signal(interaction.signal());
        signal.throw_if_aborted()?;
        let provider = self.get_provider(provider_id).ok_or_else(|| {
            models_error(
                ModelsErrorCode::Provider,
                format!("Unknown provider: {provider_id}"),
            )
        })?;
        let unsupported = models_error(
            ModelsErrorCode::Auth,
            format!(
                "{} does not support {} login",
                provider.name,
                auth_type.as_str()
            ),
        );
        let has_method = match auth_type {
            AuthType::OAuth => provider.auth.oauth.is_some(),
            AuthType::ApiKey => provider.auth.api_key.is_some(),
        };
        if !has_method {
            return Err(unsupported);
        }
        let provider_interaction = ProviderAuthInteraction::new(interaction, signal.clone());
        let login_provider = Arc::clone(&provider);
        let login_operation = async move {
            match (
                auth_type,
                &login_provider.auth.oauth,
                &login_provider.auth.api_key,
            ) {
                (AuthType::OAuth, Some(oauth), _) => oauth
                    .login(provider_interaction, options)
                    .await
                    .map(Credential::OAuth),
                (AuthType::ApiKey, _, Some(api_key)) => match api_key.login(provider_interaction) {
                    Some(login) => login.await.map(Credential::ApiKey),
                    None => Err(unsupported),
                },
                (AuthType::OAuth | AuthType::ApiKey, _, _) => Err(unsupported),
            }
        };
        let credential = race_with_abort_signal(login_operation, &signal).await?;

        let (started_tx, started_rx) = tokio::sync::oneshot::channel::<()>();
        let credentials = Arc::clone(&self.inner.credentials);
        let stored = credential.clone();
        let mutation_provider_id = provider_id.to_owned();
        let mutation_signal = signal.clone();
        let mut mutation = tokio::spawn(async move {
            credentials
                .modify(
                    &mutation_provider_id,
                    Box::new(move |_current| {
                        Box::pin(async move {
                            // Receiver gone means the login stopped waiting.
                            let _ = started_tx.send(());
                            Ok(Some(stored))
                        })
                    }),
                    AuthOperationOptions::with_signal(mutation_signal),
                )
                .await
        });

        let wrap = |error: Thrown| -> Thrown {
            if let Some(reason) = signal.reason() {
                return reason;
            }
            models_error_with_cause(
                ModelsErrorCode::Auth,
                format!("Credential store modify failed for {provider_id}"),
                error,
            )
        };
        let join = |result: Result<Result<Option<Credential>, Thrown>, tokio::task::JoinError>| {
            match result {
                Ok(result) => result.map(|_| ()),
                Err(error) => std::panic::resume_unwind(error.into_panic()),
            }
        };
        let mut started_rx = started_rx;
        tokio::select! {
            biased;
            started = &mut started_rx => {
                // A dropped sender means the mutation ended without running.
                if started.is_err() {
                    return join((&mut mutation).await).map(|()| credential).map_err(wrap);
                }
            }
            result = &mut mutation => {
                return join(result).map(|()| credential).map_err(wrap);
            }
            reason = signal.cancelled() => {
                // Aborted before the write started: stop waiting; the
                // mutation's own signal cancels its queued lock wait.
                return Err(reason);
            }
        }
        join(mutation.await).map_err(wrap)?;
        Ok(credential)
    }

    /// Remove the stored credential for a provider.
    ///
    /// # Errors
    ///
    /// `ModelsError` "auth" when the store fails; the abort reason when the
    /// signal aborts.
    pub async fn logout(
        &self,
        provider_id: &str,
        options: AuthOperationOptions,
    ) -> Result<(), Thrown> {
        let signal = operation_signal(options.signal);
        signal.throw_if_aborted()?;
        self.inner
            .credentials
            .delete(
                provider_id,
                AuthOperationOptions::with_signal(signal.clone()),
            )
            .await
            .map_err(|error| {
                if let Some(reason) = signal.reason() {
                    return reason;
                }
                models_error_with_cause(
                    ModelsErrorCode::Auth,
                    format!("Credential store delete failed for {provider_id}"),
                    error,
                )
            })
    }
}
