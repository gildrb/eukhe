//! Dynamic catalog refresh: [`Models::refresh`] and the generation-checked
//! publication its providers use.

use std::collections::HashSet;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{AbortController, AbortSignal};
use eukhe_types::pi_ai::IndexMap;
use futures::future::join_all;

use super::collection::Models;
use super::provider::{ModelsPersistence, ModelsPublication, Provider, RefreshModelsContext};
use crate::auth::Credential;
use crate::models_store::ModelsStoreOperationOptions;
use crate::utils::abort::{operation_signal, race_with_abort_signal};
use crate::utils::diagnostics::Thrown;

/// Options of [`Models::refresh`]: TS `ModelsRefreshOptions`.
#[derive(Debug, Clone, Default)]
pub struct ModelsRefreshOptions {
    /// Default: true.
    pub allow_network: Option<bool>,
    /// Restrict refresh to these provider ids. Unknown and static providers
    /// are ignored.
    pub providers: Option<Vec<String>>,
    /// Bypass provider freshness checks and fetch immediately when network
    /// access is allowed.
    pub force: Option<bool>,
    pub signal: Option<AbortSignal>,
}

/// Outcome of [`Models::refresh`]: TS `ModelsRefreshResult`.
#[derive(Debug, Clone, Default)]
pub struct ModelsRefreshResult {
    pub aborted: bool,
    /// Provider failures by provider id, in failure order.
    pub errors: IndexMap<String, Thrown>,
}

/// Awaits a spawned task, re-raising its panic.
async fn join<T>(handle: tokio::task::JoinHandle<T>) -> T {
    match handle.await {
        Ok(value) => value,
        Err(error) => std::panic::resume_unwind(error.into_panic()),
    }
}

impl Models {
    fn begin_provider_refresh(&self, provider_id: &str) -> (u64, AbortController) {
        let generation = self.supersede_provider_refresh(provider_id);
        let controller = AbortController::new();
        self.refresh_lock()
            .controllers
            .insert(provider_id.to_owned(), controller.clone());
        (generation, controller)
    }

    fn current_generation(&self, provider_id: &str) -> Option<u64> {
        self.refresh_lock().generations.get(provider_id).copied()
    }

    async fn publish_provider_models(
        &self,
        provider_id: String,
        generation: u64,
        signal: AbortSignal,
        publication: ModelsPublication,
    ) -> Result<bool, Thrown> {
        let lock = Arc::clone(
            self.publication_locks()
                .entry(provider_id.clone())
                .or_default(),
        );
        let this = self.clone();
        let queued_signal = signal.clone();
        let queued = tokio::spawn(async move {
            let result = {
                let _chain = lock.lock().await;
                this.run_publication(&provider_id, generation, &queued_signal, publication)
                    .await
            };
            // Drop the chain entry when no publication is queued behind us.
            let mut locks = this.publication_locks();
            if locks
                .get(&provider_id)
                .is_some_and(|entry| Arc::ptr_eq(entry, &lock) && Arc::strong_count(&lock) == 2)
            {
                locks.remove(&provider_id);
            }
            result
        });
        race_with_abort_signal(join(queued), &signal).await
    }

    async fn run_publication(
        &self,
        provider_id: &str,
        generation: u64,
        signal: &AbortSignal,
        publication: ModelsPublication,
    ) -> Result<bool, Thrown> {
        if signal.aborted() || self.current_generation(provider_id) != Some(generation) {
            return Ok(false);
        }
        let store_options = ModelsStoreOperationOptions {
            signal: Some(signal.clone()),
        };
        match publication.persist {
            ModelsPersistence::Keep => {}
            ModelsPersistence::Delete => {
                self.inner
                    .models_store
                    .delete(provider_id, store_options)
                    .await?;
            }
            ModelsPersistence::Write(entry) => {
                self.inner
                    .models_store
                    .write(provider_id, entry, store_options)
                    .await?;
            }
        }
        if signal.aborted() || self.current_generation(provider_id) != Some(generation) {
            return Ok(false);
        }
        if let Some(update) = publication.update {
            update();
        }
        Ok(true)
    }

    async fn run_provider_refresh_phase(
        &self,
        provider: &Provider,
        credential: Option<Credential>,
        allow_network: bool,
        force: Option<bool>,
        generation: u64,
        signal: &AbortSignal,
    ) -> Result<(), Thrown> {
        let Some(refresh_models) = &provider.refresh_models else {
            return Ok(());
        };
        let stored = self
            .inner
            .models_store
            .read(
                &provider.id,
                ModelsStoreOperationOptions {
                    signal: Some(signal.clone()),
                },
            )
            .await?;
        let this = self.clone();
        let provider_id = provider.id.clone();
        let publish_signal = signal.clone();
        refresh_models(RefreshModelsContext {
            credential,
            stored,
            publisher: Arc::new(move |publication| {
                let this = this.clone();
                let provider_id = provider_id.clone();
                let signal = publish_signal.clone();
                Box::pin(async move {
                    this.publish_provider_models(provider_id, generation, signal, publication)
                        .await
                })
            }),
            allow_network,
            force: if allow_network { force } else { None },
            signal: signal.clone(),
        })
        .await
    }

    async fn refresh_provider(
        self,
        provider: Arc<Provider>,
        allow_network: bool,
        force: Option<bool>,
        generation: u64,
        signal: AbortSignal,
    ) -> Result<(), Thrown> {
        let (stored_credential, credential_error) =
            match self.read_credential(&provider.id, &signal).await {
                Ok(credential) => (credential, None),
                Err(error) => (None, Some(error)),
            };

        // Restore cached provider state before auth resolution or network access.
        self.run_provider_refresh_phase(
            &provider,
            stored_credential.clone(),
            false,
            None,
            generation,
            &signal,
        )
        .await?;
        if let Some(error) = credential_error {
            return Err(error);
        }
        if !allow_network || signal.aborted() {
            return Ok(());
        }

        let Some(credential) = self
            .resolve_refresh_credential(&provider, stored_credential, &signal)
            .await?
        else {
            return Ok(());
        };
        self.run_provider_refresh_phase(
            &provider,
            Some(credential),
            true,
            force,
            generation,
            &signal,
        )
        .await
    }

    /// Refresh selected configured dynamic providers concurrently (all when
    /// `providers` is omitted). Provider errors and cancellation are returned
    /// without failing; static, unknown, and unconfigured providers are
    /// skipped.
    pub async fn refresh(&self, options: ModelsRefreshOptions) -> ModelsRefreshResult {
        let allow_network = options.allow_network.unwrap_or(true);
        let caller_signal = operation_signal(options.signal);
        let errors: Arc<Mutex<IndexMap<String, Thrown>>> = Arc::default();
        if caller_signal.aborted() {
            return ModelsRefreshResult {
                aborted: true,
                errors: IndexMap::new(),
            };
        }
        let selected: Option<HashSet<String>> =
            options.providers.map(|ids| ids.into_iter().collect());
        let refreshable: Vec<Arc<Provider>> = self
            .get_providers()
            .into_iter()
            .filter(|provider| {
                provider.refresh_models.is_some()
                    && selected
                        .as_ref()
                        .is_none_or(|selected| selected.contains(&provider.id))
            })
            .collect();

        let refreshes: Vec<_> = refreshable
            .into_iter()
            .map(|provider| {
                let (generation, controller) = self.begin_provider_refresh(&provider.id);
                let signal = AbortSignal::any(&[caller_signal.clone(), controller.signal()]);
                let operation = tokio::spawn(self.clone().refresh_provider(
                    Arc::clone(&provider),
                    allow_network,
                    options.force,
                    generation,
                    signal.clone(),
                ));
                let this = self.clone();
                let errors = Arc::clone(&errors);
                async move {
                    if let Err(error) = race_with_abort_signal(join(operation), &signal).await {
                        if !signal.aborted() {
                            errors
                                .lock()
                                .unwrap_or_else(PoisonError::into_inner)
                                .insert(provider.id.clone(), error);
                        }
                    }
                    let mut state = this.refresh_lock();
                    if state
                        .controllers
                        .get(&provider.id)
                        .is_some_and(|current| current.signal().same(&controller.signal()))
                    {
                        state.controllers.shift_remove(&provider.id);
                    }
                }
            })
            .collect();

        let refresh = tokio::spawn(join_all(refreshes));
        let all_settled = async move {
            join(refresh).await;
            Ok::<(), Thrown>(())
        };
        // The per-provider waits never fail, so only cancellation ends this
        // early; the refreshes then settle in the background.
        let _ = race_with_abort_signal(all_settled, &caller_signal).await;

        let errors = errors
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        ModelsRefreshResult {
            aborted: caller_signal.aborted(),
            errors,
        }
    }
}
