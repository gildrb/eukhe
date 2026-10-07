//! Default in-memory credential store. Port of `auth/credential-store.ts`.

use std::collections::HashMap;
use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_types::pi_ai::IndexMap;
use futures::future::BoxFuture;

use super::types::{AuthOperationOptions, Credential, CredentialInfo, CredentialStore, ModifyFn};
use crate::utils::abort::{operation_signal, race_with_abort_signal};
use crate::utils::diagnostics::Thrown;

/// Default in-memory credential store. Apps inject persistent stores.
/// Keyed by `Provider.id`, one credential per provider; see [`CredentialStore`].
/// Writes are serialized per provider through a FIFO lock (the TS promise chain).
#[derive(Clone, Default)]
pub struct InMemoryCredentialStore {
    inner: Arc<Inner>,
}

#[derive(Default)]
struct Inner {
    /// Insertion-ordered like the JS `Map`.
    credentials: Mutex<IndexMap<String, Credential>>,
    chains: Mutex<HashMap<String, Arc<tokio::sync::Mutex<()>>>>,
}

impl Inner {
    fn credentials(&self) -> std::sync::MutexGuard<'_, IndexMap<String, Credential>> {
        self.credentials
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    fn chain(&self, provider_id: &str) -> Arc<tokio::sync::Mutex<()>> {
        let mut chains = self.chains.lock().unwrap_or_else(PoisonError::into_inner);
        Arc::clone(chains.entry(provider_id.to_owned()).or_default())
    }
}

impl InMemoryCredentialStore {
    /// An empty store.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Serialize tasks per provider id without releasing the chain before
    /// active work settles. A caller whose signal aborts stops waiting at
    /// once; its queued task still takes its turn and then fails the abort
    /// check, like the TS chain.
    async fn enqueue<T, Fut>(
        &self,
        provider_id: &str,
        task: impl FnOnce() -> Fut + Send + 'static,
        options: &AuthOperationOptions,
    ) -> Result<T, Thrown>
    where
        T: Send + 'static,
        Fut: Future<Output = Result<T, Thrown>> + Send + 'static,
    {
        let signal = operation_signal(options.signal.clone());
        let chain = self.inner.chain(provider_id);
        // Take the queue position now: tokio's mutex is FIFO, matching the
        // order in which the TS chain links calls.
        let queued_signal = signal.clone();
        let guard_future = chain.lock_owned();
        let queued = async move {
            let _turn = guard_future.await;
            queued_signal.throw_if_aborted()?;
            task().await
        };
        race_with_abort_signal(queued, &signal).await
    }
}

impl CredentialStore for InMemoryCredentialStore {
    fn read<'a>(
        &'a self,
        provider_id: &'a str,
        options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<Option<Credential>, Thrown>> {
        Box::pin(async move {
            if let Some(signal) = &options.signal {
                signal.throw_if_aborted()?;
            }
            Ok(self.inner.credentials().get(provider_id).cloned())
        })
    }

    fn list(
        &self,
        options: AuthOperationOptions,
    ) -> BoxFuture<'_, Result<Vec<CredentialInfo>, Thrown>> {
        Box::pin(async move {
            if let Some(signal) = &options.signal {
                signal.throw_if_aborted()?;
            }
            Ok(self
                .inner
                .credentials()
                .iter()
                .map(|(provider_id, credential)| CredentialInfo {
                    provider_id: provider_id.clone(),
                    kind: credential.auth_type(),
                })
                .collect())
        })
    }

    fn modify<'a>(
        &'a self,
        provider_id: &'a str,
        f: ModifyFn,
        options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<Option<Credential>, Thrown>> {
        let inner = Arc::clone(&self.inner);
        let key = provider_id.to_owned();
        let task_signal = options.signal.clone();
        Box::pin(async move {
            self.enqueue(
                provider_id,
                move || async move {
                    let current = inner.credentials().get(&key).cloned();
                    let next = f(current.clone()).await?;
                    if let Some(signal) = &task_signal {
                        signal.throw_if_aborted()?;
                    }
                    match next {
                        Some(next) => {
                            inner.credentials().insert(key, next.clone());
                            Ok(Some(next))
                        }
                        None => Ok(current),
                    }
                },
                &options,
            )
            .await
        })
    }

    fn delete<'a>(
        &'a self,
        provider_id: &'a str,
        options: AuthOperationOptions,
    ) -> BoxFuture<'a, Result<(), Thrown>> {
        let inner = Arc::clone(&self.inner);
        let key = provider_id.to_owned();
        Box::pin(async move {
            self.enqueue(
                provider_id,
                move || async move {
                    inner.credentials().shift_remove(&key);
                    Ok(())
                },
                &options,
            )
            .await
        })
    }
}
