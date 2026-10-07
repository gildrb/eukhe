//! The public entry points (port of `api.ts`).
//!
//! TS `replicatedState(initialOrSource, options)` dispatches on whether its
//! argument has an `attach` method; Rust has
//! [`replicated_state`](crate::replicated_state) and
//! [`replicated_state_from_source`](crate::replicated_state_from_source).
//! `defineService(id, { local: true })` is [`define_local_service`].

use std::fmt;
use std::sync::{Arc, Mutex, PoisonError};

use futures::future::BoxFuture;
use futures::FutureExt;

use crate::error::{AggregateError, ChordError};
use crate::facets::host::{Facet, FacetKernel, FacetOptions};
use crate::facets::loader::{dispose_loaded_facets, FacetLoader, LoadedFacets};
use crate::services::provider::RemoteServiceProvider;
use crate::types::{Service, ServiceToken};

/// An active host for one complete set of facets.
#[derive(Clone)]
pub struct FacetHost {
    kernel: FacetKernel,
    services: RemoteServiceProvider,
}

impl FacetHost {
    /// The provider publishing the host's remotely exposable services.
    #[must_use]
    pub fn services(&self) -> &RemoteServiceProvider {
        &self.services
    }

    /// Activate and replace facets with matching IDs without disconnecting
    /// consumer service handles.
    ///
    /// # Errors
    ///
    /// The TS reload failures; failures after cutover terminate the host.
    pub async fn reload(&self, facets: Vec<Arc<dyn Facet>>) -> Result<(), ChordError> {
        self.kernel.reload(facets).await
    }

    /// Dispose every facet in reverse activation order. Idempotent.
    ///
    /// # Errors
    ///
    /// Disposal failures, or a host that is reloading.
    pub async fn dispose(&self) -> Result<(), ChordError> {
        self.kernel.dispose().await
    }
}

impl fmt::Debug for FacetHost {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("FacetHost")
            .field("catalogue", &self.services.catalogue())
            .finish_non_exhaustive()
    }
}

/// Create an active host for one complete set of facets.
///
/// # Errors
///
/// Invalid facet IDs, setup failures, dependency failures, or activation
/// failures (after cleaning the generation up).
pub async fn create_facet_host(options: FacetOptions) -> Result<FacetHost, ChordError> {
    let kernel = FacetKernel::new(options)?;
    kernel.activate().await?;
    let services = kernel.provider()?;
    Ok(FacetHost { kernel, services })
}

struct StaticFacetLoader {
    facets: Vec<Arc<dyn Facet>>,
}

impl FacetLoader for StaticFacetLoader {
    fn load(&self) -> BoxFuture<'static, Result<LoadedFacets, ChordError>> {
        let loaded = LoadedFacets::new(self.facets.clone(), || {
            futures::future::ready(Ok(())).boxed()
        });
        futures::future::ready(Ok(loaded)).boxed()
    }
}

/// A loader returning the same facets every time.
#[must_use]
pub fn create_static_facet_loader(facets: Vec<Arc<dyn Facet>>) -> Arc<dyn FacetLoader> {
    Arc::new(StaticFacetLoader { facets })
}

struct CombinedFacetLoader {
    loaders: Vec<Arc<dyn FacetLoader>>,
}

impl FacetLoader for CombinedFacetLoader {
    fn load(&self) -> BoxFuture<'static, Result<LoadedFacets, ChordError>> {
        let loaders = self.loaders.clone();
        async move {
            let mut loaded: Vec<LoadedFacets> = Vec::new();
            for loader in &loaders {
                match loader.load().await {
                    Ok(generation) => loaded.push(generation),
                    Err(error) => {
                        loaded.reverse();
                        let cleanup = dispose_loaded_facets(&loaded).await;
                        if cleanup.is_empty() {
                            return Err(error);
                        }
                        let mut errors = vec![error];
                        errors.extend(cleanup);
                        return Err(AggregateError::new(
                            errors,
                            "Facet loading and cleanup failed",
                        )
                        .into());
                    }
                }
            }
            let facets = loaded
                .iter()
                .flat_map(|generation| generation.facets.clone())
                .collect();
            let disposed = Arc::new(Mutex::new(false));
            Ok(LoadedFacets::new(facets, move || {
                let first = !std::mem::replace(
                    &mut *disposed.lock().unwrap_or_else(PoisonError::into_inner),
                    true,
                );
                let reversed: Vec<LoadedFacets> = loaded.iter().rev().cloned().collect();
                async move {
                    if !first {
                        return Ok(());
                    }
                    let mut errors = dispose_loaded_facets(&reversed).await;
                    match errors.len() {
                        0 => Ok(()),
                        1 => Err(errors.remove(0)),
                        _ => Err(
                            AggregateError::new(errors, "Failed to dispose loaded facets").into(),
                        ),
                    }
                }
                .boxed()
            }))
        }
        .boxed()
    }
}

/// A loader loading each loader in order and disposing them in reverse.
#[must_use]
pub fn combine_facet_loaders(loaders: Vec<Arc<dyn FacetLoader>>) -> Arc<dyn FacetLoader> {
    Arc::new(CombinedFacetLoader { loaders })
}

fn service_token(id: &str, local: bool) -> Result<ServiceToken, ChordError> {
    if id.is_empty() {
        return Err(ChordError::type_error("Service ID must not be empty"));
    }
    if id.starts_with("$chord.") {
        return Err(ChordError::type_error(
            "Service IDs beginning with $chord. are reserved",
        ));
    }
    Ok(ServiceToken::new(id, local))
}

/// Define a remotely exposable service contract.
///
/// # Errors
///
/// An empty ID or one in the reserved `$chord.` namespace.
pub fn define_service<T>(id: &str) -> Result<Service<T>, ChordError> {
    service_token(id, false).map(Service::new)
}

/// Define a process-local service contract whose implementations are
/// values of type `T` (TS `defineService(id, { local: true })`).
///
/// # Errors
///
/// An empty ID or one in the reserved `$chord.` namespace.
pub fn define_local_service<T>(id: &str) -> Result<Service<T>, ChordError> {
    service_token(id, true).map(Service::new)
}
