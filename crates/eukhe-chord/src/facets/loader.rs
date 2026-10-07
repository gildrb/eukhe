//! Loaded facet generations (port of `facets/loader.ts` and the loader
//! contracts of `types.ts`). The `node:vm` bundle loader is not ported.

use std::fmt;
use std::sync::Arc;

use futures::future::{join_all, BoxFuture};

use crate::error::ChordError;

use super::host::Facet;

type Dispose = Arc<dyn Fn() -> BoxFuture<'static, Result<(), ChordError>> + Send + Sync>;

/// One loaded generation of facets and the cleanup releasing it.
#[derive(Clone)]
pub struct LoadedFacets {
    /// The loaded facets in load order.
    pub facets: Vec<Arc<dyn Facet>>,
    dispose: Dispose,
}

impl LoadedFacets {
    /// A generation released by `dispose`.
    pub fn new<F>(facets: Vec<Arc<dyn Facet>>, dispose: F) -> Self
    where
        F: Fn() -> BoxFuture<'static, Result<(), ChordError>> + Send + Sync + 'static,
    {
        Self {
            facets,
            dispose: Arc::new(dispose),
        }
    }

    /// Release the generation.
    #[must_use]
    pub fn dispose(&self) -> BoxFuture<'static, Result<(), ChordError>> {
        (self.dispose)()
    }
}

impl fmt::Debug for LoadedFacets {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_list()
            .entries(self.facets.iter().map(|facet| facet.id()))
            .finish()
    }
}

/// Loads one generation of facets.
pub trait FacetLoader: Send + Sync {
    /// Load a generation; the caller owns its disposal.
    fn load(&self) -> BoxFuture<'static, Result<LoadedFacets, ChordError>>;
}

/// Dispose every generation concurrently and collect the failures.
pub(crate) async fn dispose_loaded_facets(loaded: &[LoadedFacets]) -> Vec<ChordError> {
    join_all(loaded.iter().map(LoadedFacets::dispose))
        .await
        .into_iter()
        .filter_map(Result::err)
        .collect()
}
