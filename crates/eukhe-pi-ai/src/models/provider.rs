//! The runtime [`Provider`] value and its model-refresh context.

use std::fmt;
use std::sync::Arc;

use eukhe_chord::context::AbortSignal;
use eukhe_types::pi_ai::{AnyModel, Model, ProviderHeaders};
use futures::future::BoxFuture;

use crate::api::{
    CancelDeferredFn, ClassifyFn, FetchDeferredFn, GenerateImagesFn, StreamFn, StreamSimpleFn,
};
use crate::auth::{Credential, ProviderAuth};
use crate::models_store::ModelsStoreEntry;
use crate::utils::diagnostics::Thrown;

/// Current known chat models: TS `Provider.getModels`. Should not fail;
/// `Models` treats a failing implementation as having no models.
pub type GetModelsFn = Arc<dyn Fn() -> Result<Vec<Model>, Thrown> + Send + Sync>;

/// Current known models of every type: TS `Provider.getAllModels`.
pub type GetAllModelsFn = Arc<dyn Fn() -> Result<Vec<AnyModel>, Thrown> + Send + Sync>;

/// Dynamic providers only: restore `context.stored` and optionally fetch a
/// newer list: TS `Provider.refreshModels`.
pub type RefreshModelsFn =
    Arc<dyn Fn(RefreshModelsContext) -> BoxFuture<'static, Result<(), Thrown>> + Send + Sync>;

/// Credential-specific chat model availability: TS `Provider.filterModels`.
pub type FilterModelsFn = Arc<dyn Fn(Vec<Model>, Option<&Credential>) -> Vec<Model> + Send + Sync>;

/// Credential-specific availability across every model type: TS
/// `Provider.filterAllModels`.
pub type FilterAllModelsFn =
    Arc<dyn Fn(Vec<AnyModel>, Option<&Credential>) -> Vec<AnyModel> + Send + Sync>;

/// A provider is the concrete runtime unit. It owns id/name/base metadata,
/// auth methods, model listing, and the operations its models support
/// (streaming, image generation, classification). TS `Provider`: optional
/// methods are `Option` fields, present when the provider supports them.
#[derive(Clone)]
pub struct Provider {
    pub id: String,
    pub name: String,
    pub base_url: Option<String>,
    pub headers: Option<ProviderHeaders>,
    /// Every provider has auth semantics: even providers with only ambient
    /// credentials and keyless local servers provide api-key auth whose
    /// `resolve()` reports whether the provider is configured.
    pub auth: ProviderAuth,
    /// Current known chat models, sync. Static providers return their
    /// catalog; dynamic providers the list as of the last refresh.
    pub get_models: GetModelsFn,
    /// Current known models of every type. Absent: `Models` uses
    /// `get_models`. Model ids are unique within each type.
    pub get_all_models: Option<GetAllModelsFn>,
    /// Dynamic providers only. Implementations retain their previous list on
    /// failure, publish persistence and synchronous state changes through
    /// [`RefreshModelsContext::publish`], and honor the shared signal.
    pub refresh_models: Option<RefreshModelsFn>,
    /// `get_models` stays the complete catalog; `Models::get_available`
    /// applies this filter after confirming that provider auth is configured.
    pub filter_models: Option<FilterModelsFn>,
    /// Without it, `Models::get_all_available` applies `filter_models` to
    /// chat models and keeps every other model.
    pub filter_all_models: Option<FilterAllModelsFn>,
    /// Stream a normalized transcript. `Models` normalizes the caller's
    /// `Context` before dispatching here.
    pub stream: StreamFn,
    pub stream_simple: StreamSimpleFn,
    pub fetch_deferred: Option<FetchDeferredFn>,
    pub cancel_deferred: Option<CancelDeferredFn>,
    /// Present when the provider supports dedicated image models. Never fails.
    pub generate_images: Option<GenerateImagesFn>,
    /// Present when the provider supports classifier models. Never fails.
    pub classify: Option<ClassifyFn>,
}

impl fmt::Debug for Provider {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Provider")
            .field("id", &self.id)
            .field("name", &self.name)
            .field("base_url", &self.base_url)
            .field("headers", &self.headers)
            .field("auth", &self.auth)
            .field("refresh_models", &self.refresh_models.is_some())
            .field("fetch_deferred", &self.fetch_deferred.is_some())
            .field("cancel_deferred", &self.cancel_deferred.is_some())
            .field("generate_images", &self.generate_images.is_some())
            .field("classify", &self.classify.is_some())
            .finish_non_exhaustive()
    }
}

/// What a publication does to the persisted catalog: TS
/// `ModelsPublication.persist` (`undefined` / `null` / entry).
#[derive(Debug, Clone, Default, PartialEq)]
pub enum ModelsPersistence {
    /// Leave storage unchanged.
    #[default]
    Keep,
    /// Delete the persisted catalog.
    Delete,
    /// Write this catalog.
    Write(ModelsStoreEntry),
}

/// One generation-checked catalog publication: TS `ModelsPublication`.
#[derive(Default)]
pub struct ModelsPublication {
    /// Provider-selected persisted catalog.
    pub persist: ModelsPersistence,
    /// Optional synchronous update of provider-private in-memory catalog
    /// state; runs only after the persistence mutation.
    pub update: Option<Box<dyn FnOnce() + Send>>,
}

impl fmt::Debug for ModelsPublication {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ModelsPublication")
            .field("persist", &self.persist)
            .field("update", &self.update.is_some())
            .finish()
    }
}

/// Publishes a catalog for the refresh that created the context; resolves
/// `false` when the refresh was superseded or aborted.
pub type PublishFn =
    Arc<dyn Fn(ModelsPublication) -> BoxFuture<'static, Result<bool, Thrown>> + Send + Sync>;

/// Input of [`Provider::refresh_models`]: TS `RefreshModelsContext`.
#[derive(Clone)]
pub struct RefreshModelsContext {
    /// Effective configured credential. OAuth credentials are refreshed
    /// before network access.
    pub credential: Option<Credential>,
    /// Provider-scoped catalog snapshot captured before this refresh phase.
    pub stored: Option<ModelsStoreEntry>,
    /// Generation-checked publication (see [`RefreshModelsContext::publish`]).
    pub publisher: PublishFn,
    /// False during offline/cache-only initialization.
    pub allow_network: bool,
    /// Bypass provider freshness checks and fetch immediately when network
    /// access is allowed.
    pub force: Option<bool>,
    /// Always present, including when the public refresh caller omits its
    /// optional signal.
    pub signal: AbortSignal,
}

impl RefreshModelsContext {
    /// Generation-checked publication. Persistence policy remains
    /// provider-owned; the update runs synchronously only after the selected
    /// persistence mutation. Resolves `false` when superseded or aborted.
    ///
    /// # Errors
    ///
    /// The models-store failure, or the abort reason when the refresh signal
    /// aborts while the publication waits.
    pub async fn publish(&self, publication: ModelsPublication) -> Result<bool, Thrown> {
        (self.publisher)(publication).await
    }
}

impl fmt::Debug for RefreshModelsContext {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("RefreshModelsContext")
            .field("credential", &self.credential)
            .field("stored", &self.stored)
            .field("allow_network", &self.allow_network)
            .field("force", &self.force)
            .field("signal", &self.signal)
            .finish_non_exhaustive()
    }
}
