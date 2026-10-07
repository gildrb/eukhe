//! The facet lifecycle and dependency kernel behind
//! [`create_facet_host`](crate::create_facet_host) (port of
//! `facets/host.ts`).
//!
//! # Rust mapping
//!
//! - A facet is a [`Facet`] whose `setup` receives a cloneable
//!   [`FacetEnvironment`]. Setup is synchronous by signature, so the TS
//!   "setup must be synchronous" check has no runtime counterpart.
//! - Implementations are [`ServiceImplementation`]s: a typed value for
//!   process-local services or a [`RemoteServiceObject`] (required for
//!   remotely exposable services, allowed for local ones).
//! - Service handles are [`ServiceHandle`]s re-resolved on every use.

use std::any::Any;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::marker::PhantomData;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};

use futures::future::{join_all, try_join_all, BoxFuture};
use futures::FutureExt;
use indexmap::IndexMap;

use crate::callback::{settle, AsyncCallback, Closer, Disposer, Outcome};
use crate::context::{Context, BACKGROUND_CONTEXT};
use crate::error::{collected, AggregateError, BoxError, ChordError, ErrorReporter};
use crate::json::JsonValue;
use crate::services::consumer::{
    create_remote_service_binding, RemoteServiceBinding, RemoteServiceBindingOptions,
    RemoteServices, ServiceObserver,
};
use crate::services::dispatch::{RemoteServiceObject, ServiceObject};
use crate::services::handle::{AccessGuard, ServiceHandle, SlotTarget};
use crate::services::loopback::create_loopback_service_transport;
use crate::services::provider::{
    validate_remote_service_implementation, RemoteServiceProvider, ServiceProviderDefinition,
};
use crate::services::state::{replicated_state, MutableReplicatedState};
use crate::types::{Service, ServiceCatalogueEntry, ServiceMode, ServiceToken};

use super::slots::{HostServiceSlots, KeyedSource, LocalKeyedServiceRegistry};

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// One application unit: declares its service requirements and provisions
/// during a synchronous setup.
pub trait Facet: Send + Sync {
    /// The unique, non-empty facet ID.
    fn id(&self) -> &str;

    /// Declare requirements, provisions, owned resources, and lifecycle
    /// callbacks.
    ///
    /// # Errors
    ///
    /// A failure aborts the host generation (or the reload).
    fn setup(&self, env: &FacetEnvironment) -> Result<(), BoxError>;
}

struct FnFacet<F> {
    id: String,
    setup: F,
}

impl<F> Facet for FnFacet<F>
where
    F: Fn(&FacetEnvironment) -> Result<(), BoxError> + Send + Sync,
{
    fn id(&self) -> &str {
        &self.id
    }

    fn setup(&self, env: &FacetEnvironment) -> Result<(), BoxError> {
        (self.setup)(env)
    }
}

/// Define a facet from its ID and setup function (TS `defineFacet`).
pub fn define_facet<F, E>(id: &str, setup: F) -> Arc<dyn Facet>
where
    F: Fn(&FacetEnvironment) -> Result<(), E> + Send + Sync + 'static,
    E: Into<BoxError>,
{
    Arc::new(FnFacet {
        id: id.to_owned(),
        setup: move |env: &FacetEnvironment| setup(env).map_err(Into::into),
    })
}

/// A service implementation handed to [`FacetEnvironment::provide`] or a
/// [`ServiceSpawner`].
pub enum ServiceImplementation<T> {
    /// A typed process-local implementation (local services only).
    Local(T),
    /// A described implementation (required by remotely exposable services).
    Remote(Arc<dyn RemoteServiceObject>),
}

impl<T> From<ServiceObject> for ServiceImplementation<T> {
    fn from(object: ServiceObject) -> Self {
        Self::Remote(Arc::new(object))
    }
}

impl<T> From<Arc<dyn RemoteServiceObject>> for ServiceImplementation<T> {
    fn from(object: Arc<dyn RemoteServiceObject>) -> Self {
        Self::Remote(object)
    }
}

impl<T> fmt::Debug for ServiceImplementation<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Local(_) => formatter.write_str("ServiceImplementation::Local"),
            Self::Remote(_) => formatter.write_str("ServiceImplementation::Remote"),
        }
    }
}

/// A type-erased implementation.
#[derive(Clone)]
pub(super) enum Erased {
    Local(Arc<dyn Any + Send + Sync>),
    Object(Arc<dyn RemoteServiceObject>),
}

impl Erased {
    fn new<T: Send + Sync + 'static>(implementation: ServiceImplementation<T>) -> Self {
        match implementation {
            ServiceImplementation::Local(value) => Self::Local(Arc::new(value)),
            ServiceImplementation::Remote(object) => Self::Object(object),
        }
    }

    pub(super) fn target(&self) -> SlotTarget {
        match self {
            Self::Local(value) => SlotTarget::Local(Arc::clone(value)),
            Self::Object(object) => SlotTarget::Object(Arc::clone(object)),
        }
    }

    /// The remote object, or the TS "implementation must be an object"
    /// failure for a typed value.
    fn object(
        &self,
        message: impl FnOnce() -> String,
    ) -> Result<Arc<dyn RemoteServiceObject>, ChordError> {
        match self {
            Self::Object(object) => Ok(Arc::clone(object)),
            Self::Local(_) => Err(ChordError::type_error(message())),
        }
    }
}

#[derive(Clone)]
struct FacetServiceReference {
    service_id: String,
    service: ServiceToken,
    mode: ServiceMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LifecycleState {
    SettingUp,
    Prepared,
    Active,
    Disposing,
    Dead,
}

impl LifecycleState {
    fn as_str(self) -> &'static str {
        match self {
            Self::SettingUp => "setting_up",
            Self::Prepared => "prepared",
            Self::Active => "active",
            Self::Disposing => "disposing",
            Self::Dead => "dead",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GenerationPhase {
    Setup,
    Assembling,
    Connecting,
    Activating,
    Active,
    Reloading,
    Disposing,
    Dead,
}

impl GenerationPhase {
    fn as_str(self) -> &'static str {
        match self {
            Self::Setup => "setup",
            Self::Assembling => "assembling",
            Self::Connecting => "connecting",
            Self::Activating => "activating",
            Self::Active => "active",
            Self::Reloading => "reloading",
            Self::Disposing => "disposing",
            Self::Dead => "dead",
        }
    }
}

type Observation = Box<dyn FnOnce() -> Result<Disposer, ChordError> + Send>;

struct LifecycleInner {
    effects: Vec<AsyncCallback>,
    observations: Vec<Observation>,
    activate: Vec<AsyncCallback>,
    state: LifecycleState,
    service_access: bool,
}

struct FacetLifecycle {
    id: String,
    inner: Mutex<LifecycleInner>,
}

impl FacetLifecycle {
    fn new(id: &str) -> Self {
        Self {
            id: id.to_owned(),
            inner: Mutex::new(LifecycleInner {
                effects: Vec::new(),
                observations: Vec::new(),
                activate: Vec::new(),
                state: LifecycleState::SettingUp,
                service_access: false,
            }),
        }
    }

    fn assert_setting_up(&self, operation: &str) -> Result<(), ChordError> {
        if lock(&self.inner).state != LifecycleState::SettingUp {
            return Err(ChordError::error(format!(
                "Facet {} can {operation} only during setup",
                self.id
            )));
        }
        Ok(())
    }

    fn assert_running(&self, operation: &str) -> Result<(), ChordError> {
        let state = lock(&self.inner).state;
        if state != LifecycleState::SettingUp && state != LifecycleState::Active {
            return Err(ChordError::error(format!(
                "Facet {} cannot {operation} while {}",
                self.id,
                state.as_str()
            )));
        }
        Ok(())
    }

    fn assert_active(&self, operation: &str) -> Result<(), ChordError> {
        if lock(&self.inner).state != LifecycleState::Active {
            return Err(ChordError::error(format!(
                "Facet {} can {operation} only while active",
                self.id
            )));
        }
        Ok(())
    }

    fn assert_service_access(&self) -> Result<(), ChordError> {
        let inner = lock(&self.inner);
        if !inner.service_access {
            return Err(ChordError::error(format!(
                "Facet {} service handles cannot be used while {}",
                self.id,
                inner.state.as_str()
            )));
        }
        Ok(())
    }

    fn revoke(&self) {
        lock(&self.inner).service_access = false;
    }

    fn own(&self, disposal: AsyncCallback) -> Result<(), ChordError> {
        self.assert_running("own resources")?;
        lock(&self.inner).effects.push(disposal);
        Ok(())
    }

    fn observe(&self, start: Observation) -> Result<(), ChordError> {
        self.assert_setting_up("observe services")?;
        lock(&self.inner).observations.push(start);
        Ok(())
    }

    fn on_activate(&self, callback: AsyncCallback) -> Result<(), ChordError> {
        self.assert_setting_up("register activation callbacks")?;
        lock(&self.inner).activate.push(callback);
        Ok(())
    }

    fn prepared(&self) -> Result<(), ChordError> {
        self.assert_setting_up("finish setup")?;
        lock(&self.inner).state = LifecycleState::Prepared;
        Ok(())
    }

    async fn activate(&self) -> Result<(), ChordError> {
        let (observations, callbacks) = {
            let mut inner = lock(&self.inner);
            if inner.state != LifecycleState::Prepared {
                return Err(ChordError::error(format!(
                    "Facet {} is not prepared",
                    self.id
                )));
            }
            inner.state = LifecycleState::Active;
            inner.service_access = true;
            (
                std::mem::take(&mut inner.observations),
                std::mem::take(&mut inner.activate),
            )
        };
        for start in observations {
            let stop = start()?;
            lock(&self.inner).effects.push(Box::new(move || {
                stop.dispose();
                Outcome::Done
            }));
        }
        for callback in callbacks {
            settle(callback()).await?;
        }
        Ok(())
    }

    async fn dispose(&self) -> Result<(), ChordError> {
        let effects = {
            let mut inner = lock(&self.inner);
            if inner.state == LifecycleState::Dead {
                return Ok(());
            }
            inner.state = LifecycleState::Disposing;
            std::mem::take(&mut inner.effects)
        };
        let mut errors = Vec::new();
        for effect in effects.into_iter().rev() {
            if let Err(error) = settle(effect()).await {
                errors.push(error);
            }
        }
        {
            let mut inner = lock(&self.inner);
            inner.observations.clear();
            inner.activate.clear();
            inner.service_access = false;
            inner.state = LifecycleState::Dead;
        }
        collected(errors, &format!("Failed to dispose facet {}", self.id))
    }
}

type Installer = Arc<dyn Fn(&str, &Erased) -> Result<Closer, ChordError> + Send + Sync>;

struct StagedServiceInstance {
    key: String,
    implementation: Erased,
    release: Mutex<Option<Closer>>,
}

struct SpawnerInner {
    lifecycle: Arc<FacetLifecycle>,
    service: ServiceToken,
    instances: Mutex<IndexMap<String, Arc<StagedServiceInstance>>>,
    installer: Mutex<Option<Installer>>,
}

/// The deferred spawning capability returned by
/// [`FacetEnvironment::provide_many`]. Instances spawned while active stay
/// staged until the host connects them, and outlive provider reloads only
/// through their facet generation.
pub struct ServiceSpawner<T> {
    inner: Arc<SpawnerInner>,
    implementation: PhantomData<fn(T)>,
}

impl<T> Clone for ServiceSpawner<T> {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
            implementation: PhantomData,
        }
    }
}

impl SpawnerInner {
    fn connect(&self, installer: Installer) -> Result<(), ChordError> {
        let installer = {
            let mut current = lock(&self.installer);
            if current.is_some() {
                return Err(ChordError::error(
                    "Facet service provider is already connected",
                ));
            }
            Arc::clone(current.insert(installer))
        };
        let instances: Vec<Arc<StagedServiceInstance>> =
            lock(&self.instances).values().cloned().collect();
        for instance in instances {
            let release = installer(&instance.key, &instance.implementation)?;
            *lock(&instance.release) = Some(release);
        }
        Ok(())
    }

    fn validate(&self, key: &str, implementation: &Erased) -> Result<(), ChordError> {
        if key.is_empty() {
            return Err(ChordError::type_error(
                "Facet service instance key must not be empty",
            ));
        }
        if !self.service.local() {
            let object = implementation.object(|| {
                format!(
                    "Facet service {} implementation must be an object",
                    self.service.id()
                )
            })?;
            validate_remote_service_implementation(self.service.id(), &object)?;
        }
        Ok(())
    }
}

impl<T: Send + Sync + 'static> ServiceSpawner<T> {
    /// Spawn instance `key` while the facet is active. The returned closer
    /// (also owned by the facet) retires it.
    ///
    /// # Errors
    ///
    /// An inactive facet, an empty or live key, an invalid implementation,
    /// or a failure installing the instance.
    pub fn spawn(
        &self,
        key: &str,
        implementation: impl Into<ServiceImplementation<T>>,
    ) -> Result<Closer, ChordError> {
        let inner = &self.inner;
        inner.lifecycle.assert_active("spawn service instances")?;
        let implementation = Erased::new(implementation.into());
        inner.validate(key, &implementation)?;
        let instance = {
            let mut instances = lock(&inner.instances);
            if instances.contains_key(key) {
                return Err(ChordError::error(format!(
                    "Facet service already has a live instance with key {key}"
                )));
            }
            let instance = Arc::new(StagedServiceInstance {
                key: key.to_owned(),
                implementation,
                release: Mutex::new(None),
            });
            instances.insert(key.to_owned(), Arc::clone(&instance));
            instance
        };
        let installer = lock(&inner.installer).clone();
        if let Some(installer) = installer {
            let release = installer(key, &instance.implementation)?;
            *lock(&instance.release) = Some(release);
        }
        let spawner = Arc::downgrade(inner);
        let close = Closer::new(move || {
            let Some(spawner) = spawner.upgrade() else {
                return Ok(());
            };
            {
                let mut instances = lock(&spawner.instances);
                if !instances
                    .get(&instance.key)
                    .is_some_and(|current| Arc::ptr_eq(current, &instance))
                {
                    return Ok(());
                }
                instances.shift_remove(&instance.key);
            }
            let release = lock(&instance.release).clone();
            release.map_or(Ok(()), |release| release.close())
        });
        let owned = close.clone();
        inner
            .lifecycle
            .own(Box::new(move || Outcome::from(owned.close())))?;
        Ok(close)
    }
}

enum FacetProvision {
    Singleton {
        service: ServiceToken,
        implementation: Erased,
    },
    Keyed {
        service: ServiceToken,
        spawner: Arc<SpawnerInner>,
    },
}

impl FacetProvision {
    fn service(&self) -> &ServiceToken {
        match self {
            Self::Singleton { service, .. } | Self::Keyed { service, .. } => service,
        }
    }

    fn mode(&self) -> ServiceMode {
        match self {
            Self::Singleton { .. } => ServiceMode::Singleton,
            Self::Keyed { .. } => ServiceMode::Keyed,
        }
    }

    fn remote_object(
        service: &ServiceToken,
        implementation: &Erased,
    ) -> Result<Arc<dyn RemoteServiceObject>, ChordError> {
        implementation.object(|| {
            format!(
                "Remote service {} implementation must be an object",
                service.id()
            )
        })
    }

    fn install(&self, provider: &RemoteServiceProvider) -> Result<(), ChordError> {
        match self {
            Self::Singleton {
                service,
                implementation,
            } => provider.provide(service, Self::remote_object(service, implementation)?),
            Self::Keyed { .. } => Ok(()),
        }
    }

    fn validate_replacement(&self, provider: &RemoteServiceProvider) -> Result<(), ChordError> {
        match self {
            Self::Singleton {
                service,
                implementation,
            } => provider
                .validate_replacement(service, Self::remote_object(service, implementation)?),
            Self::Keyed { .. } => Ok(()),
        }
    }

    fn replace(&self, provider: &RemoteServiceProvider) -> Result<(), ChordError> {
        match self {
            Self::Singleton {
                service,
                implementation,
            } => provider.replace(service, Self::remote_object(service, implementation)?),
            Self::Keyed { .. } => Ok(()),
        }
    }

    fn connect_local(&self, registry: &LocalKeyedServiceRegistry) -> Result<(), ChordError> {
        match self {
            Self::Keyed { service, spawner } => {
                let registry = registry.clone();
                let service = service.clone();
                spawner.connect(Arc::new(move |key, implementation| {
                    registry.spawn(&service, key, implementation)
                }))
            }
            Self::Singleton { .. } => Ok(()),
        }
    }

    fn connect_remote(&self, provider: &RemoteServiceProvider) -> Result<(), ChordError> {
        match self {
            Self::Keyed { service, spawner } => {
                let provider = provider.clone();
                let service = service.clone();
                spawner.connect(Arc::new(move |key, implementation| {
                    provider.spawn(
                        &service,
                        key,
                        Self::remote_object(&service, implementation)?,
                    )
                }))
            }
            Self::Singleton { .. } => Ok(()),
        }
    }
}

struct FacetRuntime {
    facet_id: String,
    requires: Mutex<Vec<FacetServiceReference>>,
    provides: Mutex<Vec<FacetServiceReference>>,
    lifecycle: Arc<FacetLifecycle>,
    provisions: Mutex<Vec<Arc<FacetProvision>>>,
    singleton_views: Mutex<HashMap<String, ServiceHandle>>,
}

impl FacetRuntime {
    fn new(facet_id: &str) -> Arc<Self> {
        Arc::new(Self {
            facet_id: facet_id.to_owned(),
            requires: Mutex::new(Vec::new()),
            provides: Mutex::new(Vec::new()),
            lifecycle: Arc::new(FacetLifecycle::new(facet_id)),
            provisions: Mutex::new(Vec::new()),
            singleton_views: Mutex::new(HashMap::new()),
        })
    }
}

/// A facet's setup environment. Clones share one facet generation; the
/// environment stays usable for `own`, `replicated_state`, and spawning
/// after setup, as in TS.
#[derive(Clone)]
pub struct FacetEnvironment {
    kernel: Weak<KernelInner>,
    runtime: Arc<FacetRuntime>,
}

impl FacetEnvironment {
    fn kernel(&self) -> Result<Arc<KernelInner>, ChordError> {
        self.kernel
            .upgrade()
            .ok_or_else(|| ChordError::error("Facet host is disposed"))
    }

    fn access_guard(&self) -> AccessGuard {
        let lifecycle = Arc::clone(&self.runtime.lifecycle);
        Arc::new(move || lifecycle.assert_service_access())
    }

    /// Declare a hard dependency on one singleton service and return its
    /// stable handle.
    ///
    /// # Errors
    ///
    /// Called after setup.
    pub fn use_service<T>(&self, service: &Service<T>) -> Result<ServiceHandle, ChordError> {
        let runtime = &self.runtime;
        runtime.lifecycle.assert_setting_up("acquire services")?;
        record_service_reference(&runtime.requires, service.token(), ServiceMode::Singleton);
        let kernel = self.kernel()?;
        let mut views = lock(&runtime.singleton_views);
        if let Some(view) = views.get(service.id()) {
            return Ok(view.clone());
        }
        let view = kernel
            .slots
            .get_singleton(service.token(), self.access_guard());
        views.insert(service.id().to_owned(), view.clone());
        Ok(view)
    }

    /// Declare a hard dependency on a keyed service and observe each live
    /// instance once this facet activates.
    ///
    /// # Errors
    ///
    /// Called after setup.
    pub fn observe<T>(
        &self,
        service: &Service<T>,
        handler: ServiceObserver,
    ) -> Result<(), ChordError> {
        let runtime = &self.runtime;
        runtime.lifecycle.assert_setting_up("observe services")?;
        record_service_reference(&runtime.requires, service.token(), ServiceMode::Keyed);
        let kernel = Arc::downgrade(&self.kernel()?);
        let token = service.token().clone();
        let guard = self.access_guard();
        runtime.lifecycle.observe(Box::new(move || {
            let kernel = kernel.upgrade().ok_or_else(|| {
                ChordError::error(format!("Service {} is disconnected", token.id()))
            })?;
            kernel.slots.observe(&token, guard, handler)
        }))
    }

    /// Declare and install this facet's singleton implementation of a
    /// service.
    ///
    /// # Errors
    ///
    /// Called after setup, or a typed implementation for a remotely
    /// exposable service.
    pub fn provide<T: Send + Sync + 'static>(
        &self,
        service: &Service<T>,
        implementation: impl Into<ServiceImplementation<T>>,
    ) -> Result<(), ChordError> {
        let runtime = &self.runtime;
        runtime.lifecycle.assert_setting_up("provide services")?;
        let implementation = Erased::new(implementation.into());
        if !service.local() && matches!(implementation, Erased::Local(_)) {
            return Err(ChordError::type_error(format!(
                "Service {} implementation must be an object",
                service.id()
            )));
        }
        record_service_reference(&runtime.provides, service.token(), ServiceMode::Singleton);
        lock(&runtime.provisions).push(Arc::new(FacetProvision::Singleton {
            service: service.token().clone(),
            implementation,
        }));
        Ok(())
    }

    /// Declare ownership of a multi-instance service and return its deferred
    /// spawning capability.
    ///
    /// # Errors
    ///
    /// Called after setup.
    pub fn provide_many<T>(&self, service: &Service<T>) -> Result<ServiceSpawner<T>, ChordError> {
        let runtime = &self.runtime;
        runtime
            .lifecycle
            .assert_setting_up("provide service instances")?;
        record_service_reference(&runtime.provides, service.token(), ServiceMode::Keyed);
        let spawner = Arc::new(SpawnerInner {
            lifecycle: Arc::clone(&runtime.lifecycle),
            service: service.token().clone(),
            instances: Mutex::new(IndexMap::new()),
            installer: Mutex::new(None),
        });
        lock(&runtime.provisions).push(Arc::new(FacetProvision::Keyed {
            service: service.token().clone(),
            spawner: Arc::clone(&spawner),
        }));
        Ok(ServiceSpawner {
            inner: spawner,
            implementation: PhantomData,
        })
    }

    /// Create initialized mutable state by taking immutable ownership of a
    /// JSON object or array root.
    ///
    /// # Errors
    ///
    /// A disposed facet or a non-container root.
    pub fn replicated_state(
        &self,
        initial: JsonValue,
    ) -> Result<MutableReplicatedState, ChordError> {
        self.runtime
            .lifecycle
            .assert_running("create replicated state")?;
        replicated_state(initial)
    }

    /// Give the facet ownership of a resource cleanup function, run in
    /// reverse registration order at disposal.
    ///
    /// # Errors
    ///
    /// A facet that is neither setting up nor active.
    pub fn own<F, R>(&self, disposal: F) -> Result<(), ChordError>
    where
        F: FnOnce() -> R + Send + 'static,
        R: Into<Outcome>,
    {
        self.runtime
            .lifecycle
            .own(Box::new(move || disposal().into()))
    }

    /// Own a disposer (for example a state subscription).
    ///
    /// # Errors
    ///
    /// See [`own`](Self::own).
    pub fn own_disposer(&self, disposer: Disposer) -> Result<(), ChordError> {
        self.own(move || disposer.dispose())
    }

    /// Register asynchronous initialization after dependencies are bound and
    /// ready.
    ///
    /// # Errors
    ///
    /// Called after setup.
    pub fn on_activate<F, R>(&self, callback: F) -> Result<(), ChordError>
    where
        F: FnOnce() -> R + Send + 'static,
        R: Into<Outcome>,
    {
        self.runtime
            .lifecycle
            .on_activate(Box::new(move || callback().into()))
    }

    /// Register final facet teardown.
    ///
    /// # Errors
    ///
    /// See [`own`](Self::own).
    pub fn on_deactivate<F, R>(&self, callback: F) -> Result<(), ChordError>
    where
        F: FnOnce() -> R + Send + 'static,
        R: Into<Outcome>,
    {
        self.own(callback)
    }
}

fn record_service_reference(
    target: &Mutex<Vec<FacetServiceReference>>,
    service: &ServiceToken,
    mode: ServiceMode,
) {
    let mut target = lock(target);
    if target
        .iter()
        .any(|reference| reference.service_id == service.id() && reference.mode == mode)
    {
        return;
    }
    target.push(FacetServiceReference {
        service_id: service.id().to_owned(),
        service: service.clone(),
        mode,
    });
}

/// Options for [`create_facet_host`](crate::create_facet_host).
#[derive(Clone, Default)]
pub struct FacetOptions {
    /// One complete set of facets.
    pub facets: Vec<Arc<dyn Facet>>,
    /// External service sources.
    pub service_sources: Vec<Arc<dyn RemoteServiceSource>>,
    /// Receives background failures; ignored when `None`.
    pub on_error: Option<ErrorReporter>,
}

/// What a [`RemoteServiceSource`] receives when the host opens it.
#[derive(Clone)]
pub struct RemoteServiceSourceOpenOptions {
    /// The service IDs this host takes from the source.
    pub services: Vec<String>,
    /// Guards every handle operation.
    pub assert_access: AccessGuard,
    /// Receives background failures.
    pub on_error: ErrorReporter,
}

/// An external provider of remote services for a facet host.
pub trait RemoteServiceSource: Send + Sync {
    /// Whether this currently unavailable source may provisionally own
    /// absent requirements.
    fn accepts_unavailable_services(&self) -> bool;

    /// The services the source offers.
    fn catalogue(
        &self,
        context: &Context,
    ) -> BoxFuture<'static, Result<Vec<ServiceCatalogueEntry>, ChordError>>;

    /// Open the services this host takes from the source.
    ///
    /// # Errors
    ///
    /// A failure aborts the host generation.
    fn open(
        &self,
        options: RemoteServiceSourceOpenOptions,
    ) -> Result<Arc<dyn RemoteServices>, ChordError>;
}

struct ExternalService {
    service: ServiceToken,
    mode: ServiceMode,
    source: Arc<dyn RemoteServiceSource>,
}

fn same_source(left: &Arc<dyn RemoteServiceSource>, right: &Arc<dyn RemoteServiceSource>) -> bool {
    std::ptr::addr_eq(Arc::as_ptr(left), Arc::as_ptr(right))
}

struct KernelState {
    facets: IndexMap<String, Arc<FacetRuntime>>,
    source_bindings: Vec<(Arc<dyn RemoteServiceSource>, Arc<dyn RemoteServices>)>,
    activation_order: Vec<String>,
    provider: Option<RemoteServiceProvider>,
    internal_services: Option<RemoteServiceBinding>,
    local_keyed_services: Option<LocalKeyedServiceRegistry>,
    phase: GenerationPhase,
}

struct KernelInner {
    initial_facets: Vec<Arc<dyn Facet>>,
    service_sources: Vec<Arc<dyn RemoteServiceSource>>,
    on_error: ErrorReporter,
    slots: HostServiceSlots,
    state: Mutex<KernelState>,
}

/// Private lifecycle and dependency kernel behind the atomic host entry
/// point.
#[derive(Clone)]
pub(crate) struct FacetKernel {
    inner: Arc<KernelInner>,
}

fn validate_ids<'a>(ids: impl Iterator<Item = &'a str>, duplicate: &str) -> Result<(), ChordError> {
    let mut seen = HashSet::new();
    let mut empty = false;
    let mut duplicated = false;
    for id in ids {
        empty |= id.is_empty();
        duplicated |= !seen.insert(id);
    }
    if empty {
        return Err(ChordError::error("Facet ID must not be empty"));
    }
    if duplicated {
        return Err(ChordError::error(duplicate.to_owned()));
    }
    Ok(())
}

impl FacetKernel {
    pub(crate) fn new(options: FacetOptions) -> Result<Self, ChordError> {
        validate_ids(
            options.facets.iter().map(|facet| facet.id()),
            "Facet IDs must be unique within a generation",
        )?;
        Ok(Self {
            inner: Arc::new(KernelInner {
                initial_facets: options.facets,
                service_sources: options.service_sources,
                on_error: options.on_error.unwrap_or_else(|| Arc::new(|_| {})),
                slots: HostServiceSlots::default(),
                state: Mutex::new(KernelState {
                    facets: IndexMap::new(),
                    source_bindings: Vec::new(),
                    activation_order: Vec::new(),
                    provider: None,
                    internal_services: None,
                    local_keyed_services: None,
                    phase: GenerationPhase::Setup,
                }),
            }),
        })
    }

    pub(crate) fn provider(&self) -> Result<RemoteServiceProvider, ChordError> {
        lock(&self.inner.state)
            .provider
            .clone()
            .ok_or_else(|| ChordError::error("Facet service provider is not assembled"))
    }

    fn set_phase(&self, phase: GenerationPhase) {
        lock(&self.inner.state).phase = phase;
    }

    fn setup_facet(
        &self,
        facet: &dyn Facet,
        runtime: &Arc<FacetRuntime>,
    ) -> Result<(), ChordError> {
        let env = FacetEnvironment {
            kernel: Arc::downgrade(&self.inner),
            runtime: Arc::clone(runtime),
        };
        facet.setup(&env).map_err(ChordError::from)?;
        runtime.lifecycle.prepared()
    }

    pub(crate) async fn activate(&self) -> Result<(), ChordError> {
        let result = self.activate_steps().await;
        if let Err(error) = result {
            let cleanup = self.terminate(&[]).await;
            if !cleanup.is_empty() {
                let mut errors = vec![error];
                errors.extend(cleanup);
                return Err(AggregateError::new(
                    errors,
                    "Facet generation startup and cleanup failed",
                )
                .into());
            }
            return Err(error);
        }
        Ok(())
    }

    async fn activate_steps(&self) -> Result<(), ChordError> {
        let mut records = Vec::new();
        for facet in &self.inner.initial_facets {
            let runtime = FacetRuntime::new(facet.id());
            lock(&self.inner.state)
                .facets
                .insert(facet.id().to_owned(), Arc::clone(&runtime));
            self.setup_facet(facet.as_ref(), &runtime)?;
            records.push(runtime);
        }

        self.set_phase(GenerationPhase::Assembling);
        let external = self.resolve_external_services(&records).await?;
        let order = validate_facets(&records, &external)?;
        lock(&self.inner.state).activation_order.clone_from(&order);
        self.assemble_providers()?;
        self.bind_services(&external)?;

        self.set_phase(GenerationPhase::Connecting);
        let readiness: Vec<BoxFuture<'static, Result<(), ChordError>>> = {
            let state = lock(&self.inner.state);
            let mut readiness: Vec<BoxFuture<'static, Result<(), ChordError>>> = state
                .source_bindings
                .iter()
                .map(|(_, services)| services.ready(&BACKGROUND_CONTEXT))
                .collect();
            let internal = state
                .internal_services
                .clone()
                .ok_or_else(|| ChordError::error("Facet remote services are not assembled"))?;
            readiness.push(internal.ready(&BACKGROUND_CONTEXT).boxed());
            readiness
        };
        try_join_all(readiness).await?;

        self.set_phase(GenerationPhase::Activating);
        for id in &order {
            let runtime = lock(&self.inner.state).facets.get(id).cloned();
            if let Some(runtime) = runtime {
                runtime.lifecycle.activate().await?;
            }
        }
        self.set_phase(GenerationPhase::Active);
        Ok(())
    }

    pub(crate) async fn reload(&self, facets: Vec<Arc<dyn Facet>>) -> Result<(), ChordError> {
        {
            let state = lock(&self.inner.state);
            if state.phase != GenerationPhase::Active {
                return Err(ChordError::error(format!(
                    "Facet host cannot reload while {}",
                    state.phase.as_str()
                )));
            }
        }
        validate_ids(
            facets.iter().map(|facet| facet.id()),
            "Reloaded facet IDs must be unique",
        )?;
        {
            let mut state = lock(&self.inner.state);
            if let Some(missing) = facets
                .iter()
                .find(|facet| !state.facets.contains_key(facet.id()))
            {
                return Err(ChordError::error(format!(
                    "Facet {} is not active",
                    missing.id()
                )));
            }
            state.phase = GenerationPhase::Reloading;
        }

        let mut staged = Vec::new();
        let mut candidates = Vec::new();
        let setup = self.setup_candidates(&facets, &mut staged, &mut candidates);
        if let Err(error) = setup {
            staged.reverse();
            return Err(self
                .roll_back(error, &staged, "Facet reload setup and cleanup failed")
                .await);
        }

        let candidate_order: Vec<Arc<FacetRuntime>> = {
            let state = lock(&self.inner.state);
            state
                .activation_order
                .iter()
                .filter_map(|id| {
                    candidates
                        .iter()
                        .find(|candidate| &candidate.facet_id == id)
                        .cloned()
                })
                .collect()
        };
        let activation = async {
            for candidate in &candidate_order {
                candidate.lifecycle.activate().await?;
            }
            for candidate in &candidate_order {
                self.validate_replacement_provisions(&lock(&candidate.provisions))?;
            }
            Ok::<(), ChordError>(())
        }
        .await;
        if let Err(error) = activation {
            let reversed: Vec<Arc<FacetRuntime>> = candidate_order.iter().rev().cloned().collect();
            return Err(self
                .roll_back(
                    error,
                    &reversed,
                    "Facet reload activation and cleanup failed",
                )
                .await);
        }

        let previous: Vec<Arc<FacetRuntime>> = {
            let mut state = lock(&self.inner.state);
            let previous = candidate_order
                .iter()
                .filter_map(|candidate| state.facets.get(&candidate.facet_id).cloned())
                .collect();
            for candidate in &candidate_order {
                state
                    .facets
                    .insert(candidate.facet_id.clone(), Arc::clone(candidate));
            }
            previous
        };
        let cutover = self.cut_over(&candidate_order, &previous).await;
        if let Err(error) = cutover {
            let abort = self.abort(&previous).await;
            let mut errors = vec![error];
            errors.extend(abort);
            return Err(AggregateError::new(errors, "Facet reload failed after cutover").into());
        }
        self.set_phase(GenerationPhase::Active);
        Ok(())
    }

    /// Dispose rejected candidates while the previous generation stays
    /// active; a cleanup failure terminates the host instead.
    async fn roll_back(
        &self,
        error: ChordError,
        records: &[Arc<FacetRuntime>],
        message: &str,
    ) -> ChordError {
        let cleanup = dispose_facet_records(records).await;
        if cleanup.is_empty() {
            self.set_phase(GenerationPhase::Active);
            return error;
        }
        let abort = self.abort(&[]).await;
        let mut errors = vec![error];
        errors.extend(cleanup);
        errors.extend(abort);
        AggregateError::new(errors, message).into()
    }

    /// Set up each reloaded facet and check it can replace its predecessor.
    fn setup_candidates(
        &self,
        facets: &[Arc<dyn Facet>],
        staged: &mut Vec<Arc<FacetRuntime>>,
        candidates: &mut Vec<Arc<FacetRuntime>>,
    ) -> Result<(), ChordError> {
        for facet in facets {
            let runtime = FacetRuntime::new(facet.id());
            staged.push(Arc::clone(&runtime));
            self.setup_facet(facet.as_ref(), &runtime)?;
            let previous = lock(&self.inner.state).facets.get(facet.id()).cloned();
            if let Some(previous) = previous {
                if !same_facet_shape(&previous, &runtime) {
                    return Err(ChordError::error(format!(
                        "Reloaded facet {} must preserve its service requirements and provisions",
                        facet.id()
                    )));
                }
            }
            self.validate_replacement_provisions(&lock(&runtime.provisions))?;
            candidates.push(runtime);
        }
        Ok(())
    }

    /// Route singletons to the candidates, retire the replaced records, then
    /// connect the candidates' keyed provisions.
    async fn cut_over(
        &self,
        candidate_order: &[Arc<FacetRuntime>],
        previous: &[Arc<FacetRuntime>],
    ) -> Result<(), ChordError> {
        for candidate in candidate_order {
            let provisions: Vec<Arc<FacetProvision>> = lock(&candidate.provisions).clone();
            for provision in provisions {
                let FacetProvision::Singleton {
                    service,
                    implementation,
                } = provision.as_ref()
                else {
                    continue;
                };
                if service.local() {
                    self.inner
                        .slots
                        .bind_singleton(service.id(), implementation.target());
                } else {
                    provision.replace(&self.provider()?)?;
                }
            }
        }
        let reversed: Vec<Arc<FacetRuntime>> = previous.iter().rev().cloned().collect();
        let mut retirement = dispose_facet_records(&reversed).await;
        match retirement.len() {
            0 => {}
            1 => return Err(retirement.remove(0)),
            _ => {
                return Err(
                    AggregateError::new(retirement, "Failed to retire replaced facets").into(),
                )
            }
        }
        for candidate in candidate_order {
            let provisions: Vec<Arc<FacetProvision>> = lock(&candidate.provisions).clone();
            for provision in provisions {
                if !matches!(provision.as_ref(), FacetProvision::Keyed { .. }) {
                    continue;
                }
                if provision.service().local() {
                    provision.connect_local(&self.local_keyed_registry()?)?;
                } else {
                    provision.connect_remote(&self.provider()?)?;
                }
            }
        }
        Ok(())
    }

    pub(crate) async fn dispose(&self) -> Result<(), ChordError> {
        {
            let state = lock(&self.inner.state);
            if state.phase == GenerationPhase::Dead {
                return Ok(());
            }
            if state.phase != GenerationPhase::Active {
                return Err(ChordError::error(format!(
                    "Facet host cannot be disposed while {}",
                    state.phase.as_str()
                )));
            }
        }
        let errors = self.terminate(&[]).await;
        collected(errors, "Failed to dispose facet generation")
    }

    fn validate_replacement_provisions(
        &self,
        provisions: &[Arc<FacetProvision>],
    ) -> Result<(), ChordError> {
        for provision in provisions {
            if matches!(provision.as_ref(), FacetProvision::Singleton { .. })
                && !provision.service().local()
            {
                provision.validate_replacement(&self.provider()?)?;
            }
        }
        Ok(())
    }

    async fn resolve_external_services(
        &self,
        records: &[Arc<FacetRuntime>],
    ) -> Result<IndexMap<String, ExternalService>, ChordError> {
        let catalogues = try_join_all(self.inner.service_sources.iter().map(|source| {
            let source = Arc::clone(source);
            let catalogue = source.catalogue(&BACKGROUND_CONTEXT);
            async move { catalogue.await.map(|entries| (source, entries)) }
        }))
        .await?;
        let mut offered: HashMap<String, (ServiceMode, Arc<dyn RemoteServiceSource>)> =
            HashMap::new();
        for (source, entries) in catalogues {
            for entry in entries {
                if offered.contains_key(&entry.service_id) {
                    return Err(ChordError::error(format!(
                        "Facet host service {} is offered by more than one source",
                        entry.service_id
                    )));
                }
                offered.insert(entry.service_id, (entry.mode, Arc::clone(&source)));
            }
        }

        let local: HashSet<String> = records
            .iter()
            .flat_map(|record| {
                lock(&record.provides)
                    .iter()
                    .map(|reference| reference.service_id.clone())
                    .collect::<Vec<_>>()
            })
            .collect();
        let mut external: IndexMap<String, ExternalService> = IndexMap::new();
        for record in records {
            let requires = lock(&record.requires).clone();
            for requirement in requires {
                if local.contains(&requirement.service_id)
                    || external.contains_key(&requirement.service_id)
                {
                    continue;
                }
                let mut source = offered.get(&requirement.service_id).cloned();
                if source.is_none() {
                    let deferred: Vec<&Arc<dyn RemoteServiceSource>> = self
                        .inner
                        .service_sources
                        .iter()
                        .filter(|source| source.accepts_unavailable_services())
                        .collect();
                    if deferred.len() > 1 {
                        return Err(ChordError::error(format!(
                            "Facet host service {} has more than one deferred source",
                            requirement.service_id
                        )));
                    }
                    if let Some(deferred) = deferred.first() {
                        source = Some((requirement.mode, Arc::clone(deferred)));
                    }
                }
                if let Some((mode, source)) = source {
                    external.insert(
                        requirement.service_id.clone(),
                        ExternalService {
                            service: requirement.service.clone(),
                            mode,
                            source,
                        },
                    );
                }
            }
        }
        let mut by_source: Vec<(Arc<dyn RemoteServiceSource>, Vec<String>)> = Vec::new();
        for (service_id, service) in &external {
            match by_source
                .iter_mut()
                .find(|(source, _)| same_source(source, &service.source))
            {
                Some((_, ids)) => ids.push(service_id.clone()),
                None => by_source.push((Arc::clone(&service.source), vec![service_id.clone()])),
            }
        }
        for (source, services) in by_source {
            let opened = source.open(RemoteServiceSourceOpenOptions {
                services,
                assert_access: self.target_access(),
                on_error: Arc::clone(&self.inner.on_error),
            })?;
            lock(&self.inner.state)
                .source_bindings
                .push((source, opened));
        }
        Ok(external)
    }

    fn target_access(&self) -> AccessGuard {
        let kernel = Arc::downgrade(&self.inner);
        Arc::new(move || {
            let Some(kernel) = kernel.upgrade() else {
                return Err(ChordError::error(
                    "Facet service targets cannot be used during dead",
                ));
            };
            let phase = lock(&kernel.state).phase;
            match phase {
                GenerationPhase::Activating
                | GenerationPhase::Active
                | GenerationPhase::Reloading
                | GenerationPhase::Disposing => Ok(()),
                GenerationPhase::Setup
                | GenerationPhase::Assembling
                | GenerationPhase::Connecting
                | GenerationPhase::Dead => Err(ChordError::error(format!(
                    "Facet service targets cannot be used during {}",
                    phase.as_str()
                ))),
            }
        })
    }

    fn provisions(&self) -> Vec<Arc<FacetProvision>> {
        let facets: Vec<Arc<FacetRuntime>> =
            lock(&self.inner.state).facets.values().cloned().collect();
        facets
            .iter()
            .flat_map(|facet| lock(&facet.provisions).clone())
            .collect()
    }

    fn assemble_providers(&self) -> Result<(), ChordError> {
        let provisions = self.provisions();
        let remote: Vec<&Arc<FacetProvision>> = provisions
            .iter()
            .filter(|provision| !provision.service().local())
            .collect();
        let provider =
            RemoteServiceProvider::new(remote.iter().map(|provision| ServiceProviderDefinition {
                service: provision.service().clone(),
                mode: provision.mode(),
            }))?;
        let mut binding_options = RemoteServiceBindingOptions::new(
            remote
                .iter()
                .map(|provision| provision.service().id().to_owned())
                .collect(),
            create_loopback_service_transport(provider.clone()),
        );
        binding_options.assert_access = Some(self.target_access());
        binding_options.on_error = Some(Arc::clone(&self.inner.on_error));
        let internal = create_remote_service_binding(binding_options)?;
        let local_keyed: Vec<ServiceToken> = provisions
            .iter()
            .filter(|provision| {
                matches!(provision.as_ref(), FacetProvision::Keyed { .. })
                    && provision.service().local()
            })
            .map(|provision| provision.service().clone())
            .collect();
        let registry = LocalKeyedServiceRegistry::new(&local_keyed, &self.inner.on_error)?;
        {
            let mut state = lock(&self.inner.state);
            state.provider = Some(provider.clone());
            state.internal_services = Some(internal);
            state.local_keyed_services = Some(registry.clone());
        }
        for provision in &provisions {
            match provision.as_ref() {
                FacetProvision::Singleton { service, .. } => {
                    if !service.local() {
                        provision.install(&provider)?;
                    }
                }
                FacetProvision::Keyed { service, .. } => {
                    if service.local() {
                        provision.connect_local(&registry)?;
                    } else {
                        provision.connect_remote(&provider)?;
                    }
                }
            }
        }
        Ok(())
    }

    fn bind_services(
        &self,
        external: &IndexMap<String, ExternalService>,
    ) -> Result<(), ChordError> {
        for provision in self.provisions() {
            match provision.as_ref() {
                FacetProvision::Singleton {
                    service,
                    implementation,
                } => {
                    if !self.inner.slots.has_singleton(service.id()) {
                        continue;
                    }
                    let target = if service.local() {
                        implementation.target()
                    } else {
                        self.internal_services()?
                            .use_service(service)?
                            .into_target()
                    };
                    self.inner.slots.bind_singleton(service.id(), target);
                }
                FacetProvision::Keyed { service, .. } => {
                    let source = if service.local() {
                        KeyedSource::Local(self.local_keyed_registry()?)
                    } else {
                        KeyedSource::Remote(Arc::new(self.internal_services()?))
                    };
                    self.inner.slots.bind_keyed(service.id(), source);
                }
            }
        }
        for (service_id, external_service) in external {
            let services = lock(&self.inner.state)
                .source_bindings
                .iter()
                .find(|(source, _)| same_source(source, &external_service.source))
                .map(|(_, services)| Arc::clone(services))
                .ok_or_else(|| {
                    ChordError::error(format!("Service source for {service_id} is not open"))
                })?;
            match external_service.mode {
                ServiceMode::Singleton => {
                    let target = services
                        .use_service(&external_service.service)?
                        .into_target();
                    self.inner.slots.bind_singleton(service_id, target);
                }
                ServiceMode::Keyed => self
                    .inner
                    .slots
                    .bind_keyed(service_id, KeyedSource::Remote(services)),
            }
        }
        Ok(())
    }

    fn local_keyed_registry(&self) -> Result<LocalKeyedServiceRegistry, ChordError> {
        lock(&self.inner.state)
            .local_keyed_services
            .clone()
            .ok_or_else(|| ChordError::error("Facet keyed services are not assembled"))
    }

    fn internal_services(&self) -> Result<RemoteServiceBinding, ChordError> {
        lock(&self.inner.state)
            .internal_services
            .clone()
            .ok_or_else(|| ChordError::error("Facet remote services are not assembled"))
    }

    async fn dispose_service_bindings(&self) -> Vec<ChordError> {
        let bindings: Vec<Arc<dyn RemoteServices>> = {
            let mut state = lock(&self.inner.state);
            let mut bindings: Vec<Arc<dyn RemoteServices>> = state
                .source_bindings
                .drain(..)
                .map(|(_, services)| services)
                .collect();
            if let Some(internal) = state.internal_services.take() {
                bindings.push(Arc::new(internal));
            }
            bindings
        };
        join_all(
            bindings
                .iter()
                .map(|services| services.dispose(&BACKGROUND_CONTEXT)),
        )
        .await
        .into_iter()
        .filter_map(Result::err)
        .collect()
    }

    async fn abort(&self, extra: &[Arc<FacetRuntime>]) -> Vec<ChordError> {
        let facets: Vec<Arc<FacetRuntime>> =
            lock(&self.inner.state).facets.values().cloned().collect();
        for record in facets.iter().chain(extra) {
            record.lifecycle.revoke();
        }
        self.terminate(extra).await
    }

    async fn terminate(&self, extra: &[Arc<FacetRuntime>]) -> Vec<ChordError> {
        self.set_phase(GenerationPhase::Disposing);
        let mut errors = self.dispose_lifecycles().await;
        let reversed: Vec<Arc<FacetRuntime>> = extra.iter().rev().cloned().collect();
        errors.extend(dispose_facet_records(&reversed).await);
        let registry = lock(&self.inner.state).local_keyed_services.take();
        if let Some(registry) = registry {
            registry.dispose();
        }
        errors.extend(self.dispose_service_bindings().await);
        self.inner.slots.dispose();
        let provider = lock(&self.inner.state).provider.clone();
        if let Some(provider) = provider {
            if let Err(error) = provider.dispose() {
                errors.push(error);
            }
        }
        self.set_phase(GenerationPhase::Dead);
        errors
    }

    async fn dispose_lifecycles(&self) -> Vec<ChordError> {
        let order: Vec<String> = {
            let state = lock(&self.inner.state);
            if state.activation_order.is_empty() {
                state.facets.keys().rev().cloned().collect()
            } else {
                state.activation_order.iter().rev().cloned().collect()
            }
        };
        let mut errors = Vec::new();
        for id in order {
            let record = lock(&self.inner.state).facets.shift_remove(&id);
            let Some(record) = record else {
                continue;
            };
            if let Err(error) = record.lifecycle.dispose().await {
                errors.push(error);
            }
        }
        errors
    }
}

async fn dispose_facet_records(records: &[Arc<FacetRuntime>]) -> Vec<ChordError> {
    let mut errors = Vec::new();
    for record in records {
        if let Err(error) = record.lifecycle.dispose().await {
            errors.push(error);
        }
    }
    errors
}

struct Provider {
    facet_id: Option<String>,
    mode: Option<ServiceMode>,
}

fn validate_facets(
    records: &[Arc<FacetRuntime>],
    external: &IndexMap<String, ExternalService>,
) -> Result<Vec<String>, ChordError> {
    let mut providers: HashMap<String, Provider> = external
        .iter()
        .map(|(service_id, service)| {
            (
                service_id.clone(),
                Provider {
                    facet_id: None,
                    mode: Some(service.mode),
                },
            )
        })
        .collect();
    for record in records {
        for provision in lock(&record.provides).iter() {
            if let Some(existing) = providers.get(&provision.service_id) {
                if existing.mode.is_some_and(|mode| mode != provision.mode) {
                    return Err(ChordError::error(format!(
                        "Service {} is provided as both singleton and keyed",
                        provision.service_id
                    )));
                }
                return Err(ChordError::error(match &existing.facet_id {
                    None => format!(
                        "Service {} is provided by both the host and {}",
                        provision.service_id, record.facet_id
                    ),
                    Some(facet_id) => format!(
                        "Service {} is provided by both {facet_id} and {}",
                        provision.service_id, record.facet_id
                    ),
                }));
            }
            providers.insert(
                provision.service_id.clone(),
                Provider {
                    facet_id: Some(record.facet_id.clone()),
                    mode: Some(provision.mode),
                },
            );
        }
    }

    let mut dependencies: IndexMap<String, IndexMap<String, ()>> = records
        .iter()
        .map(|record| (record.facet_id.clone(), IndexMap::new()))
        .collect();
    let mut dependents: IndexMap<String, IndexMap<String, ()>> = dependencies.clone();
    for record in records {
        for requirement in lock(&record.requires).iter() {
            let Some(provider) = providers.get(&requirement.service_id) else {
                return Err(ChordError::error(format!(
                    "Facet {} requires local/{}/{}, but no facet provides it",
                    record.facet_id, requirement.service_id, requirement.mode
                )));
            };
            if let Some(mode) = provider.mode.filter(|mode| *mode != requirement.mode) {
                return Err(ChordError::error(format!(
                    "Facet {} requires {} as {}, but {} provides it as {mode}",
                    record.facet_id,
                    requirement.service_id,
                    requirement.mode,
                    provider.facet_id.as_deref().unwrap_or("the host")
                )));
            }
            let Some(provider_id) = provider
                .facet_id
                .as_ref()
                .filter(|id| **id != record.facet_id)
            else {
                continue;
            };
            if let Some(set) = dependencies.get_mut(&record.facet_id) {
                set.insert(provider_id.clone(), ());
            }
            if let Some(set) = dependents.get_mut(provider_id) {
                set.insert(record.facet_id.clone(), ());
            }
        }
    }
    topological_order(records, &dependencies, &dependents)
}

fn topological_order(
    records: &[Arc<FacetRuntime>],
    dependencies: &IndexMap<String, IndexMap<String, ()>>,
    dependents: &IndexMap<String, IndexMap<String, ()>>,
) -> Result<Vec<String>, ChordError> {
    let mut remaining: HashMap<&str, usize> = dependencies
        .iter()
        .map(|(id, values)| (id.as_str(), values.len()))
        .collect();
    let mut ready: VecDeque<&str> = records
        .iter()
        .map(|record| record.facet_id.as_str())
        .filter(|id| remaining.get(id) == Some(&0))
        .collect();
    let mut order = Vec::new();
    while let Some(id) = ready.pop_front() {
        order.push(id.to_owned());
        if let Some(followers) = dependents.get(id) {
            for dependent in followers.keys() {
                if let Some(count) = remaining.get_mut(dependent.as_str()) {
                    *count -= 1;
                    if *count == 0 {
                        ready.push_back(dependent.as_str());
                    }
                }
            }
        }
    }
    if order.len() != records.len() {
        let cycle: Vec<&str> = records
            .iter()
            .map(|record| record.facet_id.as_str())
            .filter(|id| remaining.get(id).is_some_and(|count| *count > 0))
            .collect();
        return Err(ChordError::error(format!(
            "Facet dependency cycle: {}",
            cycle.join(", ")
        )));
    }
    Ok(order)
}

fn same_facet_shape(left: &FacetRuntime, right: &FacetRuntime) -> bool {
    same_references(&lock(&left.requires), &lock(&right.requires))
        && same_references(&lock(&left.provides), &lock(&right.provides))
}

fn same_references(left: &[FacetServiceReference], right: &[FacetServiceReference]) -> bool {
    left.len() == right.len()
        && left.iter().all(|reference| {
            right.iter().any(|other| {
                other.service_id == reference.service_id && other.mode == reference.mode
            })
        })
}
