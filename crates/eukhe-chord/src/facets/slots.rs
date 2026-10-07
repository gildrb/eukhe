//! The host's service slots and its process-local keyed service registry
//! (the `HostServiceSlots` and `LocalKeyedServiceRegistry` classes of
//! `facets/host.ts`).

use std::collections::HashMap;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use crate::callback::{Closer, Disposer};
use crate::context::Context;
use crate::error::{ChordError, ErrorReporter};
use crate::services::consumer::{RemoteServices, ServiceObserver};
use crate::services::handle::{AccessGuard, ServiceHandle, ServiceSlot, SlotTarget, WrapObjects};
use crate::services::instances::{
    InstanceDirectory, InstanceDirectoryEntry, InstanceObserver, Readiness,
};
use crate::types::ServiceToken;

use super::host::Erased;

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

struct LocalEntry {
    key: String,
    generation: u64,
    service: Erased,
}

impl InstanceDirectoryEntry for LocalEntry {
    fn key(&self) -> &str {
        &self.key
    }

    fn generation(&self) -> u64 {
        self.generation
    }

    fn service(&self) -> SlotTarget {
        self.service.target()
    }

    fn deactivate(&self) {}
}

struct LocalKeyedRegistration {
    generations: Mutex<HashMap<String, u64>>,
    directory: InstanceDirectory<LocalEntry>,
}

#[derive(Clone)]
pub(super) struct LocalKeyedServiceRegistry {
    inner: Arc<Mutex<LocalRegistryState>>,
}

struct LocalRegistryState {
    registrations: HashMap<String, Arc<LocalKeyedRegistration>>,
    disposed: bool,
}

impl LocalKeyedServiceRegistry {
    pub(super) fn new(
        services: &[ServiceToken],
        on_error: &ErrorReporter,
    ) -> Result<Self, ChordError> {
        let mut registrations = HashMap::new();
        for service in services {
            let registration = Arc::new(LocalKeyedRegistration {
                generations: Mutex::new(HashMap::new()),
                directory: InstanceDirectory::new(Readiness::Ready, Arc::clone(on_error)),
            });
            if registrations
                .insert(service.id().to_owned(), registration)
                .is_some()
            {
                return Err(ChordError::type_error(
                    "Local keyed service registry has duplicate IDs",
                ));
            }
        }
        Ok(Self {
            inner: Arc::new(Mutex::new(LocalRegistryState {
                registrations,
                disposed: false,
            })),
        })
    }

    fn registration(&self, service_id: &str) -> Result<Arc<LocalKeyedRegistration>, ChordError> {
        let state = lock(&self.inner);
        if state.disposed {
            return Err(ChordError::error(
                "Local keyed service registry is disposed",
            ));
        }
        state.registrations.get(service_id).cloned().ok_or_else(|| {
            ChordError::error(format!(
                "Local keyed service {service_id} is not registered"
            ))
        })
    }

    pub(super) fn spawn(
        &self,
        service: &ServiceToken,
        key: &str,
        implementation: &Erased,
    ) -> Result<Closer, ChordError> {
        if lock(&self.inner).disposed {
            return Err(ChordError::error(
                "Local keyed service registry is disposed",
            ));
        }
        if key.is_empty() {
            return Err(ChordError::type_error(
                "Local service instance key must not be empty",
            ));
        }
        let registration = self.registration(service.id())?;
        if registration.directory.get(key).is_some() {
            return Err(ChordError::error(format!(
                "Local service {} already has a live instance with key {key}",
                service.id()
            )));
        }
        let generation = {
            let mut generations = lock(&registration.generations);
            let generation = generations.get(key).copied().unwrap_or(0) + 1;
            generations.insert(key.to_owned(), generation);
            generation
        };
        let instance = Arc::new(LocalEntry {
            key: key.to_owned(),
            generation,
            service: implementation.clone(),
        });
        registration.directory.insert(&instance)?;
        let closed = Mutex::new(false);
        Ok(Closer::new(move || {
            {
                let mut closed = lock(&closed);
                if *closed {
                    return Ok(());
                }
                *closed = true;
            }
            registration.directory.remove(&instance);
            Ok(())
        }))
    }

    fn observe(&self, service_id: &str, handler: InstanceObserver) -> Result<Disposer, ChordError> {
        self.registration(service_id)?.directory.observe(handler)
    }

    pub(super) fn dispose(&self) {
        let registrations = {
            let mut state = lock(&self.inner);
            if state.disposed {
                return;
            }
            state.disposed = true;
            std::mem::take(&mut state.registrations)
        };
        for registration in registrations.into_values() {
            registration.directory.dispose();
        }
    }
}

#[derive(Clone)]
pub(super) enum KeyedSource {
    Local(LocalKeyedServiceRegistry),
    Remote(Arc<dyn RemoteServices>),
}

#[derive(Default)]
pub(super) struct HostServiceSlots {
    singletons: Mutex<HashMap<String, Arc<ServiceSlot>>>,
    keyed_sources: Mutex<HashMap<String, KeyedSource>>,
}

fn wrap_objects(service: &ServiceToken) -> WrapObjects {
    if service.local() {
        WrapObjects::Plain
    } else {
        WrapObjects::Wrap
    }
}

impl HostServiceSlots {
    pub(super) fn get_singleton(
        &self,
        service: &ServiceToken,
        assert_access: AccessGuard,
    ) -> ServiceHandle {
        let slot = Arc::clone(
            lock(&self.singletons)
                .entry(service.id().to_owned())
                .or_insert_with(|| ServiceSlot::new(service.id(), wrap_objects(service))),
        );
        ServiceHandle::view(slot.view(assert_access))
    }

    pub(super) fn has_singleton(&self, service_id: &str) -> bool {
        lock(&self.singletons).contains_key(service_id)
    }

    pub(super) fn observe(
        &self,
        service: &ServiceToken,
        assert_access: AccessGuard,
        handler: ServiceObserver,
    ) -> Result<Disposer, ChordError> {
        let Some(source) = lock(&self.keyed_sources).get(service.id()).cloned() else {
            return Err(ChordError::error(format!(
                "Service {} is disconnected",
                service.id()
            )));
        };
        let stopped = Arc::new(Mutex::new(false));
        let observed_service = service.clone();
        let observation_stopped = Arc::clone(&stopped);
        let wrapper = move |target: SlotTarget, context: Context| {
            let slot = ServiceSlot::new(observed_service.id(), wrap_objects(&observed_service));
            slot.bind(target);
            let assert_access = Arc::clone(&assert_access);
            let stopped = Arc::clone(&observation_stopped);
            let guard_context = context.clone();
            let service_id = observed_service.id().to_owned();
            let view = slot.view(Arc::new(move || {
                assert_access()?;
                if *lock(&stopped) || guard_context.aborted() {
                    return Err(ChordError::error(format!(
                        "Keyed service {service_id} observation is closed"
                    )));
                }
                Ok(())
            }));
            handler.call(ServiceHandle::view(view), context)
        };
        let stop = match source {
            KeyedSource::Local(registry) => registry.observe(service.id(), Arc::new(wrapper))?,
            KeyedSource::Remote(services) => services.observe(
                service,
                ServiceObserver::new(move |handle: ServiceHandle, context| {
                    wrapper(handle.into_target(), context)
                }),
            )?,
        };
        Ok(Disposer::new(move || {
            {
                let mut stopped = lock(&stopped);
                if *stopped {
                    return;
                }
                *stopped = true;
            }
            stop.dispose();
        }))
    }

    pub(super) fn bind_singleton(&self, service_id: &str, target: SlotTarget) {
        if let Some(slot) = lock(&self.singletons).get(service_id) {
            slot.bind(target);
        }
    }

    pub(super) fn bind_keyed(&self, service_id: &str, source: KeyedSource) {
        lock(&self.keyed_sources).insert(service_id.to_owned(), source);
    }

    pub(super) fn dispose(&self) {
        let slots: Vec<Arc<ServiceSlot>> = lock(&self.singletons)
            .drain()
            .map(|(_, slot)| slot)
            .collect();
        for slot in slots {
            slot.unbind();
        }
        lock(&self.keyed_sources).clear();
    }
}
