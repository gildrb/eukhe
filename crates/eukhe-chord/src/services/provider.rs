//! The remote service provider and per-consumer endpoints (port of
//! `services/provider.ts`).
//!
//! # Threads
//!
//! Provider bookkeeping lives behind one mutex that is never held while
//! application code (subscription listeners, implementations) runs. An
//! update is queued for every subscriber under the lock; each subscriber's
//! FIFO is then drained by at most one caller at a time.

use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};

use futures::future::BoxFuture;
use futures::FutureExt;
use indexmap::IndexMap;

use crate::callback::{Closer, Disposer, Outcome};
use crate::context::Context;
use crate::delta::Op;
use crate::error::{collected, ChordError};
use crate::json::JsonValue;
use crate::task::settle_detached;
use crate::types::{
    ServiceCall, ServiceCatalogueEntry, ServiceInstanceAddress, ServiceInstanceSnapshot,
    ServiceMemberSnapshot, ServiceMode, ServiceProviderUpdate, ServiceSubscription,
    ServiceSubscriptionSnapshot, ServiceToken, ServiceUpdateListener,
};

use super::dispatch::{MethodFuture, RemoteServiceObject, ServiceMember};
use super::errors::{RemoteServiceError, RemoteServiceErrorCode};
use super::state::service_delivery_context;
use super::state_internals::ReplicatedStateRef;
use super::wire::{catalogue_json, decode_service_control_call, ServiceControlCall};

/// The most updates that wait for one subscriber before a reset.
const BUFFER_LIMIT: usize = 100;

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Member kinds, for singleton replacement shape checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ServiceMemberKind {
    Method,
    State,
}

#[derive(Clone)]
enum InstanceMember {
    Method,
    State(ReplicatedStateRef),
}

impl InstanceMember {
    fn kind(&self) -> ServiceMemberKind {
        match self {
            Self::Method => ServiceMemberKind::Method,
            Self::State(_) => ServiceMemberKind::State,
        }
    }
}

/// An implementation's members, sorted by name (UTF-16 order, like JS
/// `Array.prototype.sort`).
struct ClassifiedImplementation {
    implementation: Arc<dyn RemoteServiceObject>,
    members: Vec<(String, InstanceMember)>,
}

type MemberShape = Vec<(String, ServiceMemberKind)>;

struct ProviderInstance {
    address: Option<ServiceInstanceAddress>,
    implementation: Arc<dyn RemoteServiceObject>,
    members: Vec<(String, InstanceMember)>,
    remove_member_listeners: Mutex<Vec<Disposer>>,
    active: AtomicBool,
}

impl ProviderInstance {
    fn deactivate(&self) {
        self.active.store(false, AtomicOrdering::SeqCst);
        let listeners = std::mem::take(&mut *lock(&self.remove_member_listeners));
        for remove in listeners {
            remove.dispose();
        }
    }

    fn member(&self, name: &str) -> Option<&InstanceMember> {
        self.members
            .iter()
            .find_map(|(candidate, member)| (candidate == name).then_some(member))
    }
}

type MemberKey = (Option<ServiceInstanceAddress>, String);

#[allow(
    clippy::struct_excessive_bools,
    reason = "the four independent TS subscriber flags"
)]
struct SubscriberState {
    buffer: VecDeque<(ServiceProviderUpdate, Context)>,
    snapshot_sequences: HashMap<MemberKey, u64>,
    active: bool,
    draining: bool,
    terminated: bool,
    closed: bool,
}

struct ProviderSubscriber {
    listener: ServiceUpdateListener,
    state: Mutex<SubscriberState>,
}

/// One entry of the provider's constructor list (`ServiceProviderDefinition`
/// or a bare `{ id }`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ServiceProviderDefinition {
    /// The service.
    pub service: ServiceToken,
    /// Its mode.
    pub mode: ServiceMode,
}

impl ServiceProviderDefinition {
    /// A singleton definition.
    #[must_use]
    pub fn singleton(service: &impl AsRef<ServiceToken>) -> Self {
        Self {
            service: service.as_ref().clone(),
            mode: ServiceMode::Singleton,
        }
    }

    /// A keyed definition.
    #[must_use]
    pub fn keyed(service: &impl AsRef<ServiceToken>) -> Self {
        Self {
            service: service.as_ref().clone(),
            mode: ServiceMode::Keyed,
        }
    }
}

struct ServiceRegistration {
    service_id: String,
    mode: ServiceMode,
    singleton: Option<Arc<ProviderInstance>>,
    singleton_shape: Option<MemberShape>,
    instances: IndexMap<String, Arc<ProviderInstance>>,
    generations: HashMap<String, u64>,
    subscribers: Vec<Arc<ProviderSubscriber>>,
}

struct ProviderState {
    registrations: IndexMap<String, ServiceRegistration>,
    disposed: bool,
}

struct ProviderInner {
    catalogue: Arc<[ServiceCatalogueEntry]>,
    state: Mutex<ProviderState>,
}

/// Publishes services to remote consumers: singleton providers with
/// replacement, keyed instances with generations, and subscriptions with
/// per-subscriber FIFOs. Clones share one provider.
#[derive(Clone)]
pub struct RemoteServiceProvider {
    inner: Arc<ProviderInner>,
}

impl RemoteServiceProvider {
    /// Allowlist `entries` (TS `new RemoteServiceProvider(entries)`).
    ///
    /// # Errors
    ///
    /// A process-local service or a duplicate ID.
    pub fn new(
        entries: impl IntoIterator<Item = ServiceProviderDefinition>,
    ) -> Result<Self, ChordError> {
        let definitions: Vec<ServiceProviderDefinition> = entries.into_iter().collect();
        for definition in &definitions {
            if definition.service.local() {
                return Err(ChordError::type_error(format!(
                    "Local service {} cannot be published remotely",
                    definition.service.id()
                )));
            }
        }
        let mut registrations = IndexMap::new();
        for definition in &definitions {
            let id = definition.service.id().to_owned();
            if registrations.contains_key(&id) {
                return Err(ChordError::type_error(
                    "Remote service catalogue contains duplicate IDs",
                ));
            }
            registrations.insert(
                id.clone(),
                ServiceRegistration {
                    service_id: id,
                    mode: definition.mode,
                    singleton: None,
                    singleton_shape: None,
                    instances: IndexMap::new(),
                    generations: HashMap::new(),
                    subscribers: Vec::new(),
                },
            );
        }
        let catalogue = definitions
            .iter()
            .map(|definition| ServiceCatalogueEntry {
                service_id: definition.service.id().to_owned(),
                mode: definition.mode,
            })
            .collect();
        Ok(Self {
            inner: Arc::new(ProviderInner {
                catalogue,
                state: Mutex::new(ProviderState {
                    registrations,
                    disposed: false,
                }),
            }),
        })
    }

    /// The published services in constructor order.
    #[must_use]
    pub fn catalogue(&self) -> &[ServiceCatalogueEntry] {
        &self.inner.catalogue
    }

    /// Whether both handles are the same provider.
    #[must_use]
    pub fn same(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }

    /// Install the singleton implementation of `service`.
    ///
    /// # Errors
    ///
    /// A disposed provider, a local or unlisted service, a keyed service, an
    /// existing provider, an invalid implementation, or a shape change.
    pub fn provide(
        &self,
        service: &impl AsRef<ServiceToken>,
        implementation: impl Into<Arc<dyn RemoteServiceObject>>,
    ) -> Result<(), ChordError> {
        let service = service.as_ref();
        let implementation = implementation.into();
        let mut state = self.lock_active()?;
        assert_remotable(service)?;
        assert_allowed(&state, service.id())?;
        let registration = registration(&mut state, service.id(), ServiceMode::Singleton)?;
        if registration.singleton.is_some() {
            return Err(RemoteServiceError::new(
                RemoteServiceErrorCode::ServiceModeMismatch,
                format!("Remote service {} already has a provider", service.id()),
            )
            .into());
        }
        let classified =
            classify_remote_service_implementation(&registration.service_id, implementation)?;
        let shape = member_shape(&classified.members);
        assert_singleton_shape(registration, &shape)?;
        let instance = self.create_instance(registration, classified, None);
        registration.singleton = Some(instance);
        registration.singleton_shape = Some(shape);
        Ok(())
    }

    /// Disconnect one singleton while preserving active subscriptions and
    /// remote facades.
    ///
    /// # Errors
    ///
    /// Misuse, or subscriber failures publishing the unavailability.
    pub fn withdraw(&self, service: &impl AsRef<ServiceToken>) -> Result<(), ChordError> {
        let service = service.as_ref();
        let pending = {
            let mut state = self.lock_active()?;
            assert_remotable(service)?;
            assert_allowed(&state, service.id())?;
            let registration = registration(&mut state, service.id(), ServiceMode::Singleton)?;
            let Some(previous) = registration.singleton.take() else {
                return Ok(());
            };
            previous.deactivate();
            enqueue(registration, &ServiceProviderUpdate::Unavailable, None)
        };
        pending.deliver()
    }

    /// Check a singleton replacement without changing the active provider.
    ///
    /// # Errors
    ///
    /// Misuse, an invalid implementation, or a shape change.
    pub fn validate_replacement(
        &self,
        service: &impl AsRef<ServiceToken>,
        implementation: impl Into<Arc<dyn RemoteServiceObject>>,
    ) -> Result<(), ChordError> {
        let service = service.as_ref();
        let implementation = implementation.into();
        let mut state = self.lock_active()?;
        assert_remotable(service)?;
        assert_allowed(&state, service.id())?;
        let registration = registration(&mut state, service.id(), ServiceMode::Singleton)?;
        let classified =
            classify_remote_service_implementation(&registration.service_id, implementation)?;
        assert_singleton_shape(registration, &member_shape(&classified.members))
    }

    /// Replace one singleton without making its stable remote facade
    /// unavailable.
    ///
    /// # Errors
    ///
    /// Misuse, an invalid implementation, a shape change, or subscriber
    /// failures publishing the replacement.
    pub fn replace(
        &self,
        service: &impl AsRef<ServiceToken>,
        implementation: impl Into<Arc<dyn RemoteServiceObject>>,
    ) -> Result<(), ChordError> {
        let service = service.as_ref();
        let implementation = implementation.into();
        let pending = {
            let mut state = self.lock_active()?;
            assert_remotable(service)?;
            assert_allowed(&state, service.id())?;
            let registration = registration(&mut state, service.id(), ServiceMode::Singleton)?;
            let classified =
                classify_remote_service_implementation(&registration.service_id, implementation)?;
            let shape = member_shape(&classified.members);
            assert_singleton_shape(registration, &shape)?;
            let replacement = self.create_instance(registration, classified, None);
            if let Some(previous) = registration.singleton.take() {
                previous.deactivate();
            }
            let snapshot = snapshot_instance(&replacement);
            registration.singleton = Some(replacement);
            registration.singleton_shape = Some(shape);
            enqueue(
                registration,
                &ServiceProviderUpdate::Replaced { snapshot },
                None,
            )
        };
        pending.deliver()
    }

    /// The current singleton implementation.
    ///
    /// # Errors
    ///
    /// Misuse, or no singleton provider.
    pub fn use_service(
        &self,
        service: &impl AsRef<ServiceToken>,
    ) -> Result<Arc<dyn RemoteServiceObject>, ChordError> {
        let service = service.as_ref();
        let state = self.lock_active()?;
        assert_remotable(service)?;
        assert_allowed(&state, service.id())?;
        match state.registrations.get(service.id()) {
            Some(ServiceRegistration {
                mode: ServiceMode::Singleton,
                singleton: Some(singleton),
                ..
            }) => Ok(Arc::clone(&singleton.implementation)),
            _ => Err(RemoteServiceError::new(
                RemoteServiceErrorCode::ServiceNotFound,
                format!("Remote service {} has no local provider", service.id()),
            )
            .into()),
        }
    }

    /// Spawn the next generation of keyed instance `key`. The returned closer
    /// retires it.
    ///
    /// # Errors
    ///
    /// Misuse, an empty or live key, an invalid implementation, or
    /// subscriber failures publishing the spawn.
    pub fn spawn(
        &self,
        service: &impl AsRef<ServiceToken>,
        key: &str,
        implementation: impl Into<Arc<dyn RemoteServiceObject>>,
    ) -> Result<Closer, ChordError> {
        let service = service.as_ref();
        let implementation = implementation.into();
        let (pending, instance, address) = {
            let mut state = self.lock_active()?;
            assert_remotable(service)?;
            assert_allowed(&state, service.id())?;
            if key.is_empty() {
                return Err(ChordError::type_error(
                    "Remote service instance key must not be empty",
                ));
            }
            let registration = registration(&mut state, service.id(), ServiceMode::Keyed)?;
            if registration.instances.contains_key(key) {
                return Err(RemoteServiceError::new(
                    RemoteServiceErrorCode::ServiceModeMismatch,
                    format!(
                        "Remote service {} already has a live instance with key {key}",
                        service.id()
                    ),
                )
                .into());
            }
            let generation = registration.generations.get(key).copied().unwrap_or(0) + 1;
            registration.generations.insert(key.to_owned(), generation);
            let address = ServiceInstanceAddress {
                key: key.to_owned(),
                generation,
            };
            let classified =
                classify_remote_service_implementation(&registration.service_id, implementation)?;
            let instance = self.create_instance(registration, classified, Some(&address));
            registration
                .instances
                .insert(key.to_owned(), Arc::clone(&instance));
            let snapshot = snapshot_instance(&instance);
            let pending = enqueue(
                registration,
                &ServiceProviderUpdate::Spawned { instance: snapshot },
                None,
            );
            (pending, instance, address)
        };
        let closer = self.instance_closer(service.id(), instance, address);
        pending.deliver()?;
        Ok(closer)
    }

    fn instance_closer(
        &self,
        service_id: &str,
        instance: Arc<ProviderInstance>,
        address: ServiceInstanceAddress,
    ) -> Closer {
        let provider = Arc::downgrade(&self.inner);
        let service_id = service_id.to_owned();
        let closed = AtomicBool::new(false);
        Closer::new(move || {
            if closed.swap(true, AtomicOrdering::SeqCst) {
                return Ok(());
            }
            let Some(provider) = provider.upgrade() else {
                return Ok(());
            };
            let pending = {
                let mut state = lock(&provider.state);
                let Some(registration) = state.registrations.get_mut(&service_id) else {
                    return Ok(());
                };
                let current = registration.instances.get(&address.key);
                if !current.is_some_and(|current| Arc::ptr_eq(current, &instance)) {
                    return Ok(());
                }
                instance.deactivate();
                registration.instances.shift_remove(&address.key);
                enqueue(
                    registration,
                    &ServiceProviderUpdate::Closed {
                        instance: address.clone(),
                    },
                    None,
                )
            };
            pending.deliver()
        })
    }

    /// Invoke one method. Misuse is reported through the returned future,
    /// like a rejected TS async method.
    #[must_use]
    pub fn invoke(&self, call: ServiceCall, context: &Context) -> MethodFuture {
        let target = (|| {
            let state = self.lock_active()?;
            assert_allowed(&state, &call.service_id)?;
            let Some(registration) = state.registrations.get(&call.service_id) else {
                return Err(RemoteServiceError::new(
                    RemoteServiceErrorCode::ServiceNotFound,
                    format!("Unknown remote service {}", call.service_id),
                )
                .into());
            };
            let instance = resolve_instance(registration, call.instance.as_ref())?;
            match instance.member(&call.member) {
                None => Err(RemoteServiceError::new(
                    RemoteServiceErrorCode::ServiceMemberNotFound,
                    format!(
                        "Unknown remote service member {}.{}",
                        call.service_id, call.member
                    ),
                )
                .into()),
                Some(InstanceMember::State(_)) => Err(RemoteServiceError::new(
                    RemoteServiceErrorCode::ServiceMemberMismatch,
                    format!(
                        "Remote service member {}.{} is not a method",
                        call.service_id, call.member
                    ),
                )
                .into()),
                Some(InstanceMember::Method) => Ok(Arc::clone(&instance.implementation)),
            }
        })();
        match target {
            Ok(implementation) => implementation.invoke(&call.member, call.args, context),
            Err(error) => futures::future::ready(Err(error)).boxed(),
        }
    }

    /// Open one subscription. Updates buffer until
    /// [`activate`](ProviderSubscription::activate).
    ///
    /// # Errors
    ///
    /// Misuse, or a singleton without a provider.
    pub fn subscribe(
        &self,
        service_id: &str,
        mode: ServiceMode,
        listener: ServiceUpdateListener,
    ) -> Result<ProviderSubscription, ChordError> {
        let mut state = self.lock_active()?;
        assert_allowed(&state, service_id)?;
        let registration = registration(&mut state, service_id, mode)?;
        if registration.mode == ServiceMode::Singleton && registration.singleton.is_none() {
            return Err(RemoteServiceError::new(
                RemoteServiceErrorCode::ServiceNotFound,
                format!("Remote service {service_id} has no provider"),
            )
            .into());
        }
        let snapshot = snapshot_registration(registration);
        let mut snapshot_sequences = HashMap::new();
        record_snapshot_sequences(&mut snapshot_sequences, &snapshot.instances);
        let subscriber = Arc::new(ProviderSubscriber {
            listener,
            state: Mutex::new(SubscriberState {
                buffer: VecDeque::new(),
                snapshot_sequences,
                active: false,
                draining: false,
                terminated: false,
                closed: false,
            }),
        });
        registration.subscribers.push(Arc::clone(&subscriber));
        Ok(ProviderSubscription {
            provider: Arc::downgrade(&self.inner),
            service_id: service_id.to_owned(),
            subscriber,
            snapshot,
        })
    }

    /// Retire every provider and terminate every subscription after it
    /// drains its final updates. Idempotent.
    ///
    /// # Errors
    ///
    /// Subscriber failures publishing the final updates.
    pub fn dispose(&self) -> Result<(), ChordError> {
        let registrations = {
            let mut state = lock(&self.inner.state);
            if state.disposed {
                return Ok(());
            }
            state.disposed = true;
            std::mem::take(&mut state.registrations)
        };
        let mut errors = Vec::new();
        for (_, mut registration) in registrations {
            if let Some(singleton) = registration.singleton.take() {
                singleton.deactivate();
                if let Err(error) =
                    enqueue(&registration, &ServiceProviderUpdate::Unavailable, None).deliver()
                {
                    errors.push(error);
                }
            }
            let instances: Vec<(String, Arc<ProviderInstance>)> =
                registration.instances.drain(..).collect();
            for (_, instance) in instances {
                instance.deactivate();
                let Some(address) = instance.address.clone() else {
                    continue;
                };
                let update = ServiceProviderUpdate::Closed { instance: address };
                if let Err(error) = enqueue(&registration, &update, None).deliver() {
                    errors.push(error);
                }
            }
            for subscriber in registration.subscribers.drain(..) {
                let mut state = lock(&subscriber.state);
                if state.active && !state.draining {
                    state.closed = true;
                    state.buffer.clear();
                } else {
                    state.terminated = true;
                }
            }
        }
        collected(errors, "Failed to dispose remote service provider")
    }

    fn lock_active(&self) -> Result<MutexGuard<'_, ProviderState>, ChordError> {
        let state = lock(&self.inner.state);
        if state.disposed {
            return Err(ChordError::error("Remote service provider is disposed"));
        }
        Ok(state)
    }

    fn create_instance(
        &self,
        registration: &ServiceRegistration,
        classified: ClassifiedImplementation,
        address: Option<&ServiceInstanceAddress>,
    ) -> Arc<ProviderInstance> {
        let instance = Arc::new(ProviderInstance {
            address: address.cloned(),
            implementation: classified.implementation,
            members: classified.members,
            remove_member_listeners: Mutex::new(Vec::new()),
            active: AtomicBool::new(true),
        });
        let mut removers = Vec::new();
        for (name, member) in &instance.members {
            let InstanceMember::State(state) = member else {
                continue;
            };
            let provider = Arc::downgrade(&self.inner);
            let weak_instance = Arc::downgrade(&instance);
            let service_id = registration.service_id.clone();
            let member = name.clone();
            let address = address.cloned();
            removers.push(state.internals.subscribe(Arc::new(
                move |ops: &Arc<[Op]>, sequence, context| {
                    let active = weak_instance
                        .upgrade()
                        .is_some_and(|instance| instance.active.load(AtomicOrdering::SeqCst));
                    if !active {
                        return Ok(());
                    }
                    let Some(provider) = provider.upgrade() else {
                        return Ok(());
                    };
                    let update = ServiceProviderUpdate::State {
                        instance: address.clone(),
                        member: member.clone(),
                        sequence,
                        ops: Arc::clone(ops),
                    };
                    emit(&provider, &service_id, &update, Some(context))
                },
            )));
        }
        *lock(&instance.remove_member_listeners) = removers;
        instance
    }
}

/// Queue `update` on the registration's subscribers (under the provider
/// lock) and deliver it afterwards.
fn emit(
    provider: &ProviderInner,
    service_id: &str,
    update: &ServiceProviderUpdate,
    context: Option<&Context>,
) -> Result<(), ChordError> {
    let pending = {
        let state = lock(&provider.state);
        let Some(registration) = state.registrations.get(service_id) else {
            return Ok(());
        };
        enqueue(registration, update, context)
    };
    pending.deliver()
}

/// Updates queued for subscribers, to drain once the provider lock is
/// released.
#[must_use]
struct PendingDelivery {
    service_id: String,
    subscribers: Vec<Arc<ProviderSubscriber>>,
}

impl PendingDelivery {
    fn deliver(self) -> Result<(), ChordError> {
        let mut errors = Vec::new();
        for subscriber in &self.subscribers {
            errors.extend(drain_subscriber(subscriber));
        }
        collected(
            errors,
            &format!(
                "Failed to publish remote service {} update",
                self.service_id
            ),
        )
    }
}

fn enqueue(
    registration: &ServiceRegistration,
    update: &ServiceProviderUpdate,
    context: Option<&Context>,
) -> PendingDelivery {
    let subscribers = registration.subscribers.clone();
    if subscribers.is_empty() {
        return PendingDelivery {
            service_id: registration.service_id.clone(),
            subscribers,
        };
    }
    let delivery_context = context.cloned().unwrap_or_else(service_delivery_context);
    // Queue for everyone before invoking user code, including reentrant
    // publications.
    for subscriber in &subscribers {
        let mut state = lock(&subscriber.state);
        if state.closed || update_covered_by_snapshot(&mut state.snapshot_sequences, update) {
            continue;
        }
        if state.buffer.len() == BUFFER_LIMIT {
            let snapshot = snapshot_registration(registration);
            state.buffer.clear();
            state.snapshot_sequences.clear();
            record_snapshot_sequences(&mut state.snapshot_sequences, &snapshot.instances);
            state.buffer.push_back((
                ServiceProviderUpdate::Reset { snapshot },
                delivery_context.clone(),
            ));
        } else {
            state
                .buffer
                .push_back((update.clone(), delivery_context.clone()));
        }
    }
    PendingDelivery {
        service_id: registration.service_id.clone(),
        subscribers,
    }
}

fn drain_subscriber(subscriber: &ProviderSubscriber) -> Vec<ChordError> {
    {
        let mut state = lock(&subscriber.state);
        if !state.active || state.closed || state.draining {
            return Vec::new();
        }
        state.draining = true;
    }
    let mut errors = Vec::new();
    loop {
        let entry = {
            let mut state = lock(&subscriber.state);
            if state.closed {
                None
            } else {
                state.buffer.pop_front()
            }
        };
        let Some((update, context)) = entry else {
            break;
        };
        if let Err(error) = (subscriber.listener)(update, &context) {
            errors.push(error);
        }
    }
    let mut state = lock(&subscriber.state);
    state.draining = false;
    if state.terminated {
        state.closed = true;
    }
    errors
}

/// One provider subscription.
pub struct ProviderSubscription {
    provider: Weak<ProviderInner>,
    service_id: String,
    subscriber: Arc<ProviderSubscriber>,
    snapshot: ServiceSubscriptionSnapshot,
}

impl ProviderSubscription {
    /// The atomic baseline.
    #[must_use]
    pub fn snapshot(&self) -> &ServiceSubscriptionSnapshot {
        &self.snapshot
    }

    /// Deliver buffered and later updates. Idempotent.
    ///
    /// # Errors
    ///
    /// Listener failures while replaying the buffer.
    pub fn activate(&self) -> Result<(), ChordError> {
        {
            let mut state = lock(&self.subscriber.state);
            if state.closed || state.active {
                return Ok(());
            }
            state.active = true;
        }
        collected(
            drain_subscriber(&self.subscriber),
            "Failed to activate remote service subscription",
        )
    }

    /// Stop delivery. Idempotent.
    pub fn close(&self) {
        {
            let mut state = lock(&self.subscriber.state);
            if state.closed {
                return;
            }
            state.closed = true;
            state.buffer.clear();
        }
        if let Some(provider) = self.provider.upgrade() {
            let mut state = lock(&provider.state);
            if let Some(registration) = state.registrations.get_mut(&self.service_id) {
                registration
                    .subscribers
                    .retain(|candidate| !Arc::ptr_eq(candidate, &self.subscriber));
            }
        }
    }
}

impl ServiceSubscription for ProviderSubscription {
    fn snapshot(&self) -> &ServiceSubscriptionSnapshot {
        &self.snapshot
    }

    fn activate(&self) -> Result<(), ChordError> {
        ProviderSubscription::activate(self)
    }

    fn close(&self, _context: &Context) -> BoxFuture<'static, Result<(), ChordError>> {
        ProviderSubscription::close(self);
        futures::future::ready(Ok(())).boxed()
    }
}

fn registration<'a>(
    state: &'a mut ProviderState,
    service_id: &str,
    mode: ServiceMode,
) -> Result<&'a mut ServiceRegistration, ChordError> {
    let Some(registration) = state.registrations.get_mut(service_id) else {
        return Err(RemoteServiceError::new(
            RemoteServiceErrorCode::ServiceNotFound,
            format!("Unknown remote service {service_id}"),
        )
        .into());
    };
    if registration.mode != mode {
        return Err(RemoteServiceError::new(
            RemoteServiceErrorCode::ServiceModeMismatch,
            format!(
                "Remote service {service_id} is {}, not {mode}",
                registration.mode
            ),
        )
        .into());
    }
    Ok(registration)
}

fn assert_singleton_shape(
    registration: &ServiceRegistration,
    replacement: &MemberShape,
) -> Result<(), ChordError> {
    match &registration.singleton_shape {
        Some(current) if current != replacement => Err(RemoteServiceError::new(
            RemoteServiceErrorCode::ServiceMemberMismatch,
            format!(
                "Remote service {} replacement must preserve its member shape",
                registration.service_id
            ),
        )
        .into()),
        Some(_) | None => Ok(()),
    }
}

fn resolve_instance<'a>(
    registration: &'a ServiceRegistration,
    address: Option<&ServiceInstanceAddress>,
) -> Result<&'a Arc<ProviderInstance>, ChordError> {
    let service_id = &registration.service_id;
    if registration.mode == ServiceMode::Singleton {
        if address.is_some() {
            return Err(RemoteServiceError::new(
                RemoteServiceErrorCode::ServiceModeMismatch,
                format!("Remote service {service_id} is singleton"),
            )
            .into());
        }
        return registration.singleton.as_ref().ok_or_else(|| {
            RemoteServiceError::new(
                RemoteServiceErrorCode::ServiceNotFound,
                format!("Remote service {service_id} has no provider"),
            )
            .into()
        });
    }
    let Some(address) = address else {
        return Err(RemoteServiceError::new(
            RemoteServiceErrorCode::ServiceModeMismatch,
            format!("Remote service {service_id} is keyed"),
        )
        .into());
    };
    let Some(instance) = registration.instances.get(&address.key) else {
        return Err(RemoteServiceError::new(
            RemoteServiceErrorCode::ServiceInstanceNotFound,
            format!(
                "Remote service {service_id} has no instance {}",
                address.key
            ),
        )
        .into());
    };
    if instance.address.as_ref().map(|current| current.generation) != Some(address.generation) {
        return Err(RemoteServiceError::new(
            RemoteServiceErrorCode::ServiceStaleInstance,
            format!(
                "Remote service {service_id} instance {} is stale",
                address.key
            ),
        )
        .into());
    }
    Ok(instance)
}

fn snapshot_registration(registration: &ServiceRegistration) -> ServiceSubscriptionSnapshot {
    let instances = match registration.mode {
        ServiceMode::Singleton => registration
            .singleton
            .iter()
            .map(|instance| snapshot_instance(instance))
            .collect(),
        ServiceMode::Keyed => {
            let mut instances: Vec<&Arc<ProviderInstance>> =
                registration.instances.values().collect();
            instances
                .sort_by(|left, right| locale_compare(instance_key(left), instance_key(right)));
            instances
                .into_iter()
                .map(|instance| snapshot_instance(instance))
                .collect()
        }
    };
    ServiceSubscriptionSnapshot {
        service_id: registration.service_id.clone(),
        mode: registration.mode,
        instances,
    }
}

fn instance_key(instance: &ProviderInstance) -> &str {
    instance
        .address
        .as_ref()
        .map_or("", |address| address.key.as_str())
}

/// An approximation of `String.prototype.localeCompare` under the root
/// collation: letters compare case-insensitively first, lowercase before
/// uppercase on a tie, then by code points. ICU's full collation tables
/// are not reproduced.
fn locale_compare(left: &str, right: &str) -> Ordering {
    let folded = left
        .chars()
        .flat_map(char::to_lowercase)
        .cmp(right.chars().flat_map(char::to_lowercase));
    folded
        .then_with(|| {
            left.chars()
                .map(char::is_uppercase)
                .cmp(right.chars().map(char::is_uppercase))
        })
        .then_with(|| left.cmp(right))
}

fn snapshot_instance(instance: &ProviderInstance) -> ServiceInstanceSnapshot {
    let members = instance
        .members
        .iter()
        .map(|(name, member)| match member {
            InstanceMember::Method => ServiceMemberSnapshot::Method { name: name.clone() },
            InstanceMember::State(state) => {
                let snapshot = state.snapshot();
                ServiceMemberSnapshot::State {
                    name: name.clone(),
                    sequence: snapshot.sequence,
                    ops: Arc::from(vec![Op::Replace(snapshot.value)]),
                }
            }
        })
        .collect();
    ServiceInstanceSnapshot {
        instance: instance.address.clone(),
        members,
    }
}

fn record_snapshot_sequences(
    sequences: &mut HashMap<MemberKey, u64>,
    instances: &[ServiceInstanceSnapshot],
) {
    for instance in instances {
        for member in &instance.members {
            if let ServiceMemberSnapshot::State { name, sequence, .. } = member {
                sequences.insert((instance.instance.clone(), name.clone()), *sequence);
            }
        }
    }
}

fn update_covered_by_snapshot(
    sequences: &mut HashMap<MemberKey, u64>,
    update: &ServiceProviderUpdate,
) -> bool {
    match update {
        ServiceProviderUpdate::State {
            instance,
            member,
            sequence,
            ..
        } => {
            let key = (instance.clone(), member.clone());
            let Some(covered) = sequences.get(&key) else {
                return false;
            };
            if sequence <= covered {
                return true;
            }
            sequences.remove(&key);
            false
        }
        ServiceProviderUpdate::Reset { snapshot } => {
            sequences.clear();
            record_snapshot_sequences(sequences, &snapshot.instances);
            false
        }
        ServiceProviderUpdate::Replaced { snapshot } => {
            sequences.clear();
            record_snapshot_sequences(sequences, std::slice::from_ref(snapshot));
            false
        }
        ServiceProviderUpdate::Spawned { instance } => {
            record_snapshot_sequences(sequences, std::slice::from_ref(instance));
            false
        }
        ServiceProviderUpdate::Unavailable => {
            sequences.clear();
            false
        }
        ServiceProviderUpdate::Closed { instance } => {
            sequences.retain(|(address, _), _| address.as_ref() != Some(instance));
            false
        }
    }
}

fn assert_remotable(service: &ServiceToken) -> Result<(), ChordError> {
    if service.local() {
        return Err(RemoteServiceError::new(
            RemoteServiceErrorCode::ServiceNotAllowed,
            format!("Service {} is process-local", service.id()),
        )
        .into());
    }
    Ok(())
}

fn assert_allowed(state: &ProviderState, service_id: &str) -> Result<(), ChordError> {
    if !state.registrations.contains_key(service_id) {
        return Err(RemoteServiceError::new(
            RemoteServiceErrorCode::ServiceNotAllowed,
            format!("Remote service {service_id} is not allowlisted"),
        )
        .into());
    }
    Ok(())
}

/// Check that an implementation is remotely exposable.
pub(crate) fn validate_remote_service_implementation(
    service_id: &str,
    implementation: &Arc<dyn RemoteServiceObject>,
) -> Result<(), ChordError> {
    classify_remote_service_implementation(service_id, Arc::clone(implementation)).map(drop)
}

fn classify_remote_service_implementation(
    service_id: &str,
    implementation: Arc<dyn RemoteServiceObject>,
) -> Result<ClassifiedImplementation, ChordError> {
    let mut named: BTreeMap<Vec<u16>, (String, ServiceMember)> = BTreeMap::new();
    for (name, member) in implementation.members() {
        named.insert(name.encode_utf16().collect(), (name, member));
    }
    let mut members = Vec::with_capacity(named.len());
    for (name, member) in named.into_values() {
        match member {
            ServiceMember::Method => members.push((name, InstanceMember::Method)),
            ServiceMember::State(state) => members.push((name, InstanceMember::State(state))),
            ServiceMember::Value(_) => {
                return Err(ChordError::type_error(format!(
                    "Remote service member {service_id}.{name} is not remotely exposable"
                )));
            }
        }
    }
    if members.is_empty() {
        return Err(ChordError::type_error(format!(
            "Remote service {service_id} has no members"
        )));
    }
    Ok(ClassifiedImplementation {
        implementation,
        members,
    })
}

fn member_shape(members: &[(String, InstanceMember)]) -> MemberShape {
    members
        .iter()
        .map(|(name, member)| (name.clone(), member.kind()))
        .collect()
}

/// Publishes one subscription's update to a remote consumer: TS
/// `(subscriptionId, update, context) => void | Promise<void>`. Its failures
/// belong to the publisher and are ignored by the endpoint, as in TS.
pub type ServiceUpdatePublisher =
    Arc<dyn Fn(&str, ServiceProviderUpdate, &Context) -> Outcome + Send + Sync>;

/// Hosts one provider for one remote consumer and owns that consumer's
/// subscriptions.
#[derive(Clone)]
pub struct RemoteServiceEndpoint {
    provider: RemoteServiceProvider,
    state: Arc<Mutex<EndpointState>>,
}

#[derive(Default)]
struct EndpointState {
    subscriptions: HashMap<String, Arc<ProviderSubscription>>,
    disposed: bool,
}

/// Create the endpoint of one remote consumer.
#[must_use]
pub fn create_remote_service_endpoint(provider: RemoteServiceProvider) -> RemoteServiceEndpoint {
    RemoteServiceEndpoint {
        provider,
        state: Arc::default(),
    }
}

impl RemoteServiceEndpoint {
    /// Handle one call: `$chord.service` control calls or a method call.
    #[must_use]
    pub fn invoke(
        &self,
        call: ServiceCall,
        publish: &ServiceUpdatePublisher,
        context: &Context,
    ) -> MethodFuture {
        match self.control(&call, publish) {
            Some(result) => futures::future::ready(result).boxed(),
            None => self.provider.invoke(call, context),
        }
    }

    fn control(
        &self,
        call: &ServiceCall,
        publish: &ServiceUpdatePublisher,
    ) -> Option<Result<Option<JsonValue>, ChordError>> {
        if lock(&self.state).disposed {
            return Some(Err(ChordError::error(
                "Remote service endpoint is disposed",
            )));
        }
        match decode_service_control_call(call)? {
            ServiceControlCall::Catalogue => {
                Some(Ok(Some(catalogue_json(self.provider.catalogue()))))
            }
            ServiceControlCall::Subscribe {
                subscription_id,
                service_id,
                mode,
            } => Some(self.subscribe(subscription_id, &service_id, mode, publish)),
            ServiceControlCall::Unsubscribe { subscription_id } => {
                let subscription = lock(&self.state).subscriptions.remove(&subscription_id);
                Some(match subscription {
                    None => Err(ChordError::error("Service subscription was not found")),
                    Some(subscription) => {
                        subscription.close();
                        Ok(None)
                    }
                })
            }
        }
    }

    fn subscribe(
        &self,
        subscription_id: String,
        service_id: &str,
        mode: ServiceMode,
        publish: &ServiceUpdatePublisher,
    ) -> Result<Option<JsonValue>, ChordError> {
        if lock(&self.state)
            .subscriptions
            .contains_key(&subscription_id)
        {
            return Err(ChordError::error(
                "Service subscription ID is already active",
            ));
        }
        let publish = Arc::clone(publish);
        let id = subscription_id.clone();
        let subscription = Arc::new(self.provider.subscribe(
            service_id,
            mode,
            Arc::new(move |update, context| {
                // TS `void Promise.resolve(publish(...)).catch(() => {})`: the
                // publisher owns its delivery failures.
                settle_detached(
                    publish(&id, update, context),
                    Arc::new(|_ignored: ChordError| {}),
                );
                Ok(())
            }),
        )?);
        lock(&self.state)
            .subscriptions
            .insert(subscription_id, Arc::clone(&subscription));
        subscription.activate()?;
        Ok(Some(subscription.snapshot().to_json()))
    }

    /// Close every subscription. Idempotent.
    pub fn dispose(&self) {
        let subscriptions = {
            let mut state = lock(&self.state);
            if state.disposed {
                return;
            }
            state.disposed = true;
            std::mem::take(&mut state.subscriptions)
        };
        for subscription in subscriptions.into_values() {
            subscription.close();
        }
    }
}
