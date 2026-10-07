//! Remote service bindings: stable consumer facades over a transport, with
//! cold replicas, rebinding, readiness, and disposal (port of
//! `services/consumer.ts`).
//!
//! JS calls a remote method as `facade.member(...args, context)` through a
//! proxy; Rust calls [`ServiceHandle::call`] with the member name, JSON
//! arguments, and the context. The TS check that the trailing argument is a
//! `Context` is enforced by the Rust signature.

use std::collections::{HashMap, HashSet};
use std::future::Future;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};

use futures::future::{join_all, try_join_all, BoxFuture};
use futures::FutureExt;
use indexmap::IndexMap;

use crate::callback::{Disposer, Outcome};
use crate::context::{await_with_context, Context, BACKGROUND_CONTEXT};
use crate::delta::Op;
use crate::error::{AggregateError, ChordError, ErrorReporter};
use crate::json::JsonValue;
use crate::task::{microtask, ready_task, spawn_detached, spawn_eager, Task};
use crate::types::{
    RemoteServiceTransport, ServiceCall, ServiceInstanceAddress, ServiceInstanceSnapshot,
    ServiceMemberSnapshot, ServiceMode, ServiceProviderUpdate, ServiceSubscription,
    ServiceSubscriptionSnapshot, ServiceToken, StateListener,
};

use super::dispatch::MethodFuture;
use super::errors::{RemoteServiceError, RemoteServiceErrorCode};
use super::handle::{AccessGuard, ServiceHandle, ServiceSlot, SlotTarget, WrapObjects};
use super::instances::{InstanceDirectory, InstanceDirectoryEntry, Readiness};
use super::state::{service_delivery_context, ReplicatedStateReplica};

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

type ActiveCheck = Arc<dyn Fn() -> bool + Send + Sync>;
type Invoke = Arc<dyn Fn(Vec<JsonValue>, &Context) -> MethodFuture + Send + Sync>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ServiceMemberKind {
    Method,
    State,
}

impl ServiceMemberKind {
    fn as_str(self) -> &'static str {
        match self {
            Self::Method => "method",
            Self::State => "state",
        }
    }

    fn of(member: &ServiceMemberSnapshot) -> Self {
        match member {
            ServiceMemberSnapshot::Method { .. } => Self::Method,
            ServiceMemberSnapshot::State { .. } => Self::State,
        }
    }
}

#[derive(Default)]
struct SlotKinds {
    kind: Option<ServiceMemberKind>,
    expected: Option<ServiceMemberKind>,
}

/// One member of a facade: callable as a method, readable and subscribable
/// as a state, until descriptions or use fix its kind.
pub(crate) struct MemberSlot {
    service_id: Arc<str>,
    member: Arc<str>,
    invoke: Invoke,
    state: ReplicatedStateReplica,
    is_active: ActiveCheck,
    assert_access: AccessGuard,
    kinds: Mutex<SlotKinds>,
}

impl MemberSlot {
    fn set_description(&self, kind: ServiceMemberKind) -> Result<(), ChordError> {
        let mut kinds = lock(&self.kinds);
        if kinds.kind.is_some_and(|current| current != kind) {
            return Err(ChordError::error(format!(
                "Remote service member {}.{} changed kind",
                self.service_id, self.member
            )));
        }
        kinds.kind = Some(kind);
        if let Some(expected) = kinds.expected.filter(|expected| *expected != kind) {
            return Err(RemoteServiceError::new(
                RemoteServiceErrorCode::ServiceMemberMismatch,
                format!(
                    "Remote service member {}.{} is {}, not {}",
                    self.service_id,
                    self.member,
                    kind.as_str(),
                    expected.as_str()
                ),
            )
            .into());
        }
        Ok(())
    }

    fn hydrate(&self, sequence: u64, ops: &[Op], context: &Context) -> Result<(), ChordError> {
        self.set_description(ServiceMemberKind::State)?;
        self.state.hydrate(sequence, ops, context)
    }

    fn update(&self, sequence: u64, ops: &[Op], context: &Context) -> Result<(), ChordError> {
        self.set_description(ServiceMemberKind::State)?;
        self.state.update(sequence, ops, context)
    }

    fn clear(&self) {
        self.state.clear();
    }

    pub(crate) fn value(&self) -> Result<Option<JsonValue>, ChordError> {
        (self.assert_access)()?;
        self.expect(ServiceMemberKind::State)?;
        Ok(self.state.current())
    }

    pub(crate) fn subscribe(&self, listener: StateListener) -> Result<Disposer, ChordError> {
        (self.assert_access)()?;
        self.expect(ServiceMemberKind::State)?;
        Ok(self.state.subscribe_listener(listener))
    }

    pub(crate) fn call(
        &self,
        args: Vec<JsonValue>,
        context: &Context,
    ) -> Result<MethodFuture, ChordError> {
        (self.assert_access)()?;
        self.expect(ServiceMemberKind::Method)?;
        if !(self.is_active)() {
            let error = RemoteServiceError::new(
                RemoteServiceErrorCode::ServiceStaleInstance,
                format!("Remote service {} binding is closed", self.service_id),
            );
            return Ok(futures::future::ready(Err(error.into())).boxed());
        }
        Ok((self.invoke)(args, context))
    }

    fn expect(&self, kind: ServiceMemberKind) -> Result<(), ChordError> {
        let mut kinds = lock(&self.kinds);
        if kinds.expected.is_some_and(|expected| expected != kind) {
            return Err(RemoteServiceError::new(
                RemoteServiceErrorCode::ServiceMemberMismatch,
                format!(
                    "Remote service member {}.{} was used as two different kinds",
                    self.service_id, self.member
                ),
            )
            .into());
        }
        kinds.expected = Some(kind);
        if let Some(current) = kinds.kind.filter(|current| *current != kind) {
            return Err(RemoteServiceError::new(
                RemoteServiceErrorCode::ServiceMemberMismatch,
                format!(
                    "Remote service member {}.{} is {}, not {}",
                    self.service_id,
                    self.member,
                    current.as_str(),
                    kind.as_str()
                ),
            )
            .into());
        }
        Ok(())
    }
}

/// A stable consumer facade for one singleton or keyed instance.
#[derive(Clone)]
pub(crate) struct ServiceFacade {
    inner: Arc<FacadeInner>,
}

struct FacadeInner {
    service_id: Arc<str>,
    address: Option<ServiceInstanceAddress>,
    transport: Arc<dyn RemoteServiceTransport>,
    report: ErrorReporter,
    slots: Mutex<FacadeSlots>,
    is_active: ActiveCheck,
    assert_access: AccessGuard,
}

#[derive(Default)]
struct FacadeSlots {
    slots: IndexMap<String, Arc<MemberSlot>>,
    descriptions: HashMap<String, ServiceMemberKind>,
}

impl ServiceFacade {
    fn new(
        service_id: &str,
        address: Option<ServiceInstanceAddress>,
        transport: Arc<dyn RemoteServiceTransport>,
        is_active: ActiveCheck,
        assert_access: AccessGuard,
        report: ErrorReporter,
    ) -> Self {
        Self {
            inner: Arc::new(FacadeInner {
                service_id: Arc::from(service_id),
                address,
                transport,
                report,
                slots: Mutex::new(FacadeSlots::default()),
                is_active,
                assert_access,
            }),
        }
    }

    pub(crate) fn service_id(&self) -> &str {
        &self.inner.service_id
    }

    pub(crate) fn same(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }

    /// The member slot for `member`, created on first access.
    pub(crate) fn member(&self, member: &str) -> Arc<MemberSlot> {
        let mut slots = lock(&self.inner.slots);
        self.slot_locked(&mut slots, member)
    }

    fn slot_locked(&self, slots: &mut FacadeSlots, member: &str) -> Arc<MemberSlot> {
        if let Some(slot) = slots.slots.get(member) {
            return Arc::clone(slot);
        }
        let transport = Arc::clone(&self.inner.transport);
        let service_id = Arc::clone(&self.inner.service_id);
        let address = self.inner.address.clone();
        let member_name = member.to_owned();
        let slot = Arc::new(MemberSlot {
            service_id: Arc::clone(&self.inner.service_id),
            member: Arc::from(member),
            invoke: Arc::new(move |args, context| {
                transport.invoke(
                    ServiceCall {
                        service_id: service_id.to_string(),
                        instance: address.clone(),
                        member: member_name.clone(),
                        args,
                    },
                    context,
                )
            }),
            state: ReplicatedStateReplica::new(Arc::clone(&self.inner.report)),
            is_active: Arc::clone(&self.inner.is_active),
            assert_access: Arc::clone(&self.inner.assert_access),
            kinds: Mutex::new(SlotKinds {
                kind: slots.descriptions.get(member).copied(),
                expected: None,
            }),
        });
        slots.slots.insert(member.to_owned(), Arc::clone(&slot));
        slot
    }

    fn install(
        &self,
        snapshot: &ServiceInstanceSnapshot,
        context: &Context,
    ) -> Result<(), ChordError> {
        if snapshot.instance != self.inner.address {
            return Err(ChordError::error(
                "Remote service snapshot has the wrong address",
            ));
        }
        let members = validate_members(&snapshot.members)?;
        let mut plan = Vec::with_capacity(members.len());
        {
            let mut slots = lock(&self.inner.slots);
            if let Some(unknown) = slots
                .slots
                .keys()
                .find(|name| !members.iter().any(|member| member.name() == name.as_str()))
            {
                return Err(RemoteServiceError::new(
                    RemoteServiceErrorCode::ServiceMemberNotFound,
                    format!(
                        "Unknown remote service member {}.{unknown}",
                        self.inner.service_id
                    ),
                )
                .into());
            }
            slots.descriptions = members
                .iter()
                .map(|member| (member.name().to_owned(), ServiceMemberKind::of(member)))
                .collect();
            for member in members {
                let slot = match member {
                    ServiceMemberSnapshot::State { name, .. } => {
                        Some(self.slot_locked(&mut slots, name))
                    }
                    ServiceMemberSnapshot::Method { name } => slots.slots.get(name).cloned(),
                };
                plan.push((member, slot));
            }
        }
        for (member, slot) in plan {
            match (member, slot) {
                (ServiceMemberSnapshot::State { sequence, ops, .. }, Some(slot)) => {
                    slot.hydrate(*sequence, ops, context)?;
                }
                (ServiceMemberSnapshot::Method { .. }, Some(slot)) => {
                    slot.set_description(ServiceMemberKind::Method)?;
                }
                (
                    ServiceMemberSnapshot::State { .. } | ServiceMemberSnapshot::Method { .. },
                    None,
                ) => {}
            }
        }
        Ok(())
    }

    fn update(
        &self,
        member: &str,
        sequence: u64,
        ops: &[Op],
        context: &Context,
    ) -> Result<(), ChordError> {
        let slot = {
            let mut slots = lock(&self.inner.slots);
            if slots.descriptions.get(member) != Some(&ServiceMemberKind::State) {
                return Err(ChordError::error(format!(
                    "Remote service update targets non-state member {}.{member}",
                    self.inner.service_id
                )));
            }
            self.slot_locked(&mut slots, member)
        };
        slot.update(sequence, ops, context)
    }

    fn clear(&self) {
        let slots: Vec<Arc<MemberSlot>> = lock(&self.inner.slots).slots.values().cloned().collect();
        for slot in slots {
            slot.clear();
        }
    }
}

struct SingletonBinding {
    facade: ServiceFacade,
    state: Mutex<SingletonState>,
}

struct SingletonState {
    subscription: Option<Arc<dyn ServiceSubscription>>,
    starting: Option<Task>,
    active: bool,
    revision: u64,
}

struct KeyedInstance {
    key: String,
    generation: u64,
    facade: ServiceFacade,
    active: Arc<Mutex<bool>>,
}

impl InstanceDirectoryEntry for KeyedInstance {
    fn key(&self) -> &str {
        &self.key
    }

    fn generation(&self) -> u64 {
        self.generation
    }

    fn service(&self) -> SlotTarget {
        SlotTarget::Facade(self.facade.clone())
    }

    fn deactivate(&self) {
        *lock(&self.active) = false;
        self.facade.clear();
    }
}

/// Observes each live keyed instance through a guarded handle; the context
/// is cancelled when the instance retires or the observation stops.
#[derive(Clone)]
pub struct ServiceObserver {
    handler: Arc<dyn Fn(ServiceHandle, Context) -> Outcome + Send + Sync>,
}

impl ServiceObserver {
    /// Wrap a handler.
    pub fn new<F, R>(handler: F) -> Self
    where
        F: Fn(ServiceHandle, Context) -> R + Send + Sync + 'static,
        R: Into<Outcome>,
    {
        Self {
            handler: Arc::new(move |service, context| handler(service, context).into()),
        }
    }

    pub(crate) fn call(&self, service: ServiceHandle, context: Context) -> Outcome {
        (self.handler)(service, context)
    }
}

struct KeyedBinding {
    service: ServiceToken,
    transport: Arc<dyn RemoteServiceTransport>,
    report: ErrorReporter,
    assert_access: AccessGuard,
    on_empty: Box<dyn Fn() + Send + Sync>,
    instances: InstanceDirectory<KeyedInstance>,
    state: Mutex<KeyedState>,
}

struct KeyedState {
    subscription: Option<Arc<dyn ServiceSubscription>>,
    starting: Option<Task>,
    closed: bool,
    bound: bool,
    revision: u64,
}

impl KeyedBinding {
    fn observe(self: &Arc<Self>, handler: ServiceObserver) -> Result<Disposer, ChordError> {
        if lock(&self.state).closed {
            return Err(ChordError::error("Remote keyed service binding is closed"));
        }
        let stopped = Arc::new(Mutex::new(false));
        let service_id = self.service.id().to_owned();
        let assert_access = Arc::clone(&self.assert_access);
        let observation_stopped = Arc::clone(&stopped);
        let stop = self
            .instances
            .observe(Arc::new(move |target, context: Context| {
                let slot = ServiceSlot::new(&service_id, WrapObjects::Wrap);
                slot.bind(target);
                let assert_access = Arc::clone(&assert_access);
                let stopped = Arc::clone(&observation_stopped);
                let guard_context = context.clone();
                let guard_service = service_id.clone();
                let view = slot.view(Arc::new(move || {
                    assert_access()?;
                    if *lock(&stopped) || guard_context.aborted() {
                        return Err(RemoteServiceError::new(
                            RemoteServiceErrorCode::ServiceStaleInstance,
                            format!("Remote service {guard_service} observation is closed"),
                        )
                        .into());
                    }
                    Ok(())
                }));
                handler.call(ServiceHandle::view(view), context)
            }))?;
        let start = {
            let state = lock(&self.state);
            (state.bound && state.starting.is_none()).then_some(state.revision)
        };
        if let Some(revision) = start {
            let starting = spawn_eager(Arc::clone(self).start(revision));
            lock(&self.state).starting = Some(starting.clone());
            let binding = Arc::downgrade(self);
            spawn_detached(async move {
                if let Err(error) = starting.await {
                    if let Some(binding) = binding.upgrade() {
                        let current = {
                            let state = lock(&binding.state);
                            !state.closed && state.revision == revision && state.bound
                        };
                        if current {
                            (binding.report)(error);
                        }
                    }
                }
            });
        }
        let binding = Arc::downgrade(self);
        Ok(Disposer::new(move || {
            {
                let mut stopped = lock(&stopped);
                if *stopped {
                    return;
                }
                *stopped = true;
            }
            stop.dispose();
            if let Some(binding) = binding.upgrade() {
                if binding.instances.observer_count() == 0 {
                    (binding.on_empty)();
                }
            }
        }))
    }

    async fn rebind(self: Arc<Self>, bound: bool, context: Context) -> Result<(), ChordError> {
        let revision = {
            let mut state = lock(&self.state);
            if state.closed {
                return Ok(());
            }
            state.bound = bound;
            state.revision += 1;
            state.revision
        };
        self.reset(&context, WaitForStarting::No).await?;
        {
            let state = lock(&self.state);
            if state.closed || state.revision != revision || state.bound != bound {
                return Ok(());
            }
        }
        if bound && self.instances.observer_count() > 0 {
            let starting = spawn_eager(Arc::clone(&self).start(revision));
            lock(&self.state).starting = Some(starting.clone());
            starting.await?;
        }
        Ok(())
    }

    fn ready(&self) -> Task {
        lock(&self.state)
            .starting
            .clone()
            .unwrap_or_else(|| ready_task(Ok(())))
    }

    async fn close(self: Arc<Self>, context: Context) -> Result<(), ChordError> {
        {
            let mut state = lock(&self.state);
            if state.closed {
                return Ok(());
            }
            state.closed = true;
            state.revision += 1;
        }
        self.reset(&context, WaitForStarting::Yes).await?;
        self.instances.dispose();
        Ok(())
    }

    async fn reset(&self, context: &Context, wait: WaitForStarting) -> Result<(), ChordError> {
        self.instances.reset();
        let (starting, subscription) = {
            let mut state = lock(&self.state);
            (state.starting.take(), state.subscription.take())
        };
        let starting = async move {
            if let (WaitForStarting::Yes, Some(starting)) = (wait, starting) {
                // TS `starting?.catch(() => {})`: its failure was reported.
                drop(starting.await);
            }
            Ok::<(), ChordError>(())
        };
        let closing = async {
            match subscription {
                Some(subscription) => subscription.close(context).await,
                None => Ok(()),
            }
        };
        let (started, closed) = futures::join!(starting, closing);
        started.and(closed)
    }

    async fn start(self: Arc<Self>, revision: u64) -> Result<(), ChordError> {
        let listener_binding = Arc::downgrade(&self);
        let subscription: Arc<dyn ServiceSubscription> = Arc::from(
            self.transport
                .subscribe(
                    self.service.id(),
                    ServiceMode::Keyed,
                    Arc::new(move |update, context| {
                        if let Some(binding) = listener_binding.upgrade() {
                            if lock(&binding.state).revision == revision {
                                binding.update(update, context);
                            }
                        }
                        Ok(())
                    }),
                    &BACKGROUND_CONTEXT,
                )
                .await?,
        );
        microtask().await;
        let stale = {
            let state = lock(&self.state);
            state.closed || !state.bound || state.revision != revision
        };
        if stale {
            return subscription.close(&BACKGROUND_CONTEXT).await;
        }
        lock(&self.state).subscription = Some(Arc::clone(&subscription));
        let snapshot = subscription.snapshot();
        if snapshot.mode != ServiceMode::Keyed || snapshot.service_id != self.service.id() {
            return Err(ChordError::error(format!(
                "Remote service {} returned the wrong keyed snapshot",
                self.service.id()
            )));
        }
        for instance in &snapshot.instances {
            self.spawn(instance, &service_delivery_context())?;
        }
        subscription.activate()?;
        self.instances.ready()
    }

    fn update(self: &Arc<Self>, update: ServiceProviderUpdate, context: &Context) {
        if lock(&self.state).closed {
            return;
        }
        if let Err(error) = self.apply(update, context) {
            (self.report)(error);
        }
    }

    fn apply(
        self: &Arc<Self>,
        update: ServiceProviderUpdate,
        context: &Context,
    ) -> Result<(), ChordError> {
        match update {
            ServiceProviderUpdate::Reset { snapshot } => {
                validate_reset_snapshot(&snapshot, self.service.id(), ServiceMode::Keyed)?;
                let generation_of = |key: &str| {
                    snapshot
                        .instances
                        .iter()
                        .filter_map(|instance| instance.instance.as_ref())
                        .find(|address| address.key == key)
                        .map(|address| address.generation)
                };
                for instance in self.instances.values() {
                    if generation_of(&instance.key) != Some(instance.generation) {
                        self.instances.remove(&instance);
                    }
                }
                for instance_snapshot in &snapshot.instances {
                    let Some(address) = &instance_snapshot.instance else {
                        continue;
                    };
                    match self.instances.get(&address.key) {
                        None => self.spawn(instance_snapshot, context)?,
                        Some(instance) => instance.facade.install(instance_snapshot, context)?,
                    }
                }
                Ok(())
            }
            ServiceProviderUpdate::Unavailable | ServiceProviderUpdate::Replaced { .. } => Err(
                ChordError::error("Keyed service received a singleton lifecycle update"),
            ),
            ServiceProviderUpdate::Spawned { instance } => self.spawn(&instance, context),
            ServiceProviderUpdate::Closed { instance: address } => {
                if let Some(instance) = self.instances.get(&address.key) {
                    if instance.generation == address.generation {
                        self.instances.remove(&instance);
                    }
                }
                Ok(())
            }
            ServiceProviderUpdate::State {
                instance,
                member,
                sequence,
                ops,
            } => {
                let Some(address) = instance else {
                    return Err(ChordError::error(
                        "Keyed state update has no instance address",
                    ));
                };
                match self.instances.get(&address.key) {
                    Some(instance) if instance.generation == address.generation => {
                        instance.facade.update(&member, sequence, &ops, context)
                    }
                    Some(_) | None => Ok(()),
                }
            }
        }
    }

    fn spawn(
        self: &Arc<Self>,
        snapshot: &ServiceInstanceSnapshot,
        context: &Context,
    ) -> Result<(), ChordError> {
        let Some(address) = snapshot.instance.clone() else {
            return Err(ChordError::error(
                "Keyed service instance snapshot has no address",
            ));
        };
        let active = Arc::new(Mutex::new(true));
        let binding = Arc::downgrade(self);
        let instance_active = Arc::clone(&active);
        let facade = ServiceFacade::new(
            self.service.id(),
            Some(address.clone()),
            Arc::clone(&self.transport),
            Arc::new(move || {
                *lock(&instance_active)
                    && binding
                        .upgrade()
                        .is_some_and(|binding| !lock(&binding.state).closed)
            }),
            Arc::clone(&self.assert_access),
            Arc::clone(&self.report),
        );
        facade.install(snapshot, context)?;
        self.instances.replace(&Arc::new(KeyedInstance {
            key: address.key,
            generation: address.generation,
            facade,
            active,
        }))
    }
}

#[derive(Clone, Copy)]
enum WaitForStarting {
    Yes,
    No,
}

/// Options for [`create_remote_service_binding`].
#[derive(Clone)]
pub struct RemoteServiceBindingOptions {
    /// The allowlisted service IDs.
    pub services: Vec<String>,
    /// The wire boundary.
    pub transport: Arc<dyn RemoteServiceTransport>,
    /// Whether subscriptions start right away (TS default `true`).
    pub bound: bool,
    /// Receives background failures; ignored when `None`.
    pub on_error: Option<ErrorReporter>,
    /// Guards every handle operation.
    pub assert_access: Option<AccessGuard>,
}

impl RemoteServiceBindingOptions {
    /// Bound options without an error reporter or access guard.
    #[must_use]
    pub fn new(services: Vec<String>, transport: Arc<dyn RemoteServiceTransport>) -> Self {
        Self {
            services,
            transport,
            bound: true,
            on_error: None,
            assert_access: None,
        }
    }
}

/// Acquired remote services: singleton handles, keyed observations,
/// readiness, and disposal. Object-safe so service sources can return any
/// implementation.
pub trait RemoteServices: Send + Sync {
    /// Acquire one singleton service's stable handle.
    ///
    /// # Errors
    ///
    /// A disposed binding, a local or unlisted service, or a mode conflict.
    fn use_service(&self, service: &ServiceToken) -> Result<ServiceHandle, ChordError>;

    /// Observe each live instance of a keyed service.
    ///
    /// # Errors
    ///
    /// A disposed binding, a local or unlisted service, or a mode conflict.
    fn observe(
        &self,
        service: &ServiceToken,
        handler: ServiceObserver,
    ) -> Result<Disposer, ChordError>;

    /// Wait until every currently acquired service has installed its
    /// initial snapshot.
    fn ready(&self, context: &Context) -> BoxFuture<'static, Result<(), ChordError>>;

    /// Release every acquired service.
    fn dispose(&self, context: &Context) -> BoxFuture<'static, Result<(), ChordError>>;
}

/// A remote service binding over one transport. Clones share one binding.
#[derive(Clone)]
pub struct RemoteServiceBinding {
    inner: Arc<BindingInner>,
}

struct BindingInner {
    transport: Arc<dyn RemoteServiceTransport>,
    allowlist: HashSet<String>,
    report: ErrorReporter,
    assert_access: AccessGuard,
    state: Mutex<BindingState>,
}

struct BindingState {
    modes: HashMap<String, ServiceMode>,
    singletons: IndexMap<String, Arc<SingletonBinding>>,
    keyed: IndexMap<String, Arc<KeyedBinding>>,
    bound: bool,
    readiness_revision: u64,
    binding_transition: Task,
    disposed: bool,
}

/// Create a binding (TS `createRemoteServiceBinding`).
///
/// # Errors
///
/// Duplicate service IDs.
pub fn create_remote_service_binding(
    options: RemoteServiceBindingOptions,
) -> Result<RemoteServiceBinding, ChordError> {
    let mut allowlist = HashSet::new();
    for id in &options.services {
        if !allowlist.insert(id.clone()) {
            return Err(ChordError::type_error(
                "Remote service binding has duplicate service IDs",
            ));
        }
    }
    Ok(RemoteServiceBinding {
        inner: Arc::new(BindingInner {
            transport: options.transport,
            allowlist,
            report: options.on_error.unwrap_or_else(|| Arc::new(|_| {})),
            assert_access: options.assert_access.unwrap_or_else(|| Arc::new(|| Ok(()))),
            state: Mutex::new(BindingState {
                modes: HashMap::new(),
                singletons: IndexMap::new(),
                keyed: IndexMap::new(),
                bound: options.bound,
                readiness_revision: 0,
                binding_transition: ready_task(Ok(())),
                disposed: false,
            }),
        }),
    })
}

impl BindingInner {
    fn handle_access(self: &Arc<Self>) -> AccessGuard {
        let binding = Arc::downgrade(self);
        Arc::new(move || {
            let Some(binding) = binding.upgrade() else {
                return Err(ChordError::error("Remote service binding is disposed"));
            };
            if lock(&binding.state).disposed {
                return Err(ChordError::error("Remote service binding is disposed"));
            }
            (binding.assert_access)()
        })
    }

    fn assert_available(
        &self,
        state: &mut BindingState,
        service_id: &str,
        mode: ServiceMode,
    ) -> Result<(), ChordError> {
        if state.disposed {
            return Err(ChordError::error("Remote service binding is disposed"));
        }
        if !self.allowlist.contains(service_id) {
            return Err(RemoteServiceError::new(
                RemoteServiceErrorCode::ServiceNotAllowed,
                format!("Remote service {service_id} is not allowlisted"),
            )
            .into());
        }
        if let Some(existing) = state
            .modes
            .get(service_id)
            .filter(|existing| **existing != mode)
        {
            return Err(RemoteServiceError::new(
                RemoteServiceErrorCode::ServiceModeMismatch,
                format!("Remote service {service_id} is already used as {existing}"),
            )
            .into());
        }
        state.modes.insert(service_id.to_owned(), mode);
        Ok(())
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

impl RemoteServiceBinding {
    /// Acquire one singleton service's stable facade.
    ///
    /// # Errors
    ///
    /// See [`RemoteServices::use_service`].
    pub fn use_service(
        &self,
        service: &impl AsRef<ServiceToken>,
    ) -> Result<ServiceHandle, ChordError> {
        let service = service.as_ref();
        let inner = &self.inner;
        assert_remotable(service)?;
        let (binding, start) = {
            let mut state = lock(&inner.state);
            inner.assert_available(&mut state, service.id(), ServiceMode::Singleton)?;
            if let Some(binding) = state.singletons.get(service.id()) {
                return Ok(ServiceHandle::facade(binding.facade.clone()));
            }
            let binding = Arc::new_cyclic(|weak: &Weak<SingletonBinding>| {
                let weak = weak.clone();
                let binding_inner = Arc::downgrade(inner);
                SingletonBinding {
                    facade: ServiceFacade::new(
                        service.id(),
                        None,
                        Arc::clone(&inner.transport),
                        Arc::new(move || {
                            let active = weak
                                .upgrade()
                                .is_some_and(|binding| lock(&binding.state).active);
                            active
                                && binding_inner.upgrade().is_some_and(|inner| {
                                    let state = lock(&inner.state);
                                    !state.disposed && state.bound
                                })
                        }),
                        inner.handle_access(),
                        Arc::clone(&inner.report),
                    ),
                    state: Mutex::new(SingletonState {
                        subscription: None,
                        starting: None,
                        active: true,
                        revision: 0,
                    }),
                }
            });
            state
                .singletons
                .insert(service.id().to_owned(), Arc::clone(&binding));
            state.readiness_revision += 1;
            (binding, state.bound)
        };
        if start {
            let revision = 0;
            let starting = spawn_eager(start_singleton(
                Arc::clone(inner),
                service.id().to_owned(),
                Arc::clone(&binding),
                revision,
            ));
            lock(&binding.state).starting = Some(starting.clone());
            let weak_binding = Arc::downgrade(&binding);
            let weak_inner = Arc::downgrade(inner);
            spawn_detached(async move {
                if let Err(error) = starting.await {
                    let (Some(binding), Some(inner)) =
                        (weak_binding.upgrade(), weak_inner.upgrade())
                    else {
                        return;
                    };
                    let current = {
                        let binding_state = lock(&binding.state);
                        binding_state.active && binding_state.revision == revision
                    };
                    let live = {
                        let state = lock(&inner.state);
                        !state.disposed && state.bound
                    };
                    if current && live {
                        (inner.report)(error);
                    }
                }
            });
        }
        Ok(ServiceHandle::facade(binding.facade.clone()))
    }

    /// Observe each live instance of a keyed service.
    ///
    /// # Errors
    ///
    /// See [`RemoteServices::observe`].
    pub fn observe(
        &self,
        service: &impl AsRef<ServiceToken>,
        handler: ServiceObserver,
    ) -> Result<Disposer, ChordError> {
        let service = service.as_ref();
        let inner = &self.inner;
        assert_remotable(service)?;
        let binding = {
            let mut state = lock(&inner.state);
            inner.assert_available(&mut state, service.id(), ServiceMode::Keyed)?;
            if let Some(binding) = state.keyed.get(service.id()) {
                Arc::clone(binding)
            } else {
                let binding = Arc::new_cyclic(|weak: &Weak<KeyedBinding>| {
                    let weak = weak.clone();
                    let binding_inner = Arc::downgrade(inner);
                    let service_id = service.id().to_owned();
                    KeyedBinding {
                        service: service.clone(),
                        transport: Arc::clone(&inner.transport),
                        report: Arc::clone(&inner.report),
                        assert_access: inner.handle_access(),
                        on_empty: Box::new(move || {
                            let (Some(binding), Some(inner)) =
                                (weak.upgrade(), binding_inner.upgrade())
                            else {
                                return;
                            };
                            {
                                let mut state = lock(&inner.state);
                                let current = state
                                    .keyed
                                    .get(&service_id)
                                    .is_some_and(|candidate| Arc::ptr_eq(candidate, &binding));
                                if !current {
                                    return;
                                }
                                state.keyed.shift_remove(&service_id);
                                state.readiness_revision += 1;
                            }
                            let report = Arc::clone(&inner.report);
                            spawn_detached(async move {
                                if let Err(error) = binding.close(BACKGROUND_CONTEXT.clone()).await
                                {
                                    report(error);
                                }
                            });
                        }),
                        instances: InstanceDirectory::new(
                            Readiness::Pending,
                            Arc::clone(&inner.report),
                        ),
                        state: Mutex::new(KeyedState {
                            subscription: None,
                            starting: None,
                            closed: false,
                            bound: state.bound,
                            revision: 0,
                        }),
                    }
                });
                state
                    .keyed
                    .insert(service.id().to_owned(), Arc::clone(&binding));
                state.readiness_revision += 1;
                binding
            }
        };
        binding.observe(handler)
    }

    /// Wait until every currently acquired service has installed its
    /// initial snapshot.
    ///
    /// # Errors
    ///
    /// A disposed binding, a cancelled context, or a startup failure.
    pub fn ready(
        &self,
        context: &Context,
    ) -> impl Future<Output = Result<(), ChordError>> + Send + 'static {
        let inner = Arc::clone(&self.inner);
        let context = context.clone();
        async move {
            loop {
                let (revision, starts) = {
                    let state = lock(&inner.state);
                    if state.disposed {
                        return Err(ChordError::error("Remote service binding is disposed"));
                    }
                    let mut starts = vec![state.binding_transition.clone()];
                    for binding in state.singletons.values() {
                        if let Some(starting) = &lock(&binding.state).starting {
                            starts.push(starting.clone());
                        }
                    }
                    for binding in state.keyed.values() {
                        starts.push(binding.ready());
                    }
                    (state.readiness_revision, starts)
                };
                await_with_context(try_join_all(starts), &context)
                    .await
                    .map_err(ChordError::from_shared)??;
                let state = lock(&inner.state);
                if state.disposed {
                    return Err(ChordError::error("Remote service binding is disposed"));
                }
                if revision == state.readiness_revision {
                    return Ok(());
                }
            }
        }
    }

    /// Restart every subscription bound or unbound.
    ///
    /// # Errors
    ///
    /// A disposed binding, or an aggregate of transition failures.
    pub fn rebind(
        &self,
        bound: bool,
        context: &Context,
    ) -> impl Future<Output = Result<(), ChordError>> + Send + 'static {
        let inner = Arc::clone(&self.inner);
        let context = context.clone();
        let transition = (|| {
            let (singletons, keyed) = {
                let mut state = lock(&inner.state);
                if state.disposed {
                    return Err(ChordError::error("Remote service binding is disposed"));
                }
                state.bound = bound;
                state.readiness_revision += 1;
                let singletons: Vec<(String, Arc<SingletonBinding>)> = state
                    .singletons
                    .iter()
                    .map(|(id, binding)| (id.clone(), Arc::clone(binding)))
                    .collect();
                let keyed: Vec<Arc<KeyedBinding>> = state.keyed.values().cloned().collect();
                (singletons, keyed)
            };
            let mut transitions = Vec::new();
            for (service_id, binding) in singletons {
                let (subscription, revision) = {
                    let mut state = lock(&binding.state);
                    state.revision += 1;
                    (state.subscription.take(), state.revision)
                };
                binding.facade.clear();
                let starting = spawn_eager({
                    let inner = Arc::clone(&inner);
                    let context = context.clone();
                    let binding = Arc::clone(&binding);
                    async move {
                        if let Some(subscription) = subscription {
                            subscription.close(&context).await?;
                        }
                        microtask().await;
                        if bound {
                            start_singleton(inner, service_id, binding, revision).await?;
                        }
                        Ok(())
                    }
                });
                lock(&binding.state).starting = Some(starting.clone());
                transitions.push(starting);
            }
            for binding in keyed {
                transitions.push(spawn_eager(binding.rebind(bound, context.clone())));
            }
            let completion = spawn_eager(async move {
                let errors: Vec<ChordError> = join_all(transitions)
                    .await
                    .into_iter()
                    .filter_map(Result::err)
                    .collect();
                if errors.is_empty() {
                    Ok(())
                } else {
                    Err(AggregateError::new(errors, "Failed to rebind services").into())
                }
            });
            lock(&inner.state).binding_transition = completion.clone();
            Ok(completion)
        })();
        async move { transition?.await }
    }

    /// Release every acquired service. Idempotent.
    ///
    /// # Errors
    ///
    /// An aggregate of close failures.
    pub fn dispose(
        &self,
        context: &Context,
    ) -> impl Future<Output = Result<(), ChordError>> + Send + 'static {
        let closes = (|| {
            let (singletons, keyed) = {
                let mut state = lock(&self.inner.state);
                if state.disposed {
                    return None;
                }
                state.disposed = true;
                let singletons: Vec<Arc<SingletonBinding>> = state
                    .singletons
                    .drain(..)
                    .map(|(_, binding)| binding)
                    .collect();
                let keyed: Vec<Arc<KeyedBinding>> =
                    state.keyed.drain(..).map(|(_, binding)| binding).collect();
                (singletons, keyed)
            };
            let mut closes: Vec<BoxFuture<'static, Result<(), ChordError>>> = Vec::new();
            for binding in singletons {
                let (starting, subscription) = {
                    let mut state = lock(&binding.state);
                    state.active = false;
                    (state.starting.clone(), state.subscription.clone())
                };
                binding.facade.clear();
                if let Some(starting) = starting {
                    closes.push(starting.map(|_ignored| Ok(())).boxed());
                }
                if let Some(subscription) = subscription {
                    closes.push(subscription.close(context));
                }
            }
            for binding in keyed {
                closes.push(spawn_eager(binding.close(context.clone())).boxed());
            }
            Some(closes)
        })();
        async move {
            let Some(closes) = closes else {
                return Ok(());
            };
            let errors: Vec<ChordError> = join_all(closes)
                .await
                .into_iter()
                .filter_map(Result::err)
                .collect();
            if errors.is_empty() {
                Ok(())
            } else {
                Err(AggregateError::new(errors, "Failed to dispose services").into())
            }
        }
    }
}

impl RemoteServices for RemoteServiceBinding {
    fn use_service(&self, service: &ServiceToken) -> Result<ServiceHandle, ChordError> {
        RemoteServiceBinding::use_service(self, service)
    }

    fn observe(
        &self,
        service: &ServiceToken,
        handler: ServiceObserver,
    ) -> Result<Disposer, ChordError> {
        RemoteServiceBinding::observe(self, service, handler)
    }

    fn ready(&self, context: &Context) -> BoxFuture<'static, Result<(), ChordError>> {
        RemoteServiceBinding::ready(self, context).boxed()
    }

    fn dispose(&self, context: &Context) -> BoxFuture<'static, Result<(), ChordError>> {
        RemoteServiceBinding::dispose(self, context).boxed()
    }
}

async fn start_singleton(
    inner: Arc<BindingInner>,
    service_id: String,
    binding: Arc<SingletonBinding>,
    revision: u64,
) -> Result<(), ChordError> {
    let listener_binding = Arc::downgrade(&binding);
    let report = Arc::clone(&inner.report);
    let listener_service = service_id.clone();
    let subscription: Arc<dyn ServiceSubscription> = Arc::from(
        inner
            .transport
            .subscribe(
                &service_id,
                ServiceMode::Singleton,
                Arc::new(move |update, context| {
                    let Some(binding) = listener_binding.upgrade() else {
                        return Ok(());
                    };
                    {
                        let state = lock(&binding.state);
                        if !state.active || state.revision != revision {
                            return Ok(());
                        }
                    }
                    if let Err(error) =
                        apply_singleton_update(&binding.facade, &listener_service, update, context)
                    {
                        report(error);
                    }
                    Ok(())
                }),
                &BACKGROUND_CONTEXT,
            )
            .await?,
    );
    microtask().await;
    let stale = {
        let state = lock(&binding.state);
        !state.active || state.revision != revision
    } || {
        let state = lock(&inner.state);
        state.disposed || !state.bound
    };
    if stale {
        return subscription.close(&BACKGROUND_CONTEXT).await;
    }
    lock(&binding.state).subscription = Some(Arc::clone(&subscription));
    let snapshot = subscription.snapshot();
    if snapshot.mode != ServiceMode::Singleton
        || snapshot.service_id != service_id
        || snapshot.instances.len() != 1
    {
        return Err(ChordError::error(format!(
            "Remote service {service_id} returned an invalid singleton snapshot"
        )));
    }
    binding
        .facade
        .install(&snapshot.instances[0], &service_delivery_context())?;
    subscription.activate()
}

fn apply_singleton_update(
    facade: &ServiceFacade,
    service_id: &str,
    update: ServiceProviderUpdate,
    context: &Context,
) -> Result<(), ChordError> {
    match update {
        ServiceProviderUpdate::Reset { snapshot } => {
            validate_reset_snapshot(&snapshot, service_id, ServiceMode::Singleton)?;
            match snapshot.instances.first() {
                None => {
                    facade.clear();
                    Ok(())
                }
                Some(instance) => facade.install(instance, context),
            }
        }
        ServiceProviderUpdate::Unavailable => {
            facade.clear();
            Ok(())
        }
        ServiceProviderUpdate::Replaced { snapshot } => {
            if snapshot.instance.is_some() {
                return Err(ChordError::error(
                    "Singleton replacement has an instance address",
                ));
            }
            facade.install(&snapshot, context)
        }
        ServiceProviderUpdate::State {
            instance: None,
            member,
            sequence,
            ops,
        } => facade.update(&member, sequence, &ops, context),
        ServiceProviderUpdate::State {
            instance: Some(_), ..
        }
        | ServiceProviderUpdate::Spawned { .. }
        | ServiceProviderUpdate::Closed { .. } => Ok(()),
    }
}

fn validate_reset_snapshot(
    snapshot: &ServiceSubscriptionSnapshot,
    service_id: &str,
    mode: ServiceMode,
) -> Result<(), ChordError> {
    if snapshot.service_id != service_id
        || snapshot.mode != mode
        || (mode == ServiceMode::Singleton && snapshot.instances.len() > 1)
    {
        return Err(ChordError::error(
            "Remote service reset has the wrong service or mode",
        ));
    }
    let mut keys = HashSet::new();
    for instance in &snapshot.instances {
        let invalid = match mode {
            ServiceMode::Singleton => instance.instance.is_some(),
            ServiceMode::Keyed => instance.instance.is_none(),
        };
        if invalid {
            return Err(ChordError::error(
                "Remote service reset has an invalid instance address",
            ));
        }
        if let Some(address) = &instance.instance {
            if !keys.insert(address.key.as_str()) {
                return Err(ChordError::error(
                    "Remote service reset repeats an instance key",
                ));
            }
        }
        for member in &instance.members {
            if let ServiceMemberSnapshot::State { ops, .. } = member {
                if ops.len() != 1 || !ops[0].is_replace() {
                    return Err(ChordError::error(
                        "Remote service reset must contain full root replacements",
                    ));
                }
            }
        }
    }
    Ok(())
}

fn validate_members(
    members: &[ServiceMemberSnapshot],
) -> Result<&[ServiceMemberSnapshot], ChordError> {
    let mut names = HashSet::new();
    for member in members {
        if member.name().is_empty() || !names.insert(member.name()) {
            return Err(ChordError::error(
                "Remote service has invalid member descriptions",
            ));
        }
    }
    Ok(members)
}
