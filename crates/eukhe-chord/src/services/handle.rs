//! Host-owned service slots and consumer-owned guarded views (port of
//! `services/handle.ts`).
//!
//! TS hands consumers JS proxies that re-resolve every property access
//! through the slot, so a retained handle follows provider replacement and
//! rejects use once its owner revokes access. Rust consumers hold a
//! [`ServiceHandle`]; every [`ServiceHandle::member`] lookup and every
//! operation on a [`ServiceMemberHandle`] re-resolves the same way.
//!
//! Process-local implementations are typed values: read them with
//! [`ServiceHandle::get`] on each use. Remote services (and local services
//! implemented by a [`RemoteServiceObject`]) are used through member
//! handles: [`ServiceMemberHandle::call`] for methods and
//! [`ServiceMemberHandle::value`] / [`ServiceMemberHandle::subscribe`] for
//! replicated states.

use std::any::Any;
use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use crate::callback::Disposer;
use crate::context::Context;
use crate::error::ChordError;
use crate::json::JsonValue;
use crate::types::StateListener;

use super::consumer::{MemberSlot, ServiceFacade};
use super::dispatch::{MethodFuture, RemoteServiceObject, ServiceMember};

/// A TS `assertAccess(): void` guard: fails when a handle may not be used.
pub type AccessGuard = Arc<dyn Fn() -> Result<(), ChordError> + Send + Sync>;

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// What a slot is bound to.
#[derive(Clone)]
pub(crate) enum SlotTarget {
    /// A typed process-local implementation.
    Local(Arc<dyn Any + Send + Sync>),
    /// A process-local implementation described by members.
    Object(Arc<dyn RemoteServiceObject>),
    /// A remote service facade.
    Facade(ServiceFacade),
    /// Another guarded view (a keyed observation re-scoped by the host).
    View(ServiceView),
}

/// Host-owned mutable target with consumer-owned guarded views.
pub(crate) struct ServiceSlot {
    service_id: Arc<str>,
    wrap_objects: bool,
    target: Mutex<Option<SlotTarget>>,
}

impl ServiceSlot {
    /// `wrap_objects`: whether member objects re-resolve on every access
    /// (remotely exposable services) or are returned as they are.
    pub(crate) fn new(service_id: &str, wrap_objects: WrapObjects) -> Arc<Self> {
        Arc::new(Self {
            service_id: Arc::from(service_id),
            wrap_objects: matches!(wrap_objects, WrapObjects::Wrap),
            target: Mutex::new(None),
        })
    }

    pub(crate) fn view(self: &Arc<Self>, assert_access: AccessGuard) -> ServiceView {
        ServiceView {
            inner: Arc::new(ViewInner {
                slot: Arc::clone(self),
                assert_access,
                members: Mutex::new(HashMap::new()),
            }),
        }
    }

    pub(crate) fn bind(&self, target: SlotTarget) {
        *lock(&self.target) = Some(target);
    }

    pub(crate) fn unbind(&self) {
        *lock(&self.target) = None;
    }

    fn resolve(&self, assert_access: &AccessGuard) -> Result<SlotTarget, ChordError> {
        assert_access()?;
        lock(&self.target).clone().ok_or_else(|| {
            ChordError::error(format!("Service {} is disconnected", self.service_id))
        })
    }
}

/// Whether a slot wraps member objects (see [`ServiceSlot::new`]).
#[derive(Clone, Copy, Debug)]
pub(crate) enum WrapObjects {
    /// Remotely exposable services: every member re-resolves.
    Wrap,
    /// Process-local services: only methods re-resolve.
    Plain,
}

/// One consumer's guarded view of a slot.
#[derive(Clone)]
pub(crate) struct ServiceView {
    inner: Arc<ViewInner>,
}

struct ViewInner {
    slot: Arc<ServiceSlot>,
    assert_access: AccessGuard,
    members: Mutex<HashMap<String, ServiceMemberHandle>>,
}

impl ServiceView {
    fn resolve(&self) -> Result<SlotTarget, ChordError> {
        self.inner.slot.resolve(&self.inner.assert_access)
    }

    fn member(&self, name: &str) -> Result<ServiceMemberHandle, ChordError> {
        let current = self.resolve()?;
        if let SlotTarget::Object(object) = &current {
            if !self.inner.slot.wrap_objects && !is_method(object.as_ref(), name) {
                // A local non-method member is returned as it is.
                return Ok(ServiceMemberHandle {
                    kind: MemberKind::Object(Arc::new(ObjectMember {
                        object: Arc::clone(object),
                        name: Arc::from(name),
                    })),
                });
            }
        }
        let mut members = lock(&self.inner.members);
        Ok(members
            .entry(name.to_owned())
            .or_insert_with(|| ServiceMemberHandle {
                kind: MemberKind::View(Arc::new(ViewMember {
                    slot: Arc::clone(&self.inner.slot),
                    assert_access: Arc::clone(&self.inner.assert_access),
                    name: Arc::from(name),
                })),
            })
            .clone())
    }

    fn get<T: Clone + 'static>(&self) -> Result<T, ChordError> {
        match self.resolve()? {
            SlotTarget::Local(value) => value
                .downcast_ref::<T>()
                .cloned()
                .ok_or_else(|| self.not_local()),
            SlotTarget::View(view) => view.get(),
            SlotTarget::Object(_) | SlotTarget::Facade(_) => Err(self.not_local()),
        }
    }

    fn not_local(&self) -> ChordError {
        ChordError::type_error(format!(
            "Service {} has no process-local implementation of the requested type",
            self.inner.slot.service_id
        ))
    }
}

fn is_method(object: &dyn RemoteServiceObject, name: &str) -> bool {
    object
        .members()
        .iter()
        .any(|(candidate, member)| candidate == name && matches!(member, ServiceMember::Method))
}

/// A consumer's handle to one service: a remote facade or a guarded view.
/// Clones are the same handle.
#[derive(Clone)]
pub struct ServiceHandle {
    kind: HandleKind,
}

#[derive(Clone)]
enum HandleKind {
    Facade(ServiceFacade),
    View(ServiceView),
}

impl ServiceHandle {
    pub(crate) fn facade(facade: ServiceFacade) -> Self {
        Self {
            kind: HandleKind::Facade(facade),
        }
    }

    pub(crate) fn view(view: ServiceView) -> Self {
        Self {
            kind: HandleKind::View(view),
        }
    }

    pub(crate) fn into_target(self) -> SlotTarget {
        match self.kind {
            HandleKind::Facade(facade) => SlotTarget::Facade(facade),
            HandleKind::View(view) => SlotTarget::View(view),
        }
    }

    /// The handle of member `name` (a TS property access).
    ///
    /// # Errors
    ///
    /// The owner revoked access or the service is disconnected.
    pub fn member(&self, name: &str) -> Result<ServiceMemberHandle, ChordError> {
        match &self.kind {
            HandleKind::Facade(facade) => Ok(ServiceMemberHandle {
                kind: MemberKind::Slot(facade.member(name)),
            }),
            HandleKind::View(view) => view.member(name),
        }
    }

    /// Call method `name` (`handle.name(...args, context)`).
    ///
    /// # Errors
    ///
    /// Synchronous TS throws: revoked access, a disconnected service, or a
    /// member used as the wrong kind. Remote failures arrive through the
    /// returned future.
    pub fn call(
        &self,
        name: &str,
        args: Vec<JsonValue>,
        context: &Context,
    ) -> Result<MethodFuture, ChordError> {
        self.member(name)?.call(args, context)
    }

    /// The value of state member `name` (`handle.name.value`).
    ///
    /// # Errors
    ///
    /// See [`ServiceMemberHandle::value`].
    pub fn state_value(&self, name: &str) -> Result<Option<JsonValue>, ChordError> {
        self.member(name)?.value()
    }

    /// The current process-local implementation.
    ///
    /// # Errors
    ///
    /// Revoked access, a disconnected service, or a remote or differently
    /// typed implementation.
    pub fn get<T: Clone + 'static>(&self) -> Result<T, ChordError> {
        match &self.kind {
            HandleKind::Facade(facade) => Err(ChordError::type_error(format!(
                "Service {} has no process-local implementation of the requested type",
                facade.service_id()
            ))),
            HandleKind::View(view) => view.get(),
        }
    }

    /// Whether both handles are the same handle (TS `toBe`).
    #[must_use]
    pub fn same(&self, other: &Self) -> bool {
        match (&self.kind, &other.kind) {
            (HandleKind::Facade(left), HandleKind::Facade(right)) => left.same(right),
            (HandleKind::View(left), HandleKind::View(right)) => {
                Arc::ptr_eq(&left.inner, &right.inner)
            }
            (HandleKind::Facade(_), HandleKind::View(_))
            | (HandleKind::View(_), HandleKind::Facade(_)) => false,
        }
    }
}

impl fmt::Debug for ServiceHandle {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            HandleKind::Facade(facade) => {
                write!(formatter, "ServiceHandle({})", facade.service_id())
            }
            HandleKind::View(view) => {
                write!(formatter, "ServiceHandle({})", view.inner.slot.service_id)
            }
        }
    }
}

/// A handle to one service member: a method, a replicated state, or (for
/// process-local implementations) a plain value. Clones are the same
/// handle.
#[derive(Clone)]
pub struct ServiceMemberHandle {
    kind: MemberKind,
}

#[derive(Clone)]
enum MemberKind {
    /// A remote facade member.
    Slot(Arc<MemberSlot>),
    /// A member re-resolved through a guarded view on every operation.
    View(Arc<ViewMember>),
    /// A member of a described local implementation.
    Object(Arc<ObjectMember>),
}

struct ViewMember {
    slot: Arc<ServiceSlot>,
    assert_access: AccessGuard,
    name: Arc<str>,
}

struct ObjectMember {
    object: Arc<dyn RemoteServiceObject>,
    name: Arc<str>,
}

/// A member resolved for one operation.
enum Resolved {
    Slot(Arc<MemberSlot>),
    Object(Arc<dyn RemoteServiceObject>, Arc<str>),
}

impl ViewMember {
    /// Re-resolve the member through the slot (TS `ValueView` resolver).
    fn resolve(&self) -> Result<Resolved, ChordError> {
        match self.slot.resolve(&self.assert_access)? {
            SlotTarget::Facade(facade) => Ok(Resolved::Slot(facade.member(&self.name))),
            SlotTarget::View(view) => view.member(&self.name)?.resolve(),
            SlotTarget::Object(object) => Ok(Resolved::Object(object, Arc::clone(&self.name))),
            SlotTarget::Local(_) => Err(ChordError::type_error(
                "Service member does not have properties",
            )),
        }
    }
}

impl ServiceMemberHandle {
    fn resolve(&self) -> Result<Resolved, ChordError> {
        match &self.kind {
            MemberKind::Slot(slot) => Ok(Resolved::Slot(Arc::clone(slot))),
            MemberKind::View(member) => member.resolve(),
            MemberKind::Object(member) => Ok(Resolved::Object(
                Arc::clone(&member.object),
                Arc::clone(&member.name),
            )),
        }
    }

    /// Call the method with its business arguments and trailing context.
    ///
    /// # Errors
    ///
    /// Synchronous TS throws: revoked access, a disconnected service, or a
    /// member that is not a method. Remote failures arrive through the
    /// returned future.
    pub fn call(
        &self,
        args: Vec<JsonValue>,
        context: &Context,
    ) -> Result<MethodFuture, ChordError> {
        match self.resolve()? {
            Resolved::Slot(slot) => slot.call(args, context),
            Resolved::Object(object, name) => {
                if is_method(object.as_ref(), &name) {
                    Ok(object.invoke(&name, args, context))
                } else {
                    Err(ChordError::type_error("Service member is not callable"))
                }
            }
        }
    }

    /// The replicated state's value; `None` until hydration.
    ///
    /// # Errors
    ///
    /// Revoked access, a disconnected service, or a member that is not a
    /// state.
    pub fn value(&self) -> Result<Option<JsonValue>, ChordError> {
        match self.resolve()? {
            Resolved::Slot(slot) => slot.value(),
            Resolved::Object(object, name) => match object_member(object.as_ref(), &name) {
                Some(ServiceMember::State(state)) => Ok(state.state.value()),
                Some(ServiceMember::Method) => Ok(None),
                Some(ServiceMember::Value(value)) => Ok(value.get("value").cloned()),
                None => Err(ChordError::type_error(
                    "Service member does not have properties",
                )),
            },
        }
    }

    /// Subscribe to the replicated state (see
    /// [`ReplicatedState::subscribe`](crate::ReplicatedState::subscribe)).
    ///
    /// # Errors
    ///
    /// Revoked access, a disconnected service, or a member that is not a
    /// state.
    pub fn subscribe(&self, listener: StateListener) -> Result<Disposer, ChordError> {
        match self.resolve()? {
            Resolved::Slot(slot) => slot.subscribe(listener),
            Resolved::Object(object, name) => match object_member(object.as_ref(), &name) {
                Some(ServiceMember::State(state)) => Ok(state.state.subscribe(listener)),
                Some(ServiceMember::Method | ServiceMember::Value(_)) | None => {
                    Err(ChordError::type_error("Service member is not callable"))
                }
            },
        }
    }

    /// Whether both handles are the same handle (TS `toBe`).
    #[must_use]
    pub fn same(&self, other: &Self) -> bool {
        match (&self.kind, &other.kind) {
            (MemberKind::Slot(left), MemberKind::Slot(right)) => Arc::ptr_eq(left, right),
            (MemberKind::View(left), MemberKind::View(right)) => Arc::ptr_eq(left, right),
            (MemberKind::Object(left), MemberKind::Object(right)) => Arc::ptr_eq(left, right),
            (MemberKind::Slot(_) | MemberKind::View(_) | MemberKind::Object(_), _) => false,
        }
    }
}

impl fmt::Debug for ServiceMemberHandle {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("ServiceMemberHandle")
    }
}

fn object_member(object: &dyn RemoteServiceObject, name: &str) -> Option<ServiceMember> {
    object
        .members()
        .into_iter()
        .find_map(|(candidate, member)| (candidate == name).then_some(member))
}
