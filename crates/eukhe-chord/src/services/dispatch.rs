//! Explicit dispatch for remote service implementations.
//!
//! A TS remote service implementation is a plain object: the provider
//! enumerates its own properties (`Object.keys`), treats functions as remote
//! methods and replicated states as state members, and invokes methods with
//! `Reflect.apply(method, implementation, [...args, context])`. Rust has no
//! dynamic objects, so an implementation describes its members through
//! [`RemoteServiceObject::members`] and receives calls through
//! [`RemoteServiceObject::invoke`]: method name, JSON arguments, and the
//! trailing [`Context`], producing a JSON result (`None` for `undefined`).
//!
//! [`ServiceObject`] implements the trait from closures and states; a typed
//! service can implement it directly by matching on the method name.

use std::collections::BTreeMap;
use std::fmt;
use std::future::Future;
use std::sync::Arc;

use futures::future::BoxFuture;
use futures::FutureExt;

use crate::context::Context;
use crate::error::{BoxError, ChordError};
use crate::json::JsonValue;

use super::state_internals::ReplicatedStateRef;

/// The pending result of one remote method call; `None` is `undefined`.
pub type MethodFuture = BoxFuture<'static, Result<Option<JsonValue>, ChordError>>;

/// One own member of a service implementation.
#[derive(Clone, Debug)]
pub enum ServiceMember {
    /// A remote method, called through [`RemoteServiceObject::invoke`].
    Method,
    /// A replicated state published to subscribers.
    State(ReplicatedStateRef),
    /// Any other data property. Process-local services may carry it;
    /// remote services reject it as not remotely exposable.
    Value(JsonValue),
}

/// A remote service implementation: the explicit replacement for JS
/// dynamic property access and method calls.
///
/// Implementations return the same member names and kinds on every call to
/// [`members`](Self::members) and dispatch every [`ServiceMember::Method`]
/// name in [`invoke`](Self::invoke).
pub trait RemoteServiceObject: Send + Sync + 'static {
    /// The own members, by unique name, in any order.
    fn members(&self) -> Vec<(String, ServiceMember)>;

    /// Call method `member` with the business arguments and the trailing
    /// context. Chord only invokes names that [`members`](Self::members)
    /// reports as methods.
    fn invoke(&self, member: &str, args: Vec<JsonValue>, context: &Context) -> MethodFuture;
}

type MethodFn = Arc<dyn Fn(Vec<JsonValue>, Context) -> MethodFuture + Send + Sync>;

#[derive(Clone)]
enum ObjectMember {
    Method(MethodFn),
    State(ReplicatedStateRef),
    Value(JsonValue),
}

/// A [`RemoteServiceObject`] assembled from closures, states, and values,
/// like a TS object literal. A later member replaces an earlier one with
/// the same name.
#[derive(Clone, Default)]
pub struct ServiceObject {
    members: BTreeMap<String, ObjectMember>,
}

impl ServiceObject {
    /// An object without members.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add an async method `(args, context) -> result`.
    #[must_use]
    pub fn method<F, Fut, E>(mut self, name: &str, method: F) -> Self
    where
        F: Fn(Vec<JsonValue>, Context) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<Option<JsonValue>, E>> + Send + 'static,
        E: Into<BoxError>,
    {
        let method: MethodFn = Arc::new(move |args, context| {
            method(args, context)
                .map(|result| result.map_err(|error| ChordError::from(error.into())))
                .boxed()
        });
        self.members
            .insert(name.to_owned(), ObjectMember::Method(method));
        self
    }

    /// Add a replicated state member.
    #[must_use]
    pub fn state(mut self, name: &str, state: impl Into<ReplicatedStateRef>) -> Self {
        self.members
            .insert(name.to_owned(), ObjectMember::State(state.into()));
        self
    }

    /// Add a plain data member (not remotely exposable).
    #[must_use]
    pub fn value(mut self, name: &str, value: JsonValue) -> Self {
        self.members
            .insert(name.to_owned(), ObjectMember::Value(value));
        self
    }

    /// Share as a trait object.
    #[must_use]
    pub fn into_object(self) -> Arc<dyn RemoteServiceObject> {
        Arc::new(self)
    }
}

impl fmt::Debug for ServiceObject {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_set().entries(self.members.keys()).finish()
    }
}

impl RemoteServiceObject for ServiceObject {
    fn members(&self) -> Vec<(String, ServiceMember)> {
        self.members
            .iter()
            .map(|(name, member)| {
                let member = match member {
                    ObjectMember::Method(_) => ServiceMember::Method,
                    ObjectMember::State(state) => ServiceMember::State(state.clone()),
                    ObjectMember::Value(value) => ServiceMember::Value(value.clone()),
                };
                (name.clone(), member)
            })
            .collect()
    }

    fn invoke(&self, member: &str, args: Vec<JsonValue>, context: &Context) -> MethodFuture {
        match self.members.get(member) {
            Some(ObjectMember::Method(method)) => method(args, context.clone()),
            Some(ObjectMember::State(_) | ObjectMember::Value(_)) | None => futures::future::ready(
                Err(ChordError::type_error("Service member is not callable")),
            )
            .boxed(),
        }
    }
}

impl From<ServiceObject> for Arc<dyn RemoteServiceObject> {
    fn from(object: ServiceObject) -> Self {
        Arc::new(object)
    }
}
