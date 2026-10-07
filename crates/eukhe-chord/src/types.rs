//! Public contracts shared by replicated state, services, and facets (port of
//! `types.ts`).
//!
//! `Context` and `ContextKey` live in [`crate::context`]; `JsonValue` lives
//! in [`crate::json`]. The TS compile-time contract checks
//! (`JsonRepresentation`, `RemoteServiceContract`) have no Rust counterpart:
//! remote values are [`JsonValue`]s by construction.

use std::fmt;
use std::marker::PhantomData;
use std::sync::Arc;

use futures::future::BoxFuture;

use crate::callback::{Disposer, Outcome};
use crate::context::Context;
use crate::delta::Op;
use crate::error::{BoxError, ChordError, ErrorReporter};
use crate::json::JsonValue;

/// Whether a delivery hydrates a subscriber or updates it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DeliveryKind {
    /// `"hydrate"`: the subscriber's first value.
    Hydrate,
    /// `"update"`: a later revision.
    Update,
}

impl DeliveryKind {
    /// The TS string.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Hydrate => "hydrate",
            Self::Update => "update",
        }
    }
}

/// How one value reached a subscriber.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ReplicatedStateDelivery {
    /// Hydration or update.
    pub kind: DeliveryKind,
    /// The publication sequence of the delivered value.
    pub sequence: u64,
}

/// A replicated state subscription callback: `(value, context, delivery)`.
#[derive(Clone)]
pub struct StateListener {
    listener: Arc<dyn Fn(JsonValue, Context, ReplicatedStateDelivery) -> Outcome + Send + Sync>,
}

impl StateListener {
    /// Wrap a listener. Returning [`Outcome::Pending`] suspends this
    /// subscription until the future settles.
    pub fn new<F, R>(listener: F) -> Self
    where
        F: Fn(JsonValue, Context, ReplicatedStateDelivery) -> R + Send + Sync + 'static,
        R: Into<Outcome>,
    {
        Self {
            listener: Arc::new(move |value, context, delivery| {
                listener(value, context, delivery).into()
            }),
        }
    }

    pub(crate) fn call(
        &self,
        value: JsonValue,
        context: Context,
        delivery: ReplicatedStateDelivery,
    ) -> Outcome {
        (self.listener)(value, context, delivery)
    }
}

impl fmt::Debug for StateListener {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("StateListener")
    }
}

/// A readable, subscribable replicated JSON value.
pub trait ReplicatedState: Send + Sync {
    /// Contract-immutable value, or `None` until hydration. Later updates do
    /// not change previously returned values.
    fn value(&self) -> Option<JsonValue>;

    /// Each subscription serializes callbacks, awaiting hydration before
    /// updates. At most 100 deliveries wait behind the running callback;
    /// overflow keeps only the newest pending value/context/delivery, so
    /// update sequences may skip. Failures are reported in isolation and
    /// delivery continues. Disposing discards pending work without aborting
    /// or joining a running callback.
    fn subscribe(&self, listener: StateListener) -> Disposer;
}

/// One immutable authoritative revision committed after an attachment
/// snapshot.
#[derive(Clone, Debug)]
pub struct ReplicatedStateSourceFrame {
    /// Monotonic source cursor. The first frame after a snapshot must be
    /// `snapshot.cursor + 1`.
    pub cursor: i64,
    /// The exact immutable value produced by this commit.
    pub value: JsonValue,
    /// The exact immutable operation batch that produced `value` from the
    /// preceding source revision. Chord republishes this reference.
    pub ops: Arc<[Op]>,
    /// The commit's context.
    pub context: Context,
}

/// The fixed snapshot captured at an attachment boundary.
#[derive(Clone, Debug, PartialEq)]
pub struct ReplicatedStateSourceSnapshot {
    /// The immutable value at the boundary.
    pub value: JsonValue,
    /// The source cursor of that value.
    pub cursor: i64,
}

/// The sole frame listener installed on an attachment.
pub type SourceFrameListener = Arc<dyn Fn(ReplicatedStateSourceFrame) + Send + Sync>;

/// One atomic attachment to a [`ReplicatedStateSource`].
pub trait ReplicatedStateSourceAttachment: Send + Sync {
    /// The fixed immutable snapshot captured at the atomic attachment
    /// boundary. Every call returns the same snapshot.
    fn snapshot(&self) -> ReplicatedStateSourceSnapshot;

    /// Install the sole listener and synchronously drain every buffered
    /// frame in source commit order. Single-use. After it begins, every new
    /// committed frame must also be delivered in order until disposal,
    /// including commits made reentrantly while a prior frame is being
    /// delivered.
    ///
    /// # Errors
    ///
    /// A failure aborts the attachment.
    fn activate(&self, listener: SourceFrameListener) -> Result<(), BoxError>;

    /// Stop delivery and release source resources. Must be idempotent.
    ///
    /// # Errors
    ///
    /// A failure is reported together with the failure that caused disposal.
    fn dispose(&self) -> Result<(), BoxError>;
}

/// An authoritative immutable revision source.
///
/// `attach()` must synchronously and atomically capture one snapshot and
/// register the returned attachment to buffer every later committed frame.
/// The snapshot must include every commit before that boundary; buffered
/// frames must include every commit after it, with no overlap or gap.
/// Snapshot values, frame values, and operation batches are immutable and
/// remain valid after delivery. Chord only publishes these references; it
/// never applies or re-diffs them.
pub trait ReplicatedStateSource: Send + Sync {
    /// Capture a snapshot and buffer later frames.
    ///
    /// # Errors
    ///
    /// A failure is returned to the attaching caller.
    fn attach(&self) -> Result<Box<dyn ReplicatedStateSourceAttachment>, BoxError>;
}

/// Options for [`crate::replicated_state_from_source`].
#[derive(Clone, Default)]
pub struct ReplicatedStateSourceOptions {
    /// Receives source-contract and publication-listener failures without
    /// throwing them into the source. Defaults to logging them as uncaught.
    pub on_error: Option<ErrorReporter>,
}

impl fmt::Debug for ReplicatedStateSourceOptions {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ReplicatedStateSourceOptions")
            .field("on_error", &self.on_error.is_some())
            .finish()
    }
}

/// The untyped identity of a service contract: `{ id, local }`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ServiceToken {
    id: Arc<str>,
    local: bool,
}

impl ServiceToken {
    pub(crate) fn new(id: &str, local: bool) -> Self {
        Self {
            id: Arc::from(id),
            local,
        }
    }

    /// The service ID.
    #[must_use]
    pub fn id(&self) -> &str {
        &self.id
    }

    /// Process-local services accept unrestricted implementations and are
    /// never published remotely.
    #[must_use]
    pub fn local(&self) -> bool {
        self.local
    }
}

impl AsRef<ServiceToken> for ServiceToken {
    fn as_ref(&self) -> &ServiceToken {
        self
    }
}

/// Stable identity for one shared service contract. `T` documents the
/// contract; a process-local service's implementation value has type `T`
/// (see [`crate::ServiceHandle::get`]).
pub struct Service<T> {
    token: ServiceToken,
    contract: PhantomData<fn(T) -> T>,
}

impl<T> Service<T> {
    pub(crate) fn new(token: ServiceToken) -> Self {
        Self {
            token,
            contract: PhantomData,
        }
    }

    /// The service ID.
    #[must_use]
    pub fn id(&self) -> &str {
        self.token.id()
    }

    /// Whether the service is process-local.
    #[must_use]
    pub fn local(&self) -> bool {
        self.token.local()
    }

    /// The untyped identity.
    #[must_use]
    pub fn token(&self) -> &ServiceToken {
        &self.token
    }
}

impl<T> Clone for Service<T> {
    fn clone(&self) -> Self {
        Self::new(self.token.clone())
    }
}

impl<T> fmt::Debug for Service<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("Service")
            .field("id", &self.token.id)
            .field("local", &self.token.local)
            .finish()
    }
}

impl<T> AsRef<ServiceToken> for Service<T> {
    fn as_ref(&self) -> &ServiceToken {
        &self.token
    }
}

/// How a service is provided: one singleton or keyed instances.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ServiceMode {
    /// `"singleton"`.
    Singleton,
    /// `"keyed"`.
    Keyed,
}

impl ServiceMode {
    /// The wire string.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Singleton => "singleton",
            Self::Keyed => "keyed",
        }
    }

    /// Parse a wire string.
    #[must_use]
    pub fn parse(value: &str) -> Option<Self> {
        match value {
            "singleton" => Some(Self::Singleton),
            "keyed" => Some(Self::Keyed),
            _ => None,
        }
    }
}

impl fmt::Display for ServiceMode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

/// One published service.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ServiceCatalogueEntry {
    /// The service ID.
    pub service_id: String,
    /// Its mode.
    pub mode: ServiceMode,
}

/// The address of one keyed instance incarnation.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ServiceInstanceAddress {
    /// The non-empty instance key.
    pub key: String,
    /// The incarnation of that key, from 1.
    pub generation: u64,
}

/// One member of a service instance snapshot. `O` is [`Op`] for decoded
/// values and [`WireOp`](crate::delta::WireOp) on the wire.
#[derive(Clone, Debug, PartialEq)]
pub enum ServiceMemberSnapshot<O = Op> {
    /// `{ name, kind: "method" }`.
    Method {
        /// The member name.
        name: String,
    },
    /// `{ name, kind: "state", sequence, ops }`.
    State {
        /// The member name.
        name: String,
        /// The publication sequence of the snapshot value.
        sequence: u64,
        /// A base batch (a root replacement) producing the value.
        ops: Arc<[O]>,
    },
}

impl<O> ServiceMemberSnapshot<O> {
    /// The member name.
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::Method { name } | Self::State { name, .. } => name,
        }
    }
}

/// One instance's members.
#[derive(Clone, Debug, PartialEq)]
pub struct ServiceInstanceSnapshot<O = Op> {
    /// The keyed address; `None` for a singleton.
    pub instance: Option<ServiceInstanceAddress>,
    /// The members in name order.
    pub members: Vec<ServiceMemberSnapshot<O>>,
}

/// The atomic baseline of one service subscription.
#[derive(Clone, Debug, PartialEq)]
pub struct ServiceSubscriptionSnapshot<O = Op> {
    /// The service ID.
    pub service_id: String,
    /// Its mode.
    pub mode: ServiceMode,
    /// The live instances; keyed instances are sorted by key.
    pub instances: Vec<ServiceInstanceSnapshot<O>>,
}

/// One update delivered to a service subscription.
#[derive(Clone, Debug, PartialEq)]
pub enum ServiceProviderUpdate<O = Op> {
    /// One state member's exact operation batch.
    State {
        /// The keyed address; `None` for a singleton.
        instance: Option<ServiceInstanceAddress>,
        /// The state member.
        member: String,
        /// The publication sequence.
        sequence: u64,
        /// The operations from the previous sequence.
        ops: Arc<[O]>,
    },
    /// Full subscription rebaseline after overflow; every state is a root
    /// replacement at its new sequence.
    Reset {
        /// The new baseline.
        snapshot: ServiceSubscriptionSnapshot<O>,
    },
    /// The singleton provider was withdrawn.
    Unavailable,
    /// The singleton provider was replaced.
    Replaced {
        /// The replacement's members.
        snapshot: ServiceInstanceSnapshot<O>,
    },
    /// A keyed instance was spawned.
    Spawned {
        /// The new instance.
        instance: ServiceInstanceSnapshot<O>,
    },
    /// A keyed instance was closed.
    Closed {
        /// Its address.
        instance: ServiceInstanceAddress,
    },
}

impl<O> ServiceProviderUpdate<O> {
    /// The TS `type` discriminant.
    #[must_use]
    pub fn kind(&self) -> &'static str {
        match self {
            Self::State { .. } => "state",
            Self::Reset { .. } => "reset",
            Self::Unavailable => "unavailable",
            Self::Replaced { .. } => "replaced",
            Self::Spawned { .. } => "spawned",
            Self::Closed { .. } => "closed",
        }
    }
}

/// One method invocation.
#[derive(Clone, Debug, PartialEq)]
pub struct ServiceCall {
    /// The service ID.
    pub service_id: String,
    /// The keyed address; `None` for a singleton.
    pub instance: Option<ServiceInstanceAddress>,
    /// The method name.
    pub member: String,
    /// Borrowed immutable values. Chord validates but does not clone them.
    pub args: Vec<JsonValue>,
}

/// Receives a subscription's updates. A failure is collected by the
/// provider and returned to whoever published the update.
pub type ServiceUpdateListener =
    Arc<dyn Fn(ServiceProviderUpdate, &Context) -> Result<(), ChordError> + Send + Sync>;

/// One service subscription.
pub trait ServiceSubscription: Send + Sync {
    /// Atomic baseline. Later updates buffer until activation, with a full
    /// reset on pending delivery 101.
    fn snapshot(&self) -> &ServiceSubscriptionSnapshot;

    /// Start delivering buffered and later updates.
    ///
    /// # Errors
    ///
    /// Listener failures while replaying buffered updates.
    fn activate(&self) -> Result<(), ChordError>;

    /// Stop delivery (TS `close(context?): void | Promise<void>`).
    fn close(&self, context: &Context) -> BoxFuture<'static, Result<(), ChordError>>;
}

/// Pluggable wire boundary consumed by a remote service binding.
///
/// Implementations choose transport, framing, routing, and envelope
/// encoding. Values crossing this boundary must remain strict JSON. Chord
/// does not clone values or require a particular application wire protocol;
/// adapters own serialization and any isolation copies they require.
pub trait RemoteServiceTransport: Send + Sync {
    /// Invoke one method; `None` is a TS `undefined` result.
    fn invoke(
        &self,
        call: ServiceCall,
        context: &Context,
    ) -> BoxFuture<'static, Result<Option<JsonValue>, ChordError>>;

    /// Open one subscription delivering updates to `listener`.
    fn subscribe(
        &self,
        service_id: &str,
        mode: ServiceMode,
        listener: ServiceUpdateListener,
        context: &Context,
    ) -> BoxFuture<'static, Result<Box<dyn ServiceSubscription>, ChordError>>;
}
