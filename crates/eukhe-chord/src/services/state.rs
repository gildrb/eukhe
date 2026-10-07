//! Replicated state: authoritative mutable state, publication-only states
//! attached to an external source, and cold consumer replicas (port of
//! `services/state.ts`).
//!
//! # Threads
//!
//! TS runs on one thread and serializes publication by reentrancy alone.
//! Here every state guards its bookkeeping with a mutex that is never held
//! while application code runs. A commit and the enqueueing of its
//! publication happen atomically, and exactly one caller at a time drains
//! the publication queue; a publication enqueued meanwhile (reentrantly or
//! from another thread) is delivered by that caller, in sequence order.

use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};
use std::thread::{self, ThreadId};

use crate::callback::{Disposer, Outcome};
use crate::context::{Context, BACKGROUND_CONTEXT};
use crate::delta::{apply_immutable, is_base, track, Draft, Op, Tracker};
use crate::error::{
    collected, uncaught_reporter, AggregateError, BoxError, ChordError, ErrorReporter,
};
use crate::json::JsonValue;
use crate::task::spawn_detached;
use crate::types::{
    DeliveryKind, ReplicatedState, ReplicatedStateDelivery, ReplicatedStateSource,
    ReplicatedStateSourceAttachment, ReplicatedStateSourceFrame, ReplicatedStateSourceOptions,
    StateListener,
};

use super::state_internals::{
    ReplicatedStateInternals, ReplicatedStateRef, ReplicatedStateSnapshot, SourceListener,
};

/// The most deliveries that wait behind a running subscription callback.
const PENDING_LIMIT: usize = 100;

/// `Number.MAX_SAFE_INTEGER`.
const MAX_SAFE_CURSOR: u64 = (1 << 53) - 1;

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

#[derive(Clone)]
struct StateDelivery {
    value: JsonValue,
    context: Context,
    delivery: ReplicatedStateDelivery,
}

#[derive(Default)]
struct SubscriberQueue {
    pending: VecDeque<StateDelivery>,
    running: bool,
    started: bool,
    closed: bool,
}

/// One public subscription, independent of producer and other subscriber
/// progress.
#[derive(Clone)]
struct StateSubscriber {
    inner: Arc<SubscriberInner>,
}

struct SubscriberInner {
    listener: StateListener,
    report: ErrorReporter,
    queue: Mutex<SubscriberQueue>,
}

impl StateSubscriber {
    fn new(listener: StateListener, report: ErrorReporter) -> Self {
        Self {
            inner: Arc::new(SubscriberInner {
                listener,
                report,
                queue: Mutex::new(SubscriberQueue::default()),
            }),
        }
    }

    fn same(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }

    fn push(&self, frame: StateDelivery) {
        let mut queue = lock(&self.inner.queue);
        if queue.closed {
            return;
        }
        if queue.pending.len() == PENDING_LIMIT {
            // A cold replica can queue updates reentrantly before this
            // subscriber's first hydration starts.
            let hydration = if queue.started {
                None
            } else {
                queue.pending.pop_front()
            };
            queue.pending.clear();
            if let Some(hydration) = hydration {
                queue.pending.push_back(hydration);
            }
        }
        queue.pending.push_back(frame);
    }

    fn drain(&self) {
        {
            let mut queue = lock(&self.inner.queue);
            if queue.running || queue.closed {
                return;
            }
            queue.running = true;
        }
        loop {
            let frame = {
                let mut queue = lock(&self.inner.queue);
                let Some(frame) = queue.pending.pop_front() else {
                    queue.running = false;
                    return;
                };
                queue.started = true;
                frame
            };
            match self
                .inner
                .listener
                .call(frame.value, frame.context, frame.delivery)
            {
                Outcome::Done => {}
                Outcome::Failed(error) => (self.inner.report)(error),
                Outcome::Pending(future) => {
                    let subscriber = self.clone();
                    spawn_detached(async move {
                        if let Err(error) = future.await {
                            (subscriber.inner.report)(error);
                        }
                        subscriber.resume();
                    });
                    return;
                }
            }
        }
    }

    fn clear(&self) {
        lock(&self.inner.queue).pending.clear();
    }

    fn close(&self) {
        let mut queue = lock(&self.inner.queue);
        queue.closed = true;
        queue.pending.clear();
    }

    fn resume(&self) {
        lock(&self.inner.queue).running = false;
        self.drain();
    }
}

#[derive(Clone)]
struct Publication {
    value: JsonValue,
    ops: Arc<[Op]>,
    sequence: u64,
    context: Context,
}

struct PublisherState {
    listeners: Vec<(StateSubscriber, u64)>,
    source_listeners: Vec<(u64, SourceListener)>,
    publications: VecDeque<Publication>,
    value: JsonValue,
    sequence: u64,
    delivering: bool,
    next_source_listener: u64,
}

/// Maintains local publication order independently of how revisions are
/// produced.
struct ReplicatedStatePublisher {
    state: Mutex<PublisherState>,
    report: ErrorReporter,
}

impl ReplicatedStatePublisher {
    fn new(initial: JsonValue, report: ErrorReporter) -> Self {
        Self {
            state: Mutex::new(PublisherState {
                listeners: Vec::new(),
                source_listeners: Vec::new(),
                publications: VecDeque::new(),
                value: initial,
                sequence: 0,
                delivering: false,
                next_source_listener: 0,
            }),
            report,
        }
    }

    fn value(&self) -> JsonValue {
        lock(&self.state).value.clone()
    }

    fn snapshot(&self) -> ReplicatedStateSnapshot {
        let state = lock(&self.state);
        ReplicatedStateSnapshot {
            value: state.value.clone(),
            sequence: state.sequence,
        }
    }

    fn subscribe(self: &Arc<Self>, listener: StateListener) -> Disposer {
        let subscriber = StateSubscriber::new(listener, Arc::clone(&self.report));
        {
            let mut state = lock(&self.state);
            let sequence = state.sequence;
            state.listeners.push((subscriber.clone(), sequence));
            subscriber.push(StateDelivery {
                value: state.value.clone(),
                context: service_delivery_context(),
                delivery: ReplicatedStateDelivery {
                    kind: DeliveryKind::Hydrate,
                    sequence,
                },
            });
        }
        subscriber.drain();
        let publisher = Arc::downgrade(self);
        Disposer::new(move || {
            subscriber.close();
            if let Some(publisher) = publisher.upgrade() {
                lock(&publisher.state)
                    .listeners
                    .retain(|(candidate, _)| !candidate.same(&subscriber));
            }
        })
    }

    fn subscribe_source(self: &Arc<Self>, listener: SourceListener) -> Disposer {
        let id = {
            let mut state = lock(&self.state);
            let id = state.next_source_listener;
            state.next_source_listener += 1;
            state.source_listeners.push((id, listener));
            id
        };
        let publisher = Arc::downgrade(self);
        Disposer::new(move || {
            if let Some(publisher) = publisher.upgrade() {
                lock(&publisher.state)
                    .source_listeners
                    .retain(|(candidate, _)| *candidate != id);
            }
        })
    }

    /// Record an already-prepared immutable revision. Returns whether the
    /// caller must [`deliver`](Self::deliver) it: false while another caller
    /// is delivering, which then delivers this publication too.
    fn enqueue(&self, value: JsonValue, ops: Arc<[Op]>, context: Context) -> bool {
        let mut state = lock(&self.state);
        state.value = value.clone();
        state.sequence += 1;
        let sequence = state.sequence;
        state.publications.push_back(Publication {
            value,
            ops,
            sequence,
            context,
        });
        if state.delivering {
            return false;
        }
        state.delivering = true;
        true
    }

    /// Deliver queued publications and return isolated listener failures.
    fn deliver(&self) -> Vec<ChordError> {
        struct Delivering<'a>(&'a Mutex<PublisherState>);
        impl Drop for Delivering<'_> {
            fn drop(&mut self) {
                if thread::panicking() {
                    lock(self.0).delivering = false;
                }
            }
        }
        let _guard = Delivering(&self.state);
        let mut errors = Vec::new();
        loop {
            let (publication, source_listeners, listeners) = {
                let mut state = lock(&self.state);
                let Some(publication) = state.publications.pop_front() else {
                    state.delivering = false;
                    return errors;
                };
                let source_listeners: Vec<SourceListener> = state
                    .source_listeners
                    .iter()
                    .map(|(_, listener)| Arc::clone(listener))
                    .collect();
                (publication, source_listeners, state.listeners.clone())
            };
            for listener in source_listeners {
                if let Err(error) =
                    listener(&publication.ops, publication.sequence, &publication.context)
                {
                    errors.push(error);
                }
            }
            let delivery = ReplicatedStateDelivery {
                kind: DeliveryKind::Update,
                sequence: publication.sequence,
            };
            for (subscriber, hydrated_sequence) in listeners {
                if publication.sequence <= hydrated_sequence {
                    continue;
                }
                subscriber.push(StateDelivery {
                    value: publication.value.clone(),
                    context: publication.context.clone(),
                    delivery,
                });
                subscriber.drain();
            }
        }
    }

    /// Publish one revision and return isolated listener failures.
    fn publish(&self, value: JsonValue, ops: Arc<[Op]>, context: Context) -> Vec<ChordError> {
        if self.enqueue(value, ops, context) {
            self.deliver()
        } else {
            Vec::new()
        }
    }
}

impl ReplicatedStateInternals for Arc<ReplicatedStatePublisher> {
    fn snapshot(&self) -> ReplicatedStateSnapshot {
        ReplicatedStatePublisher::snapshot(self)
    }

    fn subscribe(&self, listener: SourceListener) -> Disposer {
        self.subscribe_source(listener)
    }
}

/// Create authoritative state by taking immutable ownership of a JSON object
/// or array root.
///
/// # Errors
///
/// [`TrackerError::RootNotContainer`](crate::delta::TrackerError) when
/// `initial` is not an object or array (the TS `T extends object`).
pub fn replicated_state(initial: JsonValue) -> Result<MutableReplicatedState, ChordError> {
    MutableReplicatedState::new(initial)
}

/// Authoritative replicated state changed through atomic overlay drafts.
#[derive(Clone)]
pub struct MutableReplicatedState {
    inner: Arc<MutableInner>,
}

struct MutableInner {
    tracker: Tracker,
    publisher: Arc<ReplicatedStatePublisher>,
    /// Serializes commits from different threads.
    commit: Mutex<()>,
    /// The thread running a change callback, to reject reentrant commits.
    changing: Mutex<Option<ThreadId>>,
}

/// Clears the changing thread when a change callback settles or unwinds.
struct ChangingGuard<'a>(&'a Mutex<Option<ThreadId>>);

impl Drop for ChangingGuard<'_> {
    fn drop(&mut self) {
        *lock(self.0) = None;
    }
}

impl MutableReplicatedState {
    fn new(initial: JsonValue) -> Result<Self, ChordError> {
        let tracker = track(initial)?;
        let publisher = Arc::new(ReplicatedStatePublisher::new(
            tracker.value(),
            uncaught_reporter(),
        ));
        Ok(Self {
            inner: Arc::new(MutableInner {
                tracker,
                publisher,
                commit: Mutex::new(()),
                changing: Mutex::new(None),
            }),
        })
    }

    /// The latest committed immutable value.
    #[must_use]
    pub fn value(&self) -> JsonValue {
        self.inner.tracker.value()
    }

    /// Atomically publish one synchronous overlay mutation. Draft handles are
    /// unusable after the callback returns. Values placed through the draft
    /// are copied by value.
    ///
    /// # Errors
    ///
    /// A reentrant change, the callback's own failure, or a draft failure
    /// rolls the change back and is returned. Listener failures are returned
    /// after the revision is committed and published.
    pub fn change<F, E>(&self, context: &Context, mutate: F) -> Result<(), ChordError>
    where
        F: FnOnce(Draft) -> Result<(), E>,
        E: Into<BoxError>,
    {
        let current = thread::current().id();
        if *lock(&self.inner.changing) == Some(current) {
            return Err(ChordError::error(
                "Replicated state cannot be changed reentrantly from a change callback",
            ));
        }
        let deliver = {
            let _commit = lock(&self.inner.commit);
            let prepared = {
                *lock(&self.inner.changing) = Some(current);
                let _changing = ChangingGuard(&self.inner.changing);
                let change = self.inner.tracker.begin_change();
                let attempt = change
                    .state()
                    .map_err(ChordError::from)
                    .and_then(|draft| mutate(draft).map_err(|error| ChordError::from(error.into())))
                    .and_then(|()| change.prepare().map_err(ChordError::from));
                match attempt {
                    Ok(prepared) => prepared,
                    Err(error) => {
                        change.abort();
                        return Err(error);
                    }
                }
            };
            self.inner.tracker.adopt(&prepared)?;
            if prepared.ops().is_empty() {
                return Ok(());
            }
            self.inner.publisher.enqueue(
                prepared.value().clone(),
                Arc::from(prepared.ops()),
                context.clone(),
            )
        };
        if !deliver {
            return Ok(());
        }
        collected(
            self.inner.publisher.deliver(),
            "Replicated state listeners failed",
        )
    }

    /// Atomically take immutable ownership of a replacement root. A deeply
    /// equal replacement publishes nothing.
    ///
    /// # Errors
    ///
    /// Replacing from a change callback, a non-container root, or listener
    /// failures (returned after the revision is published).
    pub fn replace(&self, context: &Context, value: JsonValue) -> Result<(), ChordError> {
        if *lock(&self.inner.changing) == Some(thread::current().id()) {
            return Err(ChordError::error(
                "Replicated state cannot be replaced from a change callback",
            ));
        }
        let deliver = {
            let _commit = lock(&self.inner.commit);
            let prepared = self.inner.tracker.prepare_replace(value)?;
            self.inner.tracker.adopt(&prepared)?;
            if prepared.ops().is_empty() {
                return Ok(());
            }
            self.inner.publisher.enqueue(
                prepared.value().clone(),
                Arc::from(prepared.ops()),
                context.clone(),
            )
        };
        if !deliver {
            return Ok(());
        }
        collected(
            self.inner.publisher.deliver(),
            "Replicated state listeners failed",
        )
    }

    /// Subscribe with a closure (see [`ReplicatedState::subscribe`]).
    pub fn subscribe<F, R>(&self, listener: F) -> Disposer
    where
        F: Fn(JsonValue, Context, ReplicatedStateDelivery) -> R + Send + Sync + 'static,
        R: Into<Outcome>,
    {
        self.inner.publisher.subscribe(StateListener::new(listener))
    }

    /// The handle a remote service uses to expose this state as a member.
    #[must_use]
    pub fn state_ref(&self) -> ReplicatedStateRef {
        ReplicatedStateRef {
            internals: Arc::new(Arc::clone(&self.inner.publisher)),
            state: Arc::new(self.clone()),
        }
    }

    /// Whether both handles are the same state.
    #[must_use]
    pub fn same(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl ReplicatedState for MutableReplicatedState {
    fn value(&self) -> Option<JsonValue> {
        Some(MutableReplicatedState::value(self))
    }

    fn subscribe(&self, listener: StateListener) -> Disposer {
        self.inner.publisher.subscribe(listener)
    }
}

impl From<&MutableReplicatedState> for ReplicatedStateRef {
    fn from(state: &MutableReplicatedState) -> Self {
        state.state_ref()
    }
}

/// A synchronously hydrated publication-only state backed by one source
/// attachment.
///
/// The source holds only a weak reference: dropping every handle stops
/// publication, but only [`dispose`](Self::dispose) releases the attachment.
#[derive(Clone)]
pub struct AttachedReplicatedState {
    inner: Arc<AttachedInner>,
}

struct AttachedInner {
    publisher: Arc<ReplicatedStatePublisher>,
    attachment: Box<dyn ReplicatedStateSourceAttachment>,
    report: ErrorReporter,
    progress: Mutex<AttachedProgress>,
}

struct AttachedProgress {
    cursor: i64,
    disposed: bool,
}

impl AttachedInner {
    fn report(&self, error: ChordError) {
        (self.report)(error);
    }

    fn receive(&self, frame: ReplicatedStateSourceFrame) {
        let checked = {
            let mut progress = lock(&self.progress);
            if progress.disposed {
                return;
            }
            assert_cursor(frame.cursor, CursorKind::Frame).and_then(|()| {
                let expected = progress.cursor + 1;
                if frame.cursor == expected {
                    progress.cursor = frame.cursor;
                    Ok(())
                } else {
                    Err(ChordError::error(format!(
                        "Replicated state source cursor has a gap: expected {expected}, received {}",
                        frame.cursor
                    )))
                }
            })
        };
        if let Err(error) = checked {
            self.fail(error);
            return;
        }
        let mut errors = self
            .publisher
            .publish(frame.value, frame.ops, frame.context);
        match errors.len() {
            0 => {}
            1 => self.report(errors.remove(0)),
            _ => {
                self.report(
                    AggregateError::new(errors, "Replicated state listeners failed").into(),
                );
            }
        }
    }

    fn fail(&self, error: ChordError) {
        {
            let mut progress = lock(&self.progress);
            if progress.disposed {
                return;
            }
            progress.disposed = true;
        }
        if let Err(dispose_error) = self.attachment.dispose() {
            self.report(
                AggregateError::new(
                    vec![error, ChordError::from(dispose_error)],
                    "Replicated state source contract failed",
                )
                .into(),
            );
            return;
        }
        self.report(error);
    }
}

/// Attach a publication-only replicated state to one authoritative immutable
/// source stream (TS `replicatedState(source, options)`).
///
/// # Errors
///
/// An attach or activation failure, or an unsafe snapshot cursor. The
/// attachment is disposed first; when that fails too, both failures are
/// returned as an aggregate.
pub fn replicated_state_from_source(
    source: &dyn ReplicatedStateSource,
    options: ReplicatedStateSourceOptions,
) -> Result<AttachedReplicatedState, ChordError> {
    let attachment = source.attach().map_err(ChordError::from)?;
    let snapshot = attachment.snapshot();
    if let Err(error) = assert_cursor(snapshot.cursor, CursorKind::Snapshot) {
        return Err(dispose_failed_attachment(attachment.as_ref(), error));
    }
    let report = options.on_error.unwrap_or_else(uncaught_reporter);
    let inner = Arc::new_cyclic(|weak: &Weak<AttachedInner>| {
        let reporter = weak.clone();
        let publisher_report: ErrorReporter = Arc::new(move |error| {
            if let Some(inner) = reporter.upgrade() {
                inner.report(error);
            }
        });
        AttachedInner {
            publisher: Arc::new(ReplicatedStatePublisher::new(
                snapshot.value,
                publisher_report,
            )),
            attachment,
            report,
            progress: Mutex::new(AttachedProgress {
                cursor: snapshot.cursor,
                disposed: false,
            }),
        }
    });
    let receiver = Arc::downgrade(&inner);
    let activated = inner.attachment.activate(Arc::new(move |frame| {
        if let Some(inner) = receiver.upgrade() {
            inner.receive(frame);
        }
    }));
    if let Err(error) = activated {
        return Err(dispose_failed_attachment(
            inner.attachment.as_ref(),
            ChordError::from(error),
        ));
    }
    Ok(AttachedReplicatedState { inner })
}

fn dispose_failed_attachment(
    attachment: &dyn ReplicatedStateSourceAttachment,
    error: ChordError,
) -> ChordError {
    match attachment.dispose() {
        Ok(()) => error,
        Err(dispose_error) => AggregateError::new(
            vec![error, ChordError::from(dispose_error)],
            "Failed to attach replicated state source",
        )
        .into(),
    }
}

impl AttachedReplicatedState {
    /// The last published value.
    #[must_use]
    pub fn value(&self) -> JsonValue {
        self.inner.publisher.value()
    }

    /// Subscribe with a closure (see [`ReplicatedState::subscribe`]).
    pub fn subscribe<F, R>(&self, listener: F) -> Disposer
    where
        F: Fn(JsonValue, Context, ReplicatedStateDelivery) -> R + Send + Sync + 'static,
        R: Into<Outcome>,
    {
        self.inner.publisher.subscribe(StateListener::new(listener))
    }

    /// Idempotently release the source attachment. The last published value
    /// remains readable.
    ///
    /// # Errors
    ///
    /// The attachment's disposal failure.
    pub fn dispose(&self) -> Result<(), ChordError> {
        {
            let mut progress = lock(&self.inner.progress);
            if progress.disposed {
                return Ok(());
            }
            progress.disposed = true;
        }
        self.inner.attachment.dispose().map_err(ChordError::from)
    }

    /// The handle a remote service uses to expose this state as a member.
    #[must_use]
    pub fn state_ref(&self) -> ReplicatedStateRef {
        ReplicatedStateRef {
            internals: Arc::new(Arc::clone(&self.inner.publisher)),
            state: Arc::new(self.clone()),
        }
    }
}

impl ReplicatedState for AttachedReplicatedState {
    fn value(&self) -> Option<JsonValue> {
        Some(AttachedReplicatedState::value(self))
    }

    fn subscribe(&self, listener: StateListener) -> Disposer {
        self.inner.publisher.subscribe(listener)
    }
}

impl From<&AttachedReplicatedState> for ReplicatedStateRef {
    fn from(state: &AttachedReplicatedState) -> Self {
        state.state_ref()
    }
}

static NEXT_REPLICA_LISTENER: AtomicU64 = AtomicU64::new(0);

/// A cold read-only state used by service consumers until a complete
/// snapshot arrives.
#[derive(Clone)]
pub(crate) struct ReplicatedStateReplica {
    inner: Arc<ReplicaInner>,
}

struct ReplicaInner {
    report: ErrorReporter,
    state: Mutex<ReplicaState>,
}

#[derive(Default)]
struct ReplicaState {
    listeners: Vec<(u64, StateSubscriber)>,
    value: Option<JsonValue>,
    sequence: Option<u64>,
}

impl ReplicatedStateReplica {
    pub(crate) fn new(report: ErrorReporter) -> Self {
        Self {
            inner: Arc::new(ReplicaInner {
                report,
                state: Mutex::new(ReplicaState::default()),
            }),
        }
    }

    pub(crate) fn current(&self) -> Option<JsonValue> {
        lock(&self.inner.state).value.clone()
    }

    pub(crate) fn subscribe_listener(&self, listener: StateListener) -> Disposer {
        let subscriber = StateSubscriber::new(listener, Arc::clone(&self.inner.report));
        let id = NEXT_REPLICA_LISTENER.fetch_add(1, Ordering::Relaxed);
        let hydrated = {
            let mut state = lock(&self.inner.state);
            state.listeners.push((id, subscriber.clone()));
            if let (Some(value), Some(sequence)) = (state.value.clone(), state.sequence) {
                subscriber.push(StateDelivery {
                    value,
                    context: service_delivery_context(),
                    delivery: ReplicatedStateDelivery {
                        kind: DeliveryKind::Hydrate,
                        sequence,
                    },
                });
                true
            } else {
                false
            }
        };
        if hydrated {
            subscriber.drain();
        }
        let replica = Arc::downgrade(&self.inner);
        Disposer::new(move || {
            subscriber.close();
            if let Some(replica) = replica.upgrade() {
                lock(&replica.state)
                    .listeners
                    .retain(|(candidate, _)| *candidate != id);
            }
        })
    }

    pub(crate) fn hydrate(
        &self,
        sequence: u64,
        ops: &[Op],
        context: &Context,
    ) -> Result<(), ChordError> {
        let next = if is_base(ops) {
            apply_immutable(&JsonValue::Null, ops).map_err(ChordError::from)
        } else {
            Err(ChordError::error(
                "Replicated state snapshot is not a base operation batch",
            ))
        };
        let next = match next {
            Ok(next) => next,
            Err(error) => {
                self.clear();
                return Err(error);
            }
        };
        self.adopt(
            next,
            context,
            ReplicatedStateDelivery {
                kind: DeliveryKind::Hydrate,
                sequence,
            },
        );
        Ok(())
    }

    pub(crate) fn update(
        &self,
        sequence: u64,
        ops: &[Op],
        context: &Context,
    ) -> Result<(), ChordError> {
        let (current, expected) = {
            let state = lock(&self.inner.state);
            match (&state.value, state.sequence) {
                (Some(value), Some(current)) => (value.clone(), current + 1),
                _ => {
                    return Err(ChordError::error(
                        "Replicated state received an update before hydration",
                    ))
                }
            }
        };
        if sequence != expected {
            self.clear();
            return Err(ChordError::error(
                "Replicated state update sequence has a gap",
            ));
        }
        let next = match apply_immutable(&current, ops) {
            Ok(next) => next,
            Err(error) => {
                self.clear();
                return Err(error.into());
            }
        };
        self.adopt(
            next,
            context,
            ReplicatedStateDelivery {
                kind: DeliveryKind::Update,
                sequence,
            },
        );
        Ok(())
    }

    pub(crate) fn clear(&self) {
        let mut state = lock(&self.inner.state);
        state.value = None;
        state.sequence = None;
        for (_, subscriber) in &state.listeners {
            subscriber.clear();
        }
    }

    /// Adopt one validated revision and deliver it to every subscriber,
    /// enqueueing for everyone before user code can publish another revision
    /// reentrantly.
    fn adopt(&self, value: JsonValue, context: &Context, delivery: ReplicatedStateDelivery) {
        let subscribers: Vec<StateSubscriber> = {
            let mut state = lock(&self.inner.state);
            state.sequence = Some(delivery.sequence);
            state.value = Some(value.clone());
            let frame = StateDelivery {
                value,
                context: context.clone(),
                delivery,
            };
            let subscribers: Vec<StateSubscriber> = state
                .listeners
                .iter()
                .map(|(_, subscriber)| subscriber.clone())
                .collect();
            for subscriber in &subscribers {
                subscriber.push(frame.clone());
            }
            subscribers
        };
        for subscriber in subscribers {
            subscriber.drain();
        }
    }
}

impl ReplicatedState for ReplicatedStateReplica {
    fn value(&self) -> Option<JsonValue> {
        self.current()
    }

    fn subscribe(&self, listener: StateListener) -> Disposer {
        self.subscribe_listener(listener)
    }
}

/// Context for synthetic service deliveries without a caller.
pub(crate) fn service_delivery_context() -> Context {
    BACKGROUND_CONTEXT.clone()
}

#[derive(Clone, Copy)]
enum CursorKind {
    Snapshot,
    Frame,
}

/// TS `Number.isSafeInteger(cursor)`; Rust cursors are integers already.
fn assert_cursor(cursor: i64, kind: CursorKind) -> Result<(), ChordError> {
    if cursor.unsigned_abs() <= MAX_SAFE_CURSOR {
        return Ok(());
    }
    let kind = match kind {
        CursorKind::Snapshot => "snapshot",
        CursorKind::Frame => "frame",
    };
    Err(ChordError::type_error(format!(
        "Replicated state source {kind} cursor must be a safe integer"
    )))
}
