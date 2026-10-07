//! Committed observation: the Session-to-Chord state source bridge and the
//! serialized exact-frame watch.

use std::collections::VecDeque;
use std::fmt;
use std::future::Future;
use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use eukhe_chord::context::{without_abort_signal, AbortSignal, Context};
use eukhe_chord::delta::Op;
use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_chord::{
    BoxError, ReplicatedStateSource, ReplicatedStateSourceAttachment, ReplicatedStateSourceFrame,
    ReplicatedStateSourceSnapshot, SourceFrameListener,
};
use futures::future::BoxFuture;
use tokio::sync::watch;
use tokio::task::JoinHandle;

use super::error::{SessionError, SessionResult};

/// A committed document revision, or `None` once the incarnation retired
/// (TS `Readonly<JsonObject> | null`).
pub type ObservedDocumentValue = Option<Arc<JsonObject>>;

/// Shared exact operation batch of one committed frame.
pub type Ops = Arc<[Op]>;

/// Maximum exact committed frames retained behind one unavailable watch listener.
const MAX_PENDING_WATCH_FRAMES: usize = 100;

/// Canonical terminal update for a retired document incarnation: `[["r", null]]`.
pub(crate) static RETIREMENT_OPERATIONS: LazyLock<Ops> =
    LazyLock::new(|| Arc::from(vec![Op::Replace(JsonValue::Null)]));

/// Session-to-Chord bridge owned one-to-one by one attached state: a document,
/// or a conversation view. A retirement value retires it.
#[derive(Clone)]
pub(crate) struct CommittedStateSource {
    inner: Arc<Mutex<SourceState>>,
}

struct SourceState {
    attachments: Vec<(u64, Arc<SessionSourceAttachment>)>,
    next_attachment: u64,
    release: Option<Box<dyn FnOnce() + Send>>,
    /// Released on disposal.
    value: Option<JsonValue>,
    cursor: i64,
    retired: bool,
    closed: bool,
}

fn lock_source(state: &Mutex<SourceState>) -> std::sync::MutexGuard<'_, SourceState> {
    state.lock().unwrap_or_else(PoisonError::into_inner)
}

impl CommittedStateSource {
    pub(crate) fn new<T: ObservedValue>(value: &T, release: Box<dyn FnOnce() + Send>) -> Self {
        Self {
            inner: Arc::new(Mutex::new(SourceState {
                attachments: Vec::new(),
                next_attachment: 0,
                release: Some(release),
                value: Some(value.to_json()),
                cursor: 0,
                retired: false,
                closed: false,
            })),
        }
    }

    /// Publish one committed frame to every attachment.
    pub(crate) fn advance<T: ObservedValue>(&self, value: &T, ops: Ops, context: Context) {
        let (frame, attachments) = {
            let mut state = lock_source(&self.inner);
            if state.closed || state.retired {
                return;
            }
            let json = value.to_json();
            state.value = Some(json.clone());
            state.cursor += 1;
            if value.is_retirement() {
                state.retired = true;
            }
            let frame = ReplicatedStateSourceFrame {
                cursor: state.cursor,
                value: json,
                ops,
                context,
            };
            let attachments: Vec<_> = state
                .attachments
                .iter()
                .map(|(_, attachment)| Arc::clone(attachment))
                .collect();
            (frame, attachments)
        };
        for attachment in attachments {
            attachment.publish(frame.clone());
        }
    }

    /// Dispose every attachment and release the Session subscriptions.
    pub(crate) fn close_session(&self) {
        let attachments: Vec<_> = {
            let state = lock_source(&self.inner);
            if state.closed {
                return;
            }
            state
                .attachments
                .iter()
                .map(|(_, attachment)| Arc::clone(attachment))
                .collect()
        };
        for attachment in attachments {
            attachment.dispose_now();
        }
        finish_source_disposal(&self.inner);
    }
}

fn finish_source_disposal(inner: &Mutex<SourceState>) {
    let release = {
        let mut state = lock_source(inner);
        if state.closed {
            return;
        }
        state.closed = true;
        state.value = None;
        state.release.take()
    };
    if let Some(release) = release {
        release();
    }
}

impl ReplicatedStateSource for CommittedStateSource {
    fn attach(&self) -> Result<Box<dyn ReplicatedStateSourceAttachment>, BoxError> {
        let mut state = lock_source(&self.inner);
        if state.closed {
            return Err("State source is closed".into());
        }
        let id = state.next_attachment;
        state.next_attachment += 1;
        let source = Arc::downgrade(&self.inner);
        let attachment = Arc::new(SessionSourceAttachment {
            snapshot: ReplicatedStateSourceSnapshot {
                value: state.value.clone().unwrap_or(JsonValue::Null),
                cursor: state.cursor,
            },
            state: Mutex::new(AttachmentState {
                release: Some(Box::new(move || {
                    let Some(source) = source.upgrade() else {
                        return;
                    };
                    let empty = {
                        let mut state = lock_source(&source);
                        state.attachments.retain(|(other, _)| *other != id);
                        state.attachments.is_empty()
                    };
                    if empty {
                        finish_source_disposal(&source);
                    }
                })),
                frames: VecDeque::new(),
                listener: None,
                activated: false,
                disposed: false,
                scheduled: false,
                delivering: false,
            }),
        });
        state.attachments.push((id, Arc::clone(&attachment)));
        Ok(Box::new(AttachmentHandle(attachment)))
    }
}

#[expect(
    clippy::struct_excessive_bools,
    reason = "one-to-one port of the TS attachment's private flags"
)]
struct AttachmentState {
    release: Option<Box<dyn FnOnce() + Send>>,
    frames: VecDeque<ReplicatedStateSourceFrame>,
    listener: Option<SourceFrameListener>,
    activated: bool,
    disposed: bool,
    scheduled: bool,
    delivering: bool,
}

struct SessionSourceAttachment {
    snapshot: ReplicatedStateSourceSnapshot,
    state: Mutex<AttachmentState>,
}

impl SessionSourceAttachment {
    fn lock(&self) -> std::sync::MutexGuard<'_, AttachmentState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn publish(self: &Arc<Self>, frame: ReplicatedStateSourceFrame) {
        let mut state = self.lock();
        if state.disposed {
            return;
        }
        state.frames.push_back(frame);
        if !state.activated || state.delivering || state.scheduled {
            return;
        }
        state.scheduled = true;
        let attachment = Arc::clone(self);
        // TS `queueMicrotask`: deliver after the publishing commit's listeners.
        tokio::spawn(async move {
            {
                let mut state = attachment.lock();
                state.scheduled = false;
                if state.disposed {
                    return;
                }
            }
            attachment.drain();
        });
    }

    fn dispose_now(&self) {
        let release = {
            let mut state = self.lock();
            if state.disposed {
                return;
            }
            state.disposed = true;
            state.frames.clear();
            state.listener = None;
            state.release.take()
        };
        if let Some(release) = release {
            release();
        }
    }

    fn drain(&self) {
        let listener = {
            let mut state = self.lock();
            if state.delivering || state.disposed {
                return;
            }
            let Some(listener) = state.listener.clone() else {
                return;
            };
            state.delivering = true;
            listener
        };
        loop {
            let frame = {
                let mut state = self.lock();
                if state.disposed {
                    break;
                }
                state.frames.pop_front()
            };
            let Some(frame) = frame else {
                break;
            };
            listener(frame);
        }
        self.lock().delivering = false;
    }
}

/// The boxed attachment handed to Chord.
struct AttachmentHandle(Arc<SessionSourceAttachment>);

impl ReplicatedStateSourceAttachment for AttachmentHandle {
    fn snapshot(&self) -> ReplicatedStateSourceSnapshot {
        self.0.snapshot.clone()
    }

    fn activate(&self, listener: SourceFrameListener) -> Result<(), BoxError> {
        {
            let mut state = self.0.lock();
            if state.activated {
                return Err("State attachment is already active".into());
            }
            if state.disposed {
                return Err("State attachment is disposed".into());
            }
            state.activated = true;
            state.listener = Some(listener);
        }
        self.0.drain();
        Ok(())
    }

    fn dispose(&self) -> Result<(), BoxError> {
        self.0.dispose_now();
        Ok(())
    }
}

/// A value an observer delivers: `retired` is the TS `value === null` test,
/// `to_json` the value a root replacement carries.
pub trait ObservedValue: Clone + Send + Sync + 'static {
    /// Whether this value retires the observed incarnation (TS `null`).
    fn is_retirement(&self) -> bool;
    /// The JSON this value replaces the root with.
    fn to_json(&self) -> JsonValue;
}

impl ObservedValue for ObservedDocumentValue {
    fn is_retirement(&self) -> bool {
        self.is_none()
    }

    fn to_json(&self) -> JsonValue {
        self.as_ref().map_or(JsonValue::Null, |value| {
            JsonValue::Object(Arc::clone(value))
        })
    }
}

/// Terminal result of one document watch.
#[derive(Clone, Debug)]
pub enum WatchEnd {
    /// `stop()` ended the watch.
    Stopped,
    /// The acquisition context was cancelled.
    Cancelled,
    /// The Session began closing.
    SessionClosed,
    /// The observed incarnation retired and its `null` frame was delivered.
    Retired,
    /// The listener failed; no later frame is delivered.
    ListenerError(Arc<dyn std::error::Error + Send + Sync>),
}

impl WatchEnd {
    /// The TS `reason` string.
    #[must_use]
    pub fn reason(&self) -> &'static str {
        match self {
            Self::Stopped => "stopped",
            Self::Cancelled => "cancelled",
            Self::SessionClosed => "session_closed",
            Self::Retired => "retired",
            Self::ListenerError(_) => "listener_error",
        }
    }
}

/// Equal reasons; listener errors compare by message (TS `toEqual` on `Error`).
impl PartialEq for WatchEnd {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::ListenerError(left), Self::ListenerError(right)) => {
                left.to_string() == right.to_string()
            }
            _ => self.reason() == other.reason(),
        }
    }
}

/// Failure a watch listener reports.
pub type WatchListenerError = Arc<dyn std::error::Error + Send + Sync>;

/// The sole asynchronous listener of a watch: `(value, ops, context)`.
pub type WatchListener<T> = Arc<
    dyn Fn(T, Ops, Context) -> BoxFuture<'static, Result<(), WatchListenerError>> + Send + Sync,
>;

/// Serialized exact-frame observation of an immutable value with bounded pending
/// delivery (TS `WatchHandle`).
pub type DocumentWatch = CommittedWatch<ObservedDocumentValue>;

struct WatchFrame<T> {
    value: T,
    ops: Ops,
    context: Context,
    /// Position in queue order; an overflow replacement takes the newest.
    seq: u64,
}

/// How far delivery got, for [`CommittedWatch::delivered`].
#[derive(Clone, Copy, Debug, Default)]
struct Delivery {
    /// `seq` of the last frame whose listener future settled.
    settled: u64,
    /// The watch terminated; nothing more is delivered.
    ended: bool,
}

#[expect(
    clippy::struct_excessive_bools,
    reason = "one-to-one port of the TS watch's private flags"
)]
struct WatchState<T> {
    value: T,
    pending: VecDeque<WatchFrame<T>>,
    listener: Option<WatchListener<T>>,
    started: bool,
    scheduled: bool,
    running: bool,
    detach: Option<Box<dyn FnOnce() + Send>>,
    retired: bool,
    end: Option<WatchEnd>,
    /// `seq` of the newest queued frame.
    queued: u64,
    resolved: bool,
    cancellation_installed: bool,
    cancellation: Option<JoinHandle<()>>,
}

struct WatchInner<T> {
    state: Mutex<WatchState<T>>,
    replace: Option<Box<dyn Fn() -> T + Send + Sync>>,
    closed: watch::Sender<Option<WatchEnd>>,
    delivery: watch::Sender<Delivery>,
}

/// Serialized exact-frame watch bound to one document incarnation or
/// conversation view. A retirement value retires it. Clones share the watch.
pub struct CommittedWatch<T: ObservedValue> {
    inner: Arc<WatchInner<T>>,
}

impl<T: ObservedValue> Clone for CommittedWatch<T> {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl<T: ObservedValue> fmt::Debug for CommittedWatch<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let state = self.lock();
        formatter
            .debug_struct("CommittedWatch")
            .field("started", &state.started)
            .field("end", &state.end)
            .finish_non_exhaustive()
    }
}

impl<T: ObservedValue> CommittedWatch<T> {
    /// A watch at `value`; `detach` runs once when it terminates. `replace`
    /// gives the value an overflow delivers; by default the newest value.
    pub(crate) fn new(
        value: T,
        detach: Box<dyn FnOnce() + Send>,
        replace: Option<Box<dyn Fn() -> T + Send + Sync>>,
    ) -> Self {
        let (closed, _) = watch::channel(None);
        Self {
            inner: Arc::new(WatchInner {
                state: Mutex::new(WatchState {
                    value,
                    pending: VecDeque::new(),
                    listener: None,
                    started: false,
                    scheduled: false,
                    running: false,
                    detach: Some(detach),
                    retired: false,
                    end: None,
                    queued: 0,
                    resolved: false,
                    cancellation_installed: false,
                    cancellation: None,
                }),
                replace,
                closed,
                delivery: watch::Sender::new(Delivery::default()),
            }),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, WatchState<T>> {
        self.inner
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    /// Acquisition revision before start; latest delivered immutable revision afterward.
    #[must_use]
    pub fn value(&self) -> T {
        self.lock().value.clone()
    }

    /// Settles when the watch terminates; an already-running callback remains
    /// caller-owned.
    pub fn closed(&self) -> impl Future<Output = WatchEnd> + Send + 'static {
        let mut receiver = self.inner.closed.subscribe();
        async move {
            loop {
                if let Some(end) = receiver.borrow_and_update().clone() {
                    return end;
                }
                // Every handle dropped without the watch ending: like an
                // unresolved TS promise, `closed` never settles.
                if receiver.changed().await.is_err() {
                    if let Some(end) = receiver.borrow().clone() {
                        return end;
                    }
                    return std::future::pending().await;
                }
            }
        }
    }

    /// Install the sole asynchronous listener. Never invokes it inline.
    ///
    /// # Errors
    ///
    /// `Watch is already started`, or `Watch is stopped` after termination.
    pub fn start(&self, listener: WatchListener<T>) -> SessionResult<()> {
        let mut state = self.lock();
        if state.started {
            return Err(SessionError::error("Watch is already started"));
        }
        if state.end.is_some() {
            return Err(SessionError::error("Watch is stopped"));
        }
        state.started = true;
        state.listener = Some(listener);
        if !state.pending.is_empty() {
            self.schedule(&mut state);
        }
        Ok(())
    }

    /// Idempotently stop future callbacks and return this watch's terminal result.
    pub fn stop(&self) -> impl Future<Output = WatchEnd> + Send + 'static {
        self.terminate(WatchEnd::Stopped);
        self.closed()
    }

    /// eukhe addition (TS has no counterpart): resolves once every frame
    /// queued when this is called, including an overflow replacement, has
    /// been passed to the listener and the listener future for the last of
    /// them has settled. Resolves at once when the watch has terminated
    /// (stopped, cancelled, closed, retired, or a listener failure), and as
    /// soon as it terminates later. Commits queue their frames before their
    /// commit future resolves, so after `wait_for_idle()` this is a barrier
    /// for every batch committed so far. Before `start()` it waits for the
    /// listener.
    pub fn delivered(&self) -> impl Future<Output = ()> + Send + 'static {
        let target = self.lock().queued;
        let mut receiver = self.inner.delivery.subscribe();
        async move {
            // Every handle dropped: nothing can be delivered any more.
            let _ = receiver
                .wait_for(|delivery| delivery.ended || delivery.settled >= target)
                .await;
        }
    }

    /// Terminate as `cancelled` when `signal` aborts.
    pub(crate) fn observe_cancellation(&self, signal: &AbortSignal) -> SessionResult<()> {
        let mut state = self.lock();
        if state.cancellation_installed {
            return Err(SessionError::error(
                "Watch cancellation is already installed",
            ));
        }
        if state.end.is_some() {
            return Ok(());
        }
        state.cancellation_installed = true;
        if signal.aborted() {
            drop(state);
            self.cancel();
            return Ok(());
        }
        let watch = self.clone();
        let signal = signal.clone();
        state.cancellation = Some(tokio::spawn(async move {
            signal.cancelled().await;
            watch.cancel();
        }));
        Ok(())
    }

    /// Terminate as `cancelled`.
    pub(crate) fn cancel(&self) {
        self.terminate(WatchEnd::Cancelled);
    }

    /// Terminate as `session_closed`.
    pub(crate) fn close_session(&self) {
        self.terminate(WatchEnd::SessionClosed);
    }

    /// Queue one committed frame; past 100 pending frames they fold into one
    /// root replacement.
    pub(crate) fn advance(&self, value: T, ops: Ops, context: Context) {
        let mut state = self.lock();
        if state.end.is_some() || state.retired {
            return;
        }
        if value.is_retirement() {
            state.retired = true;
        }
        state.queued += 1;
        let seq = state.queued;
        if state.pending.len() >= MAX_PENDING_WATCH_FRAMES {
            state.pending.clear();
            let replacement = self
                .inner
                .replace
                .as_ref()
                .map_or(value, |replace| replace());
            let ops: Ops = Arc::from(vec![Op::Replace(replacement.to_json())]);
            state.pending.push_back(WatchFrame {
                value: replacement,
                ops,
                context,
                seq,
            });
        } else {
            state.pending.push_back(WatchFrame {
                value,
                ops,
                context,
                seq,
            });
        }
        if state.started {
            self.schedule(&mut state);
        }
    }

    fn schedule(&self, state: &mut WatchState<T>) {
        if state.scheduled || state.running || state.end.is_some() {
            return;
        }
        state.scheduled = true;
        let watch = self.clone();
        tokio::spawn(async move {
            watch.lock().scheduled = false;
            watch.drain().await;
        });
    }

    async fn drain(&self) {
        {
            let mut state = self.lock();
            if state.running || state.end.is_some() || !state.started {
                drop(state);
                self.finish_if_ready();
                return;
            }
            state.running = true;
        }
        loop {
            let (frame, listener) = {
                let mut state = self.lock();
                if state.end.is_some() {
                    break;
                }
                let Some(frame) = state.pending.pop_front() else {
                    break;
                };
                state.value = frame.value.clone();
                let Some(listener) = state.listener.clone() else {
                    break;
                };
                (frame, listener)
            };
            let delivery_context = without_abort_signal(&frame.context);
            let retirement = frame.value.is_retirement();
            let seq = frame.seq;
            if let Err(error) = listener(frame.value, frame.ops, delivery_context).await {
                self.terminate(WatchEnd::ListenerError(error));
                break;
            }
            self.inner
                .delivery
                .send_modify(|delivery| delivery.settled = seq);
            if retirement {
                self.terminate(WatchEnd::Retired);
                break;
            }
        }
        {
            let mut state = self.lock();
            state.running = false;
            if state.end.is_none() && !state.pending.is_empty() {
                self.schedule(&mut state);
            }
        }
        self.finish_if_ready();
    }

    fn terminate(&self, end: WatchEnd) {
        let detach = {
            let mut state = self.lock();
            if state.end.is_some() {
                return;
            }
            state.end = Some(end);
            state.pending.clear();
            state.detach.take()
        };
        if let Some(detach) = detach {
            detach();
        }
        self.inner
            .delivery
            .send_modify(|delivery| delivery.ended = true);
        self.finish_if_ready();
    }

    fn finish_if_ready(&self) {
        let end = {
            let mut state = self.lock();
            if state.resolved {
                return;
            }
            let Some(end) = state.end.clone() else {
                return;
            };
            state.resolved = true;
            if let Some(cancellation) = state.cancellation.take() {
                cancellation.abort();
            }
            end
        };
        self.inner.closed.send_replace(Some(end));
    }
}
