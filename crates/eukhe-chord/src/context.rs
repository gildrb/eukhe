//! Invocation contexts: explicit cancellation plus typed values. Port of
//! `@earendil-works/chord/context` and the platform `AbortController` /
//! `AbortSignal` it builds on.
//!
//! A [`Context`] is immutable. Deriving one never changes its parent.
//! Cancelling a context's signal cancels every context derived from it.
//!
//! JS promises run whether or not anyone awaits them; Rust futures run only
//! while polled and stop when dropped. [`await_with_context`] drops the
//! awaited future on cancellation, so pass it a future whose drop does not
//! cancel shared work: a channel receive, a watch, or a spawned task's join.

use std::any::Any;
use std::fmt;
use std::future::Future;
use std::marker::PhantomData;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, LazyLock, Mutex, MutexGuard, PoisonError, Weak};

use tokio::sync::watch;
use tokio_util::sync::CancellationToken;

/// Why a signal aborted: the JS `AbortSignal.reason`.
pub type AbortReason = Arc<dyn std::error::Error + Send + Sync + 'static>;

/// The reason of an abort that supplied none. JS uses a `DOMException` named
/// `AbortError` with this message.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("This operation was aborted")]
pub struct AbortError;

/// Locks a follower list. Every critical section only pushes or drains
/// handles, so a panic in another thread leaves the list consistent.
fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

#[derive(Default)]
struct Followers {
    signals: Vec<Weak<SignalInner>>,
    tokens: Vec<CancellationToken>,
}

struct SignalInner {
    state: watch::Sender<Option<AbortReason>>,
    followers: Mutex<Followers>,
}

impl SignalInner {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            state: watch::Sender::new(None),
            followers: Mutex::new(Followers::default()),
        })
    }

    fn reason(&self) -> Option<AbortReason> {
        self.state.borrow().clone()
    }

    /// Abort once; later calls keep the first reason. Followers abort with it.
    fn abort(&self, reason: &AbortReason) {
        let mut first = false;
        self.state.send_if_modified(|current| {
            if current.is_some() {
                return false;
            }
            *current = Some(reason.clone());
            first = true;
            true
        });
        if !first {
            return;
        }
        let followers = std::mem::take(&mut *lock(&self.followers));
        for token in followers.tokens {
            token.cancel();
        }
        for follower in followers.signals {
            if let Some(follower) = follower.upgrade() {
                follower.abort(reason);
            }
        }
    }

    /// Register a signal that aborts with this one. Weak, so a short-lived
    /// combined signal does not stay alive through a long-lived source.
    fn follow_signal(&self, follower: &Arc<SignalInner>) {
        let mut followers = lock(&self.followers);
        if let Some(reason) = self.reason() {
            drop(followers);
            follower.abort(&reason);
            return;
        }
        followers.signals.retain(|weak| weak.strong_count() > 0);
        followers.signals.push(Arc::downgrade(follower));
    }

    fn follow_token(&self, token: &CancellationToken) {
        let mut followers = lock(&self.followers);
        if self.reason().is_some() {
            drop(followers);
            token.cancel();
            return;
        }
        followers.tokens.retain(|token| !token.is_cancelled());
        followers.tokens.push(token.clone());
    }
}

/// Observes one [`AbortController`]: the JS `AbortSignal`. Clones share state.
#[derive(Clone)]
pub struct AbortSignal {
    inner: Arc<SignalInner>,
}

impl AbortSignal {
    /// Whether the signal has aborted.
    #[must_use]
    pub fn aborted(&self) -> bool {
        self.inner.state.borrow().is_some()
    }

    /// The abort reason, once aborted.
    #[must_use]
    pub fn reason(&self) -> Option<AbortReason> {
        self.inner.reason()
    }

    /// Resolves with the reason when the signal aborts; at once if it has.
    pub async fn cancelled(&self) -> AbortReason {
        let mut receiver = self.inner.state.subscribe();
        loop {
            if let Some(reason) = receiver.borrow_and_update().clone() {
                return reason;
            }
            // The sender lives in `self.inner`, which this future borrows, so
            // the channel cannot close while this loop runs.
            if receiver.changed().await.is_err() {
                return Arc::new(AbortError);
            }
        }
    }

    /// The JS `throwIfAborted()`.
    ///
    /// # Errors
    ///
    /// Returns the abort reason when the signal has aborted.
    pub fn throw_if_aborted(&self) -> Result<(), AbortReason> {
        self.reason().map_or(Ok(()), Err)
    }

    /// A signal that aborts when any of `signals` aborts, with that signal's
    /// reason: the JS `AbortSignal.any()`. Aborted at once when one already
    /// has.
    #[must_use]
    pub fn any(signals: &[AbortSignal]) -> AbortSignal {
        let combined = SignalInner::new();
        for signal in signals {
            signal.inner.follow_signal(&combined);
            if combined.reason().is_some() {
                break;
            }
        }
        AbortSignal { inner: combined }
    }

    /// A cancellation token cancelled when this signal aborts, for APIs that
    /// take a [`CancellationToken`].
    #[must_use]
    pub fn cancellation_token(&self) -> CancellationToken {
        let token = CancellationToken::new();
        self.inner.follow_token(&token);
        token
    }

    /// Whether both handles observe the same signal.
    #[must_use]
    pub fn same(&self, other: &AbortSignal) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl fmt::Debug for AbortSignal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("AbortSignal")
            .field("aborted", &self.aborted())
            .finish()
    }
}

/// Owns one [`AbortSignal`]: the JS `AbortController`.
#[derive(Clone, Debug)]
pub struct AbortController {
    signal: AbortSignal,
}

impl Default for AbortController {
    fn default() -> Self {
        Self::new()
    }
}

impl AbortController {
    /// A controller with a fresh, unaborted signal.
    #[must_use]
    pub fn new() -> Self {
        Self {
            signal: AbortSignal {
                inner: SignalInner::new(),
            },
        }
    }

    /// The signal this controller aborts.
    #[must_use]
    pub fn signal(&self) -> AbortSignal {
        self.signal.clone()
    }

    /// Abort the signal with `reason`, or [`AbortError`] when `None`. Only the
    /// first abort counts.
    pub fn abort(&self, reason: Option<AbortReason>) {
        self.signal
            .inner
            .abort(&reason.unwrap_or_else(|| Arc::new(AbortError)));
    }
}

static NEXT_KEY: AtomicU64 = AtomicU64::new(1);

/// Typed identity for one value carried by a [`Context`]. Two keys are equal
/// only when one is a clone of the other, like two JS symbols.
pub struct ContextKey<T> {
    id: u64,
    description: Arc<str>,
    value_type: PhantomData<fn(T) -> T>,
}

impl<T> Clone for ContextKey<T> {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            description: Arc::clone(&self.description),
            value_type: PhantomData,
        }
    }
}

impl<T> fmt::Debug for ContextKey<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ContextKey")
            .field("description", &self.description)
            .finish_non_exhaustive()
    }
}

impl<T> ContextKey<T> {
    /// The description given at creation.
    #[must_use]
    pub fn description(&self) -> &str {
        &self.description
    }
}

/// Create a key with a fresh identity: the JS `createContextKey()`.
#[must_use]
pub fn create_context_key<T>(description: &str) -> ContextKey<T> {
    ContextKey {
        id: NEXT_KEY.fetch_add(1, Ordering::Relaxed),
        description: Arc::from(description),
        value_type: PhantomData,
    }
}

static ABORT_SIGNAL_CONTEXT_KEY: LazyLock<ContextKey<Option<AbortSignal>>> =
    LazyLock::new(|| create_context_key("chord.abortSignal"));

enum ContextNode {
    Empty(&'static str),
    Value {
        parent: Context,
        key: u64,
        description: Arc<str>,
        value: Arc<dyn Any + Send + Sync>,
    },
}

/// Immutable invocation-scoped values passed explicitly through operations.
#[derive(Clone)]
pub struct Context {
    node: Arc<ContextNode>,
}

/// A context that is never cancelled and carries no values.
pub static BACKGROUND_CONTEXT: LazyLock<Context> =
    LazyLock::new(|| Context::empty("[Context BACKGROUND_CONTEXT]"));

/// Like [`BACKGROUND_CONTEXT`]; marks code that still has to receive its
/// caller's context.
pub static TODO_CONTEXT: LazyLock<Context> =
    LazyLock::new(|| Context::empty("[Context TODO_CONTEXT]"));

impl Context {
    fn empty(name: &'static str) -> Self {
        Self {
            node: Arc::new(ContextNode::Empty(name)),
        }
    }

    /// The value stored under `key` by this context or its nearest ancestor
    /// that has one.
    #[must_use]
    pub fn value<T: Clone + Send + Sync + 'static>(&self, key: &ContextKey<T>) -> Option<T> {
        let mut node = &self.node;
        loop {
            match node.as_ref() {
                ContextNode::Empty(_) => return None,
                ContextNode::Value {
                    parent,
                    key: id,
                    value,
                    ..
                } => {
                    if *id == key.id {
                        return value.downcast_ref::<T>().cloned();
                    }
                    node = &parent.node;
                }
            }
        }
    }

    /// The cancellation signal, if this context can be cancelled.
    #[must_use]
    pub fn abort_signal(&self) -> Option<AbortSignal> {
        self.value(&ABORT_SIGNAL_CONTEXT_KEY).flatten()
    }

    /// Whether the cancellation signal has aborted.
    #[must_use]
    pub fn aborted(&self) -> bool {
        self.abort_signal().is_some_and(|signal| signal.aborted())
    }
}

impl fmt::Display for Context {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.node.as_ref() {
            ContextNode::Empty(name) => formatter.write_str(name),
            ContextNode::Value {
                parent,
                description,
                ..
            } => write!(formatter, "{parent}.WithValue({description})"),
        }
    }
}

impl fmt::Debug for Context {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, formatter)
    }
}

/// Derive a context containing one additional or replaced value.
#[must_use]
pub fn with_context_value<T: Send + Sync + 'static>(
    key: &ContextKey<T>,
    value: T,
    parent: &Context,
) -> Context {
    Context {
        node: Arc::new(ContextNode::Value {
            parent: parent.clone(),
            key: key.id,
            description: Arc::clone(&key.description),
            value: Arc::new(value),
        }),
    }
}

/// Derive a context cancelled by either the parent signal or `signal`. The
/// parent context remains unchanged.
#[must_use]
pub fn with_abort_signal(signal: &AbortSignal, context: &Context) -> Context {
    let combined = match context.abort_signal() {
        None => signal.clone(),
        Some(parent) => AbortSignal::any(&[parent, signal.clone()]),
    };
    with_context_value(&ABORT_SIGNAL_CONTEXT_KEY, Some(combined), context)
}

/// Derive a context retaining all values except caller cancellation. Intended
/// for mandatory cleanup only.
#[must_use]
pub fn without_abort_signal(context: &Context) -> Context {
    with_context_value(&ABORT_SIGNAL_CONTEXT_KEY, None, context)
}

/// Cancels the context returned with it by [`with_cancel`].
#[derive(Clone, Debug)]
pub struct CancelContext {
    controller: AbortController,
}

impl CancelContext {
    /// Cancel with `reason`, or [`AbortError`] when `None`.
    pub fn cancel(&self, reason: Option<AbortReason>) {
        self.controller.abort(reason);
    }
}

/// Derive an independently cancellable child context.
#[must_use]
pub fn with_cancel(context: &Context) -> (Context, CancelContext) {
    let controller = AbortController::new();
    let child = with_abort_signal(&controller.signal(), context);
    (child, CancelContext { controller })
}

/// Await `future` until it completes or `context` is cancelled. Cancellation
/// rejects only this waiter: the JS promise keeps running, so `future` must
/// not own the work it waits for (see the module docs).
///
/// # Errors
///
/// Returns the abort reason when the context is cancelled first, including
/// when it already was.
pub async fn await_with_context<F: Future>(
    future: F,
    context: &Context,
) -> Result<F::Output, AbortReason> {
    let Some(signal) = context.abort_signal() else {
        return Ok(future.await);
    };
    if let Some(reason) = signal.reason() {
        return Err(reason);
    }
    tokio::select! {
        biased;
        reason = signal.cancelled() => Err(reason),
        output = future => Ok(output),
    }
}
