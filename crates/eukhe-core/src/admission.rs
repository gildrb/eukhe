//! Per-provider model-request admission (omp2 `AdmissionController`): a
//! provider with a `providerMaxInFlight` limit serves at most that many
//! requests at once; later requests wait in FIFO order, and once
//! `providerMaxQueued` requests wait the next one fails at once with a
//! non-retryable error.
//!
//! Requests come in two classes ([`AdmissionPriority`]). A session's
//! requests are interactive; the chat-memory compactor's are background.
//! Both count against the same limit, but a background request is
//! admitted only while no interactive request of its provider holds or
//! waits for a slot, and an interactive request that comes while
//! background requests hold slots preempts them all: their slots free at
//! once and their holders stop their requests, so a user's turn never
//! waits behind the compactor, even on a server that runs one request at
//! a time. An unlimited provider admits every request at once, and still
//! holds its background requests back while interactive ones run.
//!
//! The controller and its registry are process-local. Every eukhe session
//! runs in its own worker process, so the daemon supervisor owns the one
//! registry of a daemon and workers reach it through
//! [`ProviderAdmission`]; a run without a daemon uses
//! [`local_admission`], the same semantics in this process.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::future::Future;
use std::num::NonZeroU32;
use std::pin::Pin;
use std::sync::{Arc, LazyLock, Mutex, MutexGuard, PoisonError};
use std::task::{Context, Poll, Waker};

use eukhe_types::daemon::AdmissionPriority;
use futures::future::BoxFuture;
use futures::FutureExt as _;
use tokio_util::sync::{CancellationToken, WaitForCancellationFuture};

/// `providerMaxQueued` default (omp2 `ai_provider_max_queued`).
pub const DEFAULT_PROVIDER_MAX_QUEUED: u32 = 64;

/// The admission limits of every provider: `providerMaxInFlight` and
/// `providerMaxQueued`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdmissionLimits {
    max_in_flight: BTreeMap<String, NonZeroU32>,
    /// The limit of every provider `max_in_flight` does not name; `None`
    /// is unlimited.
    other_providers: Option<NonZeroU32>,
    max_queued: u32,
}

impl Default for AdmissionLimits {
    fn default() -> Self {
        Self {
            max_in_flight: BTreeMap::new(),
            other_providers: None,
            max_queued: DEFAULT_PROVIDER_MAX_QUEUED,
        }
    }
}

/// The in-flight limit a malformed `providerMaxInFlight` entry gives its
/// provider: the tightest one, never "no limit".
pub const MALFORMED_IN_FLIGHT_LIMIT: NonZeroU32 = NonZeroU32::MIN;

impl AdmissionLimits {
    /// Limits from the settings values: a provider mapped to `0` is
    /// unlimited, like an absent one; an absent `max_queued` is the default.
    #[must_use]
    pub fn new(max_in_flight: Option<&BTreeMap<String, u32>>, max_queued: Option<u32>) -> Self {
        Self {
            max_in_flight: max_in_flight
                .into_iter()
                .flatten()
                .filter_map(|(provider, limit)| Some((provider.clone(), NonZeroU32::new(*limit)?)))
                .collect(),
            other_providers: None,
            max_queued: max_queued.unwrap_or(DEFAULT_PROVIDER_MAX_QUEUED),
        }
    }

    /// Limits from the `providerMaxInFlight` value as written, read entry
    /// by entry so that a malformed limit fails closed
    /// (`LAWS.bend` section `config` `limit_malformed_fails_closed`): a whole number
    /// is the provider's limit (`0` unlimited); any other entry caps its
    /// provider at [`MALFORMED_IN_FLIGHT_LIMIT`]; a value that is neither
    /// a map nor `null` (unset) caps every provider at it. The settings
    /// load names each malformed value.
    #[must_use]
    pub fn from_setting(max_in_flight: &serde_json::Value, max_queued: Option<u32>) -> Self {
        use serde_json::Value;
        let mut limits = Self::new(None, max_queued);
        match max_in_flight {
            Value::Null => {}
            Value::Object(entries) => {
                for (provider, entry) in entries {
                    let limit = match entry.as_u64().map(u32::try_from) {
                        Some(Ok(limit)) => NonZeroU32::new(limit),
                        Some(Err(_)) => NonZeroU32::new(u32::MAX),
                        None => Some(MALFORMED_IN_FLIGHT_LIMIT),
                    };
                    if let Some(limit) = limit {
                        limits.max_in_flight.insert(provider.clone(), limit);
                    }
                }
            }
            Value::Bool(_) | Value::Number(_) | Value::String(_) | Value::Array(_) => {
                limits.other_providers = Some(MALFORMED_IN_FLIGHT_LIMIT);
            }
        }
        limits
    }

    /// The in-flight limit of `provider_id`; `None` is unlimited.
    #[must_use]
    pub fn max_in_flight(&self, provider_id: &str) -> Option<NonZeroU32> {
        self.max_in_flight
            .get(provider_id)
            .copied()
            .or(self.other_providers)
    }

    /// How many interactive requests may wait per provider.
    #[must_use]
    pub fn max_queued(&self) -> u32 {
        self.max_queued
    }
}

/// A request found the provider's wait queue full.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error(
    "provider admission queue is full for {provider_id}: {queue_limit} requests already wait \
     (providerMaxQueued)"
)]
pub struct AdmissionRejected {
    pub provider_id: String,
    pub queue_limit: u32,
}

/// Why a model request was not admitted.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum AdmissionError {
    /// The provider's wait queue is full; retrying at once would only
    /// lengthen it (never retried).
    #[error(transparent)]
    QueueFull(#[from] AdmissionRejected),
    /// The admission authority (the daemon supervisor) could not be asked.
    #[error("provider admission for {provider_id} is unavailable: {reason}")]
    Unavailable { provider_id: String, reason: String },
}

/// The counters of one provider.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AdmissionSnapshot {
    /// Interactive requests holding a permit.
    pub active: u32,
    /// Interactive requests waiting for one.
    pub waiting: u32,
    /// Background requests holding a permit.
    pub background_active: u32,
    /// Background requests waiting for one.
    pub background_waiting: u32,
}

/// A queue or table length as a counter.
fn count(len: usize) -> u32 {
    u32::try_from(len).unwrap_or(u32::MAX)
}

#[derive(Debug)]
struct WaitSlot {
    /// The grant's preemption token, once granted. A background grant its
    /// waiter has not collected yet goes back to the queue on preemption.
    granted: Option<CancellationToken>,
    waker: Option<Waker>,
}

#[derive(Debug)]
struct ControllerState {
    limit: Option<NonZeroU32>,
    queue_limit: u32,
    /// Interactive permits held (granted waiters included).
    interactive: u32,
    /// Background permits held (granted waiters included), by ticket: a
    /// preemption frees their slots and cancels their tokens.
    background: HashMap<u64, CancellationToken>,
    next_ticket: u64,
    /// Waiting interactive tickets. Tickets count up, so ticket order is
    /// arrival order: the first is the oldest.
    interactive_queue: BTreeSet<u64>,
    /// Waiting background tickets, oldest first. `providerMaxQueued` does
    /// not apply to them: the compactor bounds its own calls.
    background_queue: BTreeSet<u64>,
    /// Every ticket not yet collected by its waiter: queued ones and
    /// granted ones whose waiter has not polled since the grant.
    slots: HashMap<u64, WaitSlot>,
}

impl ControllerState {
    fn has_room(&self) -> bool {
        let active = self
            .interactive
            .saturating_add(count(self.background.len()));
        self.limit.is_none_or(|limit| active < limit.get())
    }

    /// Whether an interactive request holds or waits for a slot: background
    /// requests wait meanwhile.
    fn interactive_busy(&self) -> bool {
        self.interactive > 0 || !self.interactive_queue.is_empty()
    }

    /// Take a slot for `ticket` (the caller made sure there is room).
    /// Returns its preemption token, which only a preemption of a
    /// background slot cancels.
    fn hold(&mut self, ticket: u64, priority: AdmissionPriority) -> CancellationToken {
        let token = CancellationToken::new();
        match priority {
            AdmissionPriority::Interactive => self.interactive += 1,
            AdmissionPriority::Background => {
                self.background.insert(ticket, token.clone());
            }
        }
        token
    }

    /// Hand free slots to the oldest waiters (FIFO within each class):
    /// interactive ones first, background ones only while no interactive
    /// request holds a slot. Returns the wakers to fire once the lock is
    /// released.
    fn grant_waiters(&mut self) -> Vec<Waker> {
        let mut wake = Vec::new();
        while self.has_room() {
            let next = match self.interactive_queue.pop_first() {
                Some(ticket) => Some((ticket, AdmissionPriority::Interactive)),
                None if self.interactive == 0 => self
                    .background_queue
                    .pop_first()
                    .map(|ticket| (ticket, AdmissionPriority::Background)),
                None => None,
            };
            let Some((ticket, priority)) = next else {
                break;
            };
            let token = self.hold(ticket, priority);
            if let Some(slot) = self.slots.get_mut(&ticket) {
                slot.granted = Some(token);
                wake.extend(slot.waker.take());
            }
        }
        wake
    }

    /// An interactive request came: every background slot frees at once. A
    /// granted background waiter that has not collected its permit waits
    /// again, in its ticket's place (ahead of the requests that never had
    /// a slot); the tokens of collected permits are returned, to cancel
    /// once the lock is released.
    fn preempt_background(&mut self) -> Vec<CancellationToken> {
        let mut preempted = Vec::new();
        for (ticket, token) in self.background.drain() {
            match self.slots.get_mut(&ticket) {
                Some(slot) => {
                    slot.granted = None;
                    self.background_queue.insert(ticket);
                }
                None => preempted.push(token),
            }
        }
        preempted
    }

    /// The permit of `ticket` returns: its slot goes to the waiters. A
    /// preempted background permit's slot was freed by the preemption.
    fn release(&mut self, ticket: u64, priority: AdmissionPriority) -> Vec<Waker> {
        match priority {
            AdmissionPriority::Interactive => {
                self.interactive = self.interactive.saturating_sub(1);
            }
            AdmissionPriority::Background => {
                if self.background.remove(&ticket).is_none() {
                    return Vec::new();
                }
            }
        }
        self.grant_waiters()
    }
}

/// The admission of one provider (omp2 `AdmissionController`): permits
/// held per class, and one wait queue per class. A released permit goes
/// straight to the oldest waiter (FIFO-fair, where omp2 wakes every waiter
/// to race for it), so a stream of new requests can never starve an old
/// one of its class. Lowering the limit below the permits held lets the
/// excess drain; raising it admits waiters at once.
#[derive(Debug)]
pub struct AdmissionController {
    provider_id: String,
    state: Mutex<ControllerState>,
}

/// The outcome of [`AdmissionController::admit`] that did not fail.
pub enum Admission {
    /// A slot was free.
    Granted(ProviderPermit),
    /// The request waits (await the value).
    Queued(QueuedPermit),
}

impl AdmissionController {
    #[must_use]
    pub fn new(provider_id: impl Into<String>, limits: &AdmissionLimits) -> Arc<Self> {
        let provider_id = provider_id.into();
        Arc::new(Self {
            state: Mutex::new(ControllerState {
                limit: limits.max_in_flight(&provider_id),
                queue_limit: limits.max_queued(),
                interactive: 0,
                background: HashMap::new(),
                next_ticket: 0,
                interactive_queue: BTreeSet::new(),
                background_queue: BTreeSet::new(),
                slots: HashMap::new(),
            }),
            provider_id,
        })
    }

    fn lock(&self) -> MutexGuard<'_, ControllerState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Take a permit of class `priority` if a slot is free for it, else
    /// join the class's wait queue. An interactive request first preempts
    /// every background permit of the provider.
    ///
    /// # Errors
    ///
    /// [`AdmissionRejected`] when an interactive request finds
    /// `queue_limit` interactive requests waiting.
    pub fn admit(
        self: &Arc<Self>,
        priority: AdmissionPriority,
    ) -> Result<Admission, AdmissionRejected> {
        let mut state = self.lock();
        let preempted = match priority {
            AdmissionPriority::Interactive => state.preempt_background(),
            AdmissionPriority::Background => Vec::new(),
        };
        let free = state.has_room()
            && match priority {
                AdmissionPriority::Interactive => state.interactive_queue.is_empty(),
                AdmissionPriority::Background => {
                    !state.interactive_busy() && state.background_queue.is_empty()
                }
            };
        let ticket = state.next_ticket;
        state.next_ticket += 1;
        let admission = if free {
            Ok(Admission::Granted(ProviderPermit {
                controller: Arc::clone(self),
                ticket,
                priority,
                preempted: state.hold(ticket, priority),
            }))
        } else {
            let queued = match priority {
                AdmissionPriority::Interactive => {
                    if count(state.interactive_queue.len()) >= state.queue_limit {
                        Err(AdmissionRejected {
                            provider_id: self.provider_id.clone(),
                            queue_limit: state.queue_limit,
                        })
                    } else {
                        state.interactive_queue.insert(ticket);
                        Ok(())
                    }
                }
                AdmissionPriority::Background => {
                    state.background_queue.insert(ticket);
                    Ok(())
                }
            };
            queued.map(|()| {
                state.slots.insert(
                    ticket,
                    WaitSlot {
                        granted: None,
                        waker: None,
                    },
                );
                Admission::Queued(QueuedPermit {
                    controller: Arc::clone(self),
                    ticket,
                    priority,
                    collected: false,
                })
            })
        };
        drop(state);
        for token in preempted {
            token.cancel();
        }
        admission
    }

    /// Apply new limits; waiters a raised limit makes room for are granted.
    pub fn set_limits(&self, limits: &AdmissionLimits) {
        let wake = {
            let mut state = self.lock();
            state.limit = limits.max_in_flight(&self.provider_id);
            state.queue_limit = limits.max_queued();
            state.grant_waiters()
        };
        wake.into_iter().for_each(Waker::wake);
    }

    /// The current counters.
    #[must_use]
    pub fn snapshot(&self) -> AdmissionSnapshot {
        let state = self.lock();
        AdmissionSnapshot {
            active: state.interactive,
            waiting: count(state.interactive_queue.len()),
            background_active: count(state.background.len()),
            background_waiting: count(state.background_queue.len()),
        }
    }

    fn release(&self, ticket: u64, priority: AdmissionPriority) {
        let wake = self.lock().release(ticket, priority);
        wake.into_iter().for_each(Waker::wake);
    }
}

/// One admitted request; dropping it frees the slot.
#[derive(Debug)]
pub struct ProviderPermit {
    controller: Arc<AdmissionController>,
    ticket: u64,
    priority: AdmissionPriority,
    preempted: CancellationToken,
}

impl ProviderPermit {
    /// Cancelled once an interactive request preempts this permit (only a
    /// background permit is ever preempted): its slot is free already, and
    /// its request must stop.
    #[must_use]
    pub fn preemption(&self) -> CancellationToken {
        self.preempted.clone()
    }
}

impl Drop for ProviderPermit {
    fn drop(&mut self) {
        self.controller.release(self.ticket, self.priority);
    }
}

/// A request waiting in a provider's queue; resolves to its permit.
/// Dropping it leaves the queue, and a permit granted but not yet
/// collected goes to the next waiter.
#[derive(Debug)]
pub struct QueuedPermit {
    controller: Arc<AdmissionController>,
    ticket: u64,
    priority: AdmissionPriority,
    collected: bool,
}

impl Future for QueuedPermit {
    type Output = ProviderPermit;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<ProviderPermit> {
        let this = self.get_mut();
        let mut state = this.controller.lock();
        let Some(slot) = state.slots.get_mut(&this.ticket) else {
            // Only `poll` and `drop` remove a slot, and a collected permit
            // is never polled again.
            return Poll::Pending;
        };
        let Some(preempted) = slot.granted.take() else {
            slot.waker = Some(cx.waker().clone());
            return Poll::Pending;
        };
        state.slots.remove(&this.ticket);
        drop(state);
        this.collected = true;
        Poll::Ready(ProviderPermit {
            controller: Arc::clone(&this.controller),
            ticket: this.ticket,
            priority: this.priority,
            preempted,
        })
    }
}

impl Drop for QueuedPermit {
    fn drop(&mut self) {
        if self.collected {
            return;
        }
        let wake = {
            let mut state = self.controller.lock();
            let granted = state
                .slots
                .remove(&self.ticket)
                .is_some_and(|slot| slot.granted.is_some());
            if granted {
                state.release(self.ticket, self.priority)
            } else {
                match self.priority {
                    AdmissionPriority::Interactive => {
                        state.interactive_queue.remove(&self.ticket);
                    }
                    AdmissionPriority::Background => {
                        state.background_queue.remove(&self.ticket);
                    }
                }
                // The last interactive waiter leaving may let background
                // waiters through.
                state.grant_waiters()
            }
        };
        wake.into_iter().for_each(Waker::wake);
    }
}

/// The controllers of every provider, created on first use, sharing one
/// set of limits. A provider gets its controller once a request names it,
/// limited or not, so the configured providers bound the table.
#[derive(Debug, Default)]
pub struct AdmissionRegistry {
    controllers: Mutex<HashMap<String, Arc<AdmissionController>>>,
    limits: Mutex<AdmissionLimits>,
}

impl AdmissionRegistry {
    #[must_use]
    pub fn new(limits: AdmissionLimits) -> Self {
        Self {
            controllers: Mutex::new(HashMap::new()),
            limits: Mutex::new(limits),
        }
    }

    /// Apply `limits` to every provider when they changed.
    pub fn apply_limits(&self, limits: &AdmissionLimits) {
        {
            let mut current = self.limits.lock().unwrap_or_else(PoisonError::into_inner);
            if *current == *limits {
                return;
            }
            current.clone_from(limits);
        }
        let controllers: Vec<Arc<AdmissionController>> = self
            .controllers
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .values()
            .cloned()
            .collect();
        for controller in controllers {
            controller.set_limits(limits);
        }
    }

    /// The controller of `provider_id`.
    #[must_use]
    pub fn controller(&self, provider_id: &str) -> Arc<AdmissionController> {
        let mut controllers = self
            .controllers
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        if let Some(controller) = controllers.get(provider_id) {
            return Arc::clone(controller);
        }
        let limits = self
            .limits
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        let controller = AdmissionController::new(provider_id, &limits);
        controllers.insert(provider_id.to_owned(), Arc::clone(&controller));
        controller
    }

    /// Take a slot of `request.provider_id` in the request's class,
    /// waiting in the provider's queue when it has to (the request's notice
    /// fires then), under the limits applied last.
    ///
    /// # Errors
    ///
    /// [`AdmissionError::QueueFull`] when `providerMaxQueued` interactive
    /// requests already wait.
    #[tracing::instrument(
        level = "debug",
        skip_all,
        fields(provider = %request.provider_id, priority = ?request.priority)
    )]
    pub async fn acquire(&self, request: AdmissionRequest) -> Result<ModelPermit, AdmissionError> {
        let permit = match self
            .controller(&request.provider_id)
            .admit(request.priority)?
        {
            Admission::Granted(permit) => permit,
            Admission::Queued(waiting) => {
                request.on_queued.notify();
                waiting.await
            }
        };
        let preempted = permit.preemption();
        Ok(ModelPermit::preemptible(permit, preempted))
    }
}

/// Called once when a request has to wait for its provider (the roster
/// shows the agent as queued).
pub struct QueuedNotice(Box<dyn FnOnce() + Send>);

impl QueuedNotice {
    #[must_use]
    pub fn new(notify: impl FnOnce() + Send + 'static) -> Self {
        Self(Box::new(notify))
    }

    /// Report that the request waits.
    pub fn notify(self) {
        (self.0)();
    }
}

/// One admitted model request: the provider slot stays taken until this
/// drops, or until the admission preempts it. What holds the slot is the
/// admission's business (a process-local [`ProviderPermit`], or the
/// supervisor connection of a daemon worker).
pub struct ModelPermit {
    _held: Box<dyn Send>,
    preempted: CancellationToken,
}

impl ModelPermit {
    /// A permit holding `held` until it drops, never preempted.
    #[must_use]
    pub fn holding(held: impl Send + 'static) -> Self {
        Self::preemptible(held, CancellationToken::new())
    }

    /// A permit holding `held` until it drops, preempted once `preempted`
    /// is cancelled.
    #[must_use]
    pub fn preemptible(held: impl Send + 'static, preempted: CancellationToken) -> Self {
        Self {
            _held: Box::new(held),
            preempted,
        }
    }

    /// Resolves once an interactive request took the slot back (only a
    /// background permit is ever preempted): the slot is no longer held,
    /// and the request must stop at once.
    pub fn preempted(&self) -> WaitForCancellationFuture<'_> {
        self.preempted.cancelled()
    }
}

/// One model request asking for admission.
pub struct AdmissionRequest {
    /// The provider the request goes to.
    pub provider_id: String,
    /// The request's class.
    pub priority: AdmissionPriority,
    /// Fired when the request has to wait.
    pub on_queued: QueuedNotice,
}

/// The authority model requests ask before they go out to a provider.
/// Implementations admit at most the provider's `providerMaxInFlight`
/// requests at once across every process they cover (an unlimited
/// provider admits every request at once), queue the rest in arrival
/// order within each [`AdmissionPriority`], fire the request's
/// [`QueuedNotice`] when it has to wait, and fail with
/// [`AdmissionError::QueueFull`] once `providerMaxQueued` interactive
/// requests wait. A background request waits while an interactive request
/// of its provider holds or waits for a slot, and its [`ModelPermit`] is
/// preempted (see [`ModelPermit::preempted`]) when one comes. The
/// returned permit frees the slot when dropped, and a dropped `acquire`
/// future gives up its place in the queue. The daemon supervisor owns the
/// registry of a daemon, and its workers implement it over their
/// supervisor link; [`LocalAdmission`] is the in-process authority of a
/// run without a daemon.
pub trait ProviderAdmission: Send + Sync {
    /// Wait for a slot of `request.provider_id`.
    fn acquire(
        &self,
        request: AdmissionRequest,
    ) -> impl Future<Output = Result<ModelPermit, AdmissionError>> + Send;
}

type AcquireFn = Arc<
    dyn Fn(AdmissionRequest) -> BoxFuture<'static, Result<ModelPermit, AdmissionError>>
        + Send
        + Sync,
>;

/// A [`ProviderAdmission`] as a session takes it (type-erased).
#[derive(Clone)]
pub struct AdmissionHandle {
    acquire: AcquireFn,
}

impl AdmissionHandle {
    #[must_use]
    pub fn new<A: ProviderAdmission + 'static>(admission: Arc<A>) -> Self {
        Self {
            acquire: Arc::new(move |request| {
                let admission = Arc::clone(&admission);
                async move { admission.acquire(request).await }.boxed()
            }),
        }
    }

    /// See [`ProviderAdmission::acquire`].
    #[must_use]
    pub fn acquire(
        &self,
        request: AdmissionRequest,
    ) -> BoxFuture<'static, Result<ModelPermit, AdmissionError>> {
        (self.acquire)(request)
    }
}

/// The in-process admission authority: one [`AdmissionRegistry`] for the
/// process, its limits re-applied from the caller's settings on every
/// request.
pub struct LocalAdmission {
    registry: Arc<AdmissionRegistry>,
    limits: Box<dyn Fn() -> AdmissionLimits + Send + Sync>,
}

impl LocalAdmission {
    /// An authority over `registry` reading its limits from `limits`.
    #[must_use]
    pub fn new(
        registry: Arc<AdmissionRegistry>,
        limits: impl Fn() -> AdmissionLimits + Send + Sync + 'static,
    ) -> Self {
        Self {
            registry,
            limits: Box::new(limits),
        }
    }
}

impl ProviderAdmission for LocalAdmission {
    #[tracing::instrument(level = "debug", skip_all, fields(provider = %request.provider_id))]
    async fn acquire(&self, request: AdmissionRequest) -> Result<ModelPermit, AdmissionError> {
        self.registry.apply_limits(&(self.limits)());
        self.registry.acquire(request).await
    }
}

/// The registry every in-process session of this process shares.
static LOCAL_REGISTRY: LazyLock<Arc<AdmissionRegistry>> =
    LazyLock::new(|| Arc::new(AdmissionRegistry::default()));

/// The in-process authority over this process's shared registry.
#[must_use]
pub fn local_admission(
    limits: impl Fn() -> AdmissionLimits + Send + Sync + 'static,
) -> AdmissionHandle {
    AdmissionHandle::new(Arc::new(LocalAdmission::new(
        Arc::clone(&LOCAL_REGISTRY),
        limits,
    )))
}

#[cfg(test)]
mod bridge;

#[cfg(test)]
mod tests;
