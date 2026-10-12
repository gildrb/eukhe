//! Per-provider model-request admission (omp2 `AdmissionController`): a
//! provider with a `providerMaxInFlight` limit serves at most that many
//! requests at once; later requests wait in FIFO order, and once
//! `providerMaxQueued` requests wait the next one fails at once with a
//! non-retryable error.
//!
//! The controller and its registry are process-local. Every eukhe session
//! runs in its own worker process, so the daemon supervisor owns the one
//! registry of a daemon and workers reach it through
//! [`ProviderAdmission`]; a run without a daemon uses
//! [`local_admission`], the same semantics in this process.

use std::collections::{BTreeMap, HashMap, VecDeque};
use std::future::Future;
use std::num::NonZeroU32;
use std::pin::Pin;
use std::sync::{Arc, LazyLock, Mutex, MutexGuard, PoisonError};
use std::task::{Context, Poll, Waker};

use futures::future::BoxFuture;
use futures::FutureExt as _;

/// `providerMaxQueued` default (omp2 `ai_provider_max_queued`).
pub const DEFAULT_PROVIDER_MAX_QUEUED: u32 = 64;

/// The admission limits of every provider: `providerMaxInFlight` and
/// `providerMaxQueued`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdmissionLimits {
    max_in_flight: BTreeMap<String, NonZeroU32>,
    max_queued: u32,
}

impl Default for AdmissionLimits {
    fn default() -> Self {
        Self {
            max_in_flight: BTreeMap::new(),
            max_queued: DEFAULT_PROVIDER_MAX_QUEUED,
        }
    }
}

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
            max_queued: max_queued.unwrap_or(DEFAULT_PROVIDER_MAX_QUEUED),
        }
    }

    /// The in-flight limit of `provider_id`; `None` is unlimited.
    #[must_use]
    pub fn max_in_flight(&self, provider_id: &str) -> Option<NonZeroU32> {
        self.max_in_flight.get(provider_id).copied()
    }

    /// How many requests may wait per provider.
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AdmissionSnapshot {
    /// Requests holding a permit.
    pub active: u32,
    /// Requests waiting for one.
    pub waiting: u32,
}

#[derive(Debug)]
struct WaitSlot {
    granted: bool,
    waker: Option<Waker>,
}

#[derive(Debug)]
struct ControllerState {
    limit: Option<NonZeroU32>,
    queue_limit: u32,
    active: u32,
    next_ticket: u64,
    /// Waiting tickets, oldest first.
    queue: VecDeque<u64>,
    /// Every ticket not yet collected by its waiter: queued ones and
    /// granted ones whose waiter has not polled since the grant.
    slots: HashMap<u64, WaitSlot>,
}

impl ControllerState {
    fn has_room(&self) -> bool {
        self.limit.is_none_or(|limit| self.active < limit.get())
    }

    /// Hand free slots to the oldest waiters (FIFO): each grant moves one
    /// unit of `active` to the waiter. Returns the wakers to fire once the
    /// lock is released.
    fn grant_waiters(&mut self) -> Vec<Waker> {
        let mut wake = Vec::new();
        while self.has_room() {
            let Some(ticket) = self.queue.pop_front() else {
                break;
            };
            let Some(slot) = self.slots.get_mut(&ticket) else {
                continue;
            };
            slot.granted = true;
            self.active += 1;
            wake.extend(slot.waker.take());
        }
        wake
    }

    /// One permit returns: the slot goes to the oldest waiter if any.
    fn release(&mut self) -> Vec<Waker> {
        self.active = self.active.saturating_sub(1);
        self.grant_waiters()
    }
}

/// The admission of one provider (omp2 `AdmissionController`): `active`
/// requests hold permits, `queue` waits for one. A released permit goes
/// straight to the oldest waiter (FIFO-fair, where omp2 wakes every waiter
/// to race for it), so a stream of new requests can never starve an old
/// one. Lowering the limit below `active` lets the excess drain; raising
/// it admits waiters at once.
#[derive(Debug)]
pub struct AdmissionController {
    provider_id: String,
    state: Mutex<ControllerState>,
}

/// The outcome of [`AdmissionController::admit`] that did not fail.
pub enum Admission {
    /// A slot was free.
    Granted(ProviderPermit),
    /// Every slot is taken: the request waits (await the value).
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
                active: 0,
                next_ticket: 0,
                queue: VecDeque::new(),
                slots: HashMap::new(),
            }),
            provider_id,
        })
    }

    fn lock(&self) -> MutexGuard<'_, ControllerState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Take a permit if a slot is free, else join the wait queue.
    ///
    /// # Errors
    ///
    /// [`AdmissionRejected`] when `queue_limit` requests already wait.
    pub fn admit(self: &Arc<Self>) -> Result<Admission, AdmissionRejected> {
        let mut state = self.lock();
        if state.has_room() && state.queue.is_empty() {
            state.active += 1;
            return Ok(Admission::Granted(ProviderPermit {
                controller: Arc::clone(self),
            }));
        }
        let waiting = u32::try_from(state.queue.len()).unwrap_or(u32::MAX);
        if waiting >= state.queue_limit {
            return Err(AdmissionRejected {
                provider_id: self.provider_id.clone(),
                queue_limit: state.queue_limit,
            });
        }
        let ticket = state.next_ticket;
        state.next_ticket += 1;
        state.queue.push_back(ticket);
        state.slots.insert(
            ticket,
            WaitSlot {
                granted: false,
                waker: None,
            },
        );
        Ok(Admission::Queued(QueuedPermit {
            controller: Arc::clone(self),
            ticket,
            collected: false,
        }))
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
            active: state.active,
            waiting: u32::try_from(state.queue.len()).unwrap_or(u32::MAX),
        }
    }

    fn release(&self) {
        let wake = self.lock().release();
        wake.into_iter().for_each(Waker::wake);
    }
}

/// One admitted request; dropping it frees the slot.
#[derive(Debug)]
pub struct ProviderPermit {
    controller: Arc<AdmissionController>,
}

impl Drop for ProviderPermit {
    fn drop(&mut self) {
        self.controller.release();
    }
}

/// A request waiting in a provider's queue; resolves to its permit.
/// Dropping it leaves the queue, and a permit granted but not yet
/// collected goes to the next waiter.
#[derive(Debug)]
pub struct QueuedPermit {
    controller: Arc<AdmissionController>,
    ticket: u64,
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
        if slot.granted {
            state.slots.remove(&this.ticket);
            drop(state);
            this.collected = true;
            return Poll::Ready(ProviderPermit {
                controller: Arc::clone(&this.controller),
            });
        }
        slot.waker = Some(cx.waker().clone());
        Poll::Pending
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
                .is_some_and(|slot| slot.granted);
            if granted {
                state.release()
            } else {
                state.queue.retain(|ticket| *ticket != self.ticket);
                Vec::new()
            }
        };
        wake.into_iter().for_each(Waker::wake);
    }
}

/// The controllers of every provider, created on first use, sharing one
/// set of limits.
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
/// drops. What holds the slot is the admission's business (a process-local
/// [`ProviderPermit`], or the supervisor connection of a daemon worker).
pub struct ModelPermit {
    _held: Box<dyn Send>,
}

impl ModelPermit {
    /// A permit holding `held` until it drops.
    #[must_use]
    pub fn holding(held: impl Send + 'static) -> Self {
        Self {
            _held: Box::new(held),
        }
    }
}

/// One model request asking for admission.
pub struct AdmissionRequest {
    /// The provider the request goes to.
    pub provider_id: String,
    /// Fired when the request has to wait.
    pub on_queued: QueuedNotice,
}

/// The authority a session's model requests ask before they go out to a
/// limited provider. Implementations admit at most the provider's
/// `providerMaxInFlight` requests at once across every process they
/// cover, queue the rest in arrival order, fire the request's
/// [`QueuedNotice`] when it has to wait, and fail with
/// [`AdmissionError::QueueFull`] once `providerMaxQueued` requests wait.
/// The returned [`ModelPermit`] frees the slot when dropped, and a
/// dropped `acquire` future gives up its place in the queue. The daemon
/// worker implements it over its supervisor link; [`LocalAdmission`] is
/// the in-process authority of a run without a daemon.
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
        let controller = self.registry.controller(&request.provider_id);
        match controller.admit()? {
            Admission::Granted(permit) => Ok(ModelPermit::holding(permit)),
            Admission::Queued(waiting) => {
                request.on_queued.notify();
                Ok(ModelPermit::holding(waiting.await))
            }
        }
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
mod tests;
