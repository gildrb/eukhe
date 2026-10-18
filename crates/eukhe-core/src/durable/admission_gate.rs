//! The session's side of provider admission ([`crate::admission`]): every
//! model request first takes an interactive slot of its provider from the
//! session's [`AdmissionHandle`] and keeps it until its stream ends (done,
//! error, abort, or a dropped consumer). A limited provider
//! (`providerMaxInFlight`) runs at most its limit; an unlimited one admits
//! at once, and its slot only tells the chat-memory compactor's background
//! requests to stand aside. When the authority cannot be asked (the
//! daemon supervisor is unreachable), a request to an unlimited provider
//! goes out without a slot; one to a limited provider fails.
//!
//! The gate wraps each provider row INNERMOST (under the provider runtime's
//! failover and quota-park wrappers): a failover re-dispatch takes a slot
//! of the provider it goes to, and no slot is held while a wrapper sleeps
//! between attempts.
//!
//! The session reports where its requests stand through the
//! [`AdmissionStateSink`]: `queued` while one waits for a slot (and none
//! holds one), `generating` while one holds a slot, nothing otherwise.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::api::{StreamFn, StreamSimpleFn};
use eukhe_ai::models::Models;
use eukhe_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_ai::utils::stream_idle::StreamClock;
use eukhe_chord::context::AbortSignal;
use eukhe_types::daemon::agent_roster::ModelAdmission;
use eukhe_types::daemon::AdmissionPriority;
use eukhe_types::pi_ai::{
    AssistantMessage, AssistantMessageEvent, ErrorReason, Model, StopReason, TranscriptContext,
    Usage,
};
use futures::StreamExt as _;

use super::settings::EukheSettings;
use crate::admission::{AdmissionHandle, AdmissionRequest, QueuedNotice};

/// Receives the session's admission state whenever it changes (`None`: no
/// request waits for or holds a slot). Called synchronously in change
/// order; it must not block.
pub type AdmissionStateSink = Arc<dyn Fn(Option<ModelAdmission>) + Send + Sync>;

/// Where one gated request stands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Phase {
    /// Asking for a slot, not (yet) known to wait.
    Asking,
    Queued,
    Generating,
}

/// The phases of the session's gated requests, folded into one state.
struct Tracker {
    requests: Mutex<TrackerState>,
    sink: Option<AdmissionStateSink>,
    next_id: AtomicU64,
}

#[derive(Default)]
struct TrackerState {
    phases: HashMap<u64, Phase>,
    reported: Option<ModelAdmission>,
}

impl Tracker {
    /// Move request `id` to `phase` (`None` removes it) and report the
    /// session state when it changed. The sink runs under the lock so the
    /// reports keep their order.
    fn set(&self, id: u64, phase: Option<Phase>) {
        let mut state = self.requests.lock().unwrap_or_else(PoisonError::into_inner);
        match phase {
            Some(phase) => {
                state.phases.insert(id, phase);
            }
            None => {
                state.phases.remove(&id);
            }
        }
        let phases = || state.phases.values();
        let current = if phases().any(|phase| *phase == Phase::Generating) {
            Some(ModelAdmission::Generating)
        } else if phases().any(|phase| *phase == Phase::Queued) {
            Some(ModelAdmission::Queued)
        } else {
            None
        };
        if current == state.reported {
            return;
        }
        state.reported = current;
        if let Some(sink) = &self.sink {
            sink(current);
        }
    }
}

/// One gated request's place in the tracker; dropping it removes it.
struct Tracked {
    tracker: Arc<Tracker>,
    id: u64,
}

impl Tracked {
    fn new(tracker: &Arc<Tracker>) -> Self {
        let id = tracker.next_id.fetch_add(1, Ordering::Relaxed);
        tracker.set(id, Some(Phase::Asking));
        Self {
            tracker: Arc::clone(tracker),
            id,
        }
    }

    fn queued_notice(&self) -> QueuedNotice {
        let tracker = Arc::clone(&self.tracker);
        let id = self.id;
        QueuedNotice::new(move || tracker.set(id, Some(Phase::Queued)))
    }

    fn generating(&self) {
        self.tracker.set(self.id, Some(Phase::Generating));
    }
}

impl Drop for Tracked {
    fn drop(&mut self) {
        self.tracker.set(self.id, None);
    }
}

/// The admission gate of one session.
pub(crate) struct AdmissionGate {
    admission: AdmissionHandle,
    settings: Arc<EukheSettings>,
    tracker: Arc<Tracker>,
}

impl AdmissionGate {
    pub(crate) fn new(
        admission: AdmissionHandle,
        settings: Arc<EukheSettings>,
        sink: Option<AdmissionStateSink>,
    ) -> Arc<Self> {
        Arc::new(Self {
            admission,
            settings,
            tracker: Arc::new(Tracker {
                requests: Mutex::new(TrackerState::default()),
                sink,
                next_id: AtomicU64::new(0),
            }),
        })
    }

    /// Whether requests to `provider_id` are limited (the current global
    /// settings; a changed file applies to the next request).
    fn limited(&self, provider_id: &str) -> bool {
        self.settings
            .manager()
            .get_admission_limits()
            .max_in_flight(provider_id)
            .is_some()
    }

    /// The stream of one gated request: a slot first (abortable through
    /// `signal`), then `start`'s stream forwarded while the slot is held.
    /// The stream's idle `clock` is held while the request waits for its
    /// slot: a queue is not a stall (H6.3). Must be called inside a tokio
    /// runtime (the provider contract runs every request on one).
    fn admitted(
        self: &Arc<Self>,
        provider_id: &str,
        model: &Model,
        context: &TranscriptContext,
        signal: Option<AbortSignal>,
        clock: Option<StreamClock>,
        start: impl FnOnce(&Model, &TranscriptContext) -> AssistantMessageEventStream + Send + 'static,
    ) -> AssistantMessageEventStream {
        let outer = AssistantMessageEventStream::new();
        let sink = outer.clone();
        let gate = Arc::clone(self);
        let provider_id = provider_id.to_owned();
        let model = model.clone();
        let context = context.clone();
        tokio::spawn(async move {
            let tracked = Tracked::new(&gate.tracker);
            let queued = clock.as_ref().map(StreamClock::hold);
            let acquire = gate.admission.acquire(AdmissionRequest {
                provider_id: provider_id.clone(),
                priority: AdmissionPriority::Interactive,
                on_queued: tracked.queued_notice(),
            });
            let acquired = match &signal {
                Some(signal) => {
                    let aborted = signal.cancellation_token();
                    tokio::select! {
                        biased;
                        () = aborted.cancelled() => None,
                        acquired = acquire => Some(acquired),
                    }
                }
                None => Some(acquire.await),
            };
            drop(queued);
            let permit = match acquired {
                None => {
                    let message = failure(
                        &model,
                        StopReason::Aborted,
                        "Request was aborted".to_owned(),
                    );
                    sink.push(AssistantMessageEvent::Error {
                        reason: ErrorReason::Aborted,
                        error: message,
                    });
                    sink.end(None);
                    return;
                }
                Some(Err(error)) => {
                    let message = failure(&model, StopReason::Error, error.to_string());
                    sink.push(AssistantMessageEvent::Error {
                        reason: ErrorReason::Error,
                        error: message,
                    });
                    sink.end(None);
                    return;
                }
                Some(Ok(permit)) => permit,
            };
            tracked.generating();
            let inner = start(&model, &context);
            let mut events = inner.events();
            while let Some(event) = events.next().await {
                sink.push(event);
            }
            sink.end(None);
            drop(permit);
            drop(tracked);
        });
        outer
    }

    /// The stream of a request to an unlimited provider: it goes out at
    /// once, as an ungated request does, while an interactive slot is
    /// taken alongside it, only so the chat-memory compactor's background
    /// requests stand aside. The slot (or its pending acquire) is let go
    /// when the stream ends; when the authority cannot be asked, the
    /// request runs without one.
    fn alongside(
        self: &Arc<Self>,
        provider_id: &str,
        inner: AssistantMessageEventStream,
    ) -> AssistantMessageEventStream {
        let outer = AssistantMessageEventStream::new();
        let sink = outer.clone();
        let gate = Arc::clone(self);
        let provider_id = provider_id.to_owned();
        tokio::spawn(async move {
            let tracked = Tracked::new(&gate.tracker);
            tracked.generating();
            let slot = tokio::spawn(gate.admission.acquire(AdmissionRequest {
                provider_id: provider_id.clone(),
                priority: AdmissionPriority::Interactive,
                on_queued: tracked.queued_notice(),
            }));
            let mut events = inner.events();
            while let Some(event) = events.next().await {
                sink.push(event);
            }
            sink.end(None);
            slot.abort();
            match slot.await {
                Ok(Ok(permit)) => drop(permit),
                Ok(Err(error)) => tracing::warn!(
                    provider = %provider_id,
                    "{error}; the request to the unlimited provider ran without a slot"
                ),
                Err(cancelled) => tracing::debug!(
                    provider = %provider_id,
                    "the unlimited provider's slot was still pending: {cancelled}"
                ),
            }
            drop(tracked);
        });
        outer
    }
}

/// A request that never reached its provider.
fn failure(model: &Model, stop_reason: StopReason, error_message: String) -> AssistantMessage {
    let timestamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |elapsed| {
            u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX)
        });
    AssistantMessage {
        content: Vec::new(),
        api: model.api.clone(),
        provider: model.provider.clone(),
        model: model.id.clone(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage::default(),
        stop_reason,
        deferred: None,
        error_message: Some(error_message),
        raw_stop_reason: None,
        end_turn: None,
        timestamp,
        duration_ms: None,
        timing: None,
    }
}

/// Gate every provider row of `models` (re-wrapped in place).
pub(crate) fn wrap_models_with_admission(models: &Models, gate: &Arc<AdmissionGate>) {
    for provider in models.get_providers() {
        let mut provider = (*provider).clone();
        provider.stream = gate_stream_fn(Arc::clone(gate), provider.id.clone(), provider.stream);
        provider.stream_simple = gate_stream_simple_fn(
            Arc::clone(gate),
            provider.id.clone(),
            provider.stream_simple,
        );
        models.set_provider(provider);
    }
}

fn gate_stream_fn(gate: Arc<AdmissionGate>, provider_id: String, inner: StreamFn) -> StreamFn {
    Arc::new(move |model, context, options| {
        if !gate.limited(&provider_id) {
            return gate.alongside(&provider_id, inner(model, context, options));
        }
        let signal = options.stream.request.signal.clone();
        let clock = options.stream.request.stream_clock.clone();
        let inner = Arc::clone(&inner);
        gate.admitted(
            &provider_id,
            model,
            context,
            signal,
            clock,
            move |model, context| inner(model, context, options),
        )
    })
}

fn gate_stream_simple_fn(
    gate: Arc<AdmissionGate>,
    provider_id: String,
    inner: StreamSimpleFn,
) -> StreamSimpleFn {
    Arc::new(move |model, context, options| {
        if !gate.limited(&provider_id) {
            return gate.alongside(&provider_id, inner(model, context, options));
        }
        let signal = options.stream.request.signal.clone();
        let clock = options.stream.request.stream_clock.clone();
        let inner = Arc::clone(&inner);
        gate.admitted(
            &provider_id,
            model,
            context,
            signal,
            clock,
            move |model, context| inner(model, context, options),
        )
    })
}

#[cfg(test)]
mod tests;
