//! The session's side of provider admission ([`crate::admission`]): every
//! model request to a provider with a `providerMaxInFlight` limit first
//! takes a slot from the session's [`AdmissionHandle`] and keeps it until
//! its stream ends (done, error, abort, or a dropped consumer). Requests to
//! unlimited providers go out untouched.
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
use eukhe_chord::context::AbortSignal;
use eukhe_types::daemon::agent_roster::ModelAdmission;
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
    fn limits(&self, provider_id: &str) -> bool {
        self.settings
            .manager()
            .get_admission_limits()
            .max_in_flight(provider_id)
            .is_some()
    }

    /// The stream of one gated request: a slot first (abortable through
    /// `signal`), then `start`'s stream forwarded while the slot is held.
    /// Must be called inside a tokio runtime (the provider contract runs
    /// every request on one).
    fn admitted(
        self: &Arc<Self>,
        provider_id: &str,
        model: &Model,
        context: &TranscriptContext,
        signal: Option<AbortSignal>,
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
            let acquire = gate.admission.acquire(AdmissionRequest {
                provider_id,
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
        adjustments: Vec::new(),
        usage: Usage::default(),
        stop_reason,
        deferred: None,
        error_message: Some(error_message),
        raw_stop_reason: None,
        end_turn: None,
        timestamp,
        duration_ms: None,
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
        if !gate.limits(&provider_id) {
            return inner(model, context, options);
        }
        let signal = options.stream.request.signal.clone();
        let inner = Arc::clone(&inner);
        gate.admitted(
            &provider_id,
            model,
            context,
            signal,
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
        if !gate.limits(&provider_id) {
            return inner(model, context, options);
        }
        let signal = options.stream.request.signal.clone();
        let inner = Arc::clone(&inner);
        gate.admitted(
            &provider_id,
            model,
            context,
            signal,
            move |model, context| inner(model, context, options),
        )
    })
}

#[cfg(test)]
mod tests;
