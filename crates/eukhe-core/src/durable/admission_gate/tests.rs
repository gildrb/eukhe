//! The session gate over a shared in-process authority: limited providers
//! run at most their limit, a waiting session reports `queued`, an abort
//! leaves the queue, and a full queue fails the request at once.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use eukhe_ai::api::StreamFn;
use eukhe_ai::providers::faux::{faux_assistant_message, FauxAssistantMessageOptions};
use eukhe_ai::types::ProviderStreamOptions;
use eukhe_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_chord::context::AbortController;
use eukhe_types::daemon::agent_roster::ModelAdmission;
use eukhe_types::pi_ai::{
    AssistantMessageEvent, DoneReason, Model, ModelCost, StopReason, TranscriptContext,
};
use tempfile::TempDir;

use super::{gate_stream_fn, AdmissionGate, AdmissionStateSink};
use crate::admission::{AdmissionHandle, AdmissionRegistry, LocalAdmission};
use crate::durable::settings::EukheSettings;

/// A settings pair whose global document sets the admission limits.
fn settings(document: &serde_json::Value) -> (Arc<EukheSettings>, TempDir) {
    let dir = TempDir::new().unwrap();
    let agent_dir = dir.path().join("agent");
    let cwd = dir.path().join("work");
    std::fs::create_dir_all(&agent_dir).unwrap();
    std::fs::create_dir_all(&cwd).unwrap();
    std::fs::write(agent_dir.join("settings.json"), document.to_string()).unwrap();
    (Arc::new(EukheSettings::new(cwd, agent_dir)), dir)
}

/// The provider side: every call counts while its stream is open; the
/// test ends streams through `open`.
#[derive(Default)]
struct Provider {
    in_flight: AtomicUsize,
    peak: AtomicUsize,
    calls: AtomicUsize,
    open: Mutex<Vec<AssistantMessageEventStream>>,
}

impl Provider {
    fn stream_fn(self: &Arc<Self>) -> StreamFn {
        let provider = Arc::clone(self);
        Arc::new(move |_model, _context, _options| {
            provider.calls.fetch_add(1, Ordering::SeqCst);
            let now = provider.in_flight.fetch_add(1, Ordering::SeqCst) + 1;
            provider.peak.fetch_max(now, Ordering::SeqCst);
            let stream = AssistantMessageEventStream::new();
            provider.open.lock().unwrap().push(stream.clone());
            stream
        })
    }

    /// End the oldest open stream with a stop.
    fn finish_one(&self) {
        let stream = self.open.lock().unwrap().remove(0);
        self.in_flight.fetch_sub(1, Ordering::SeqCst);
        stream.push(AssistantMessageEvent::Done {
            reason: DoneReason::Stop,
            message: faux_assistant_message(
                "done",
                FauxAssistantMessageOptions {
                    timestamp: Some(0),
                    ..Default::default()
                },
            ),
        });
        stream.end(None);
    }
}

fn recording_sink() -> (AdmissionStateSink, Arc<Mutex<Vec<Option<ModelAdmission>>>>) {
    let seen = Arc::new(Mutex::new(Vec::new()));
    let sink_seen = Arc::clone(&seen);
    let sink: AdmissionStateSink = Arc::new(move |state| sink_seen.lock().unwrap().push(state));
    (sink, seen)
}

fn model(provider: &str) -> Model {
    Model {
        id: "m".to_string(),
        name: "m".to_string(),
        api: "test".to_string(),
        provider: provider.to_string(),
        base_url: "http://localhost:0".to_string(),
        input: Vec::new(),
        input_limits: None,
        cost: ModelCost::default(),
        headers: None,
        model_type: None,
        reasoning: false,
        thinking_level_map: None,
        prompt_cache: None,
        context_window: 1,
        max_tokens: 1,
        sampling_params: None,
        sampling_params_by_thinking_level: None,
        compat: None,
        featured: None,
    }
}

fn call(
    stream: &StreamFn,
    provider: &str,
    options: ProviderStreamOptions,
) -> AssistantMessageEventStream {
    stream(
        &model(provider),
        &TranscriptContext::from_normalized_messages(Vec::new()),
        options,
    )
}

async fn settle() {
    for _ in 0..50 {
        tokio::task::yield_now().await;
    }
}

#[tokio::test]
async fn sessions_share_the_limit_and_a_waiting_session_reports_queued() {
    let (settings, _dir) = settings(&serde_json::json!({ "providerMaxInFlight": { "test": 1 } }));
    let registry = Arc::new(AdmissionRegistry::default());
    let limits_settings = Arc::clone(&settings);
    let admission = AdmissionHandle::new(Arc::new(LocalAdmission::new(registry, move || {
        limits_settings.manager().get_admission_limits()
    })));
    let provider = Arc::new(Provider::default());
    let (sink_a, seen_a) = recording_sink();
    let (sink_b, seen_b) = recording_sink();
    let gate_a = AdmissionGate::new(admission.clone(), Arc::clone(&settings), Some(sink_a));
    let gate_b = AdmissionGate::new(admission, Arc::clone(&settings), Some(sink_b));
    let stream_a = gate_stream_fn(gate_a, "test".to_owned(), provider.stream_fn());
    let stream_b = gate_stream_fn(gate_b, "test".to_owned(), provider.stream_fn());

    let first = call(&stream_a, "test", ProviderStreamOptions::default());
    settle().await;
    let second = call(&stream_b, "test", ProviderStreamOptions::default());
    let third = call(&stream_a, "test", ProviderStreamOptions::default());
    settle().await;
    assert_eq!(provider.calls.load(Ordering::SeqCst), 1);
    assert_eq!(*seen_b.lock().unwrap(), vec![Some(ModelAdmission::Queued)]);

    provider.finish_one();
    assert_eq!(first.result().await.stop_reason, StopReason::Stop);
    settle().await;
    provider.finish_one();
    assert_eq!(second.result().await.stop_reason, StopReason::Stop);
    settle().await;
    provider.finish_one();
    assert_eq!(third.result().await.stop_reason, StopReason::Stop);
    settle().await;

    assert_eq!(
        (
            provider.calls.load(Ordering::SeqCst),
            provider.peak.load(Ordering::SeqCst)
        ),
        (3, 1)
    );
    // Session A: generating while its first request runs (its waiting
    // third request never outranks a held slot), queued once the first
    // ended and the slot went to B, generating again, then idle.
    assert_eq!(
        *seen_a.lock().unwrap(),
        vec![
            Some(ModelAdmission::Generating),
            Some(ModelAdmission::Queued),
            Some(ModelAdmission::Generating),
            None
        ]
    );
    assert_eq!(
        *seen_b.lock().unwrap(),
        vec![
            Some(ModelAdmission::Queued),
            Some(ModelAdmission::Generating),
            None
        ]
    );
}

#[tokio::test]
async fn an_unlimited_provider_is_not_gated() {
    let (settings, _dir) = settings(&serde_json::json!({ "providerMaxInFlight": { "test": 1 } }));
    let limits_settings = Arc::clone(&settings);
    let admission = AdmissionHandle::new(Arc::new(LocalAdmission::new(
        Arc::new(AdmissionRegistry::default()),
        move || limits_settings.manager().get_admission_limits(),
    )));
    let provider = Arc::new(Provider::default());
    let (sink, seen) = recording_sink();
    let gate = AdmissionGate::new(admission, settings, Some(sink));
    let stream = gate_stream_fn(gate, "other".to_owned(), provider.stream_fn());
    let _streams: Vec<AssistantMessageEventStream> = (0..3)
        .map(|_| call(&stream, "other", ProviderStreamOptions::default()))
        .collect();
    // The calls reach the provider synchronously: no slot, no state.
    assert_eq!(
        (
            provider.peak.load(Ordering::SeqCst),
            seen.lock().unwrap().clone()
        ),
        (3, Vec::new())
    );
}

#[tokio::test]
async fn an_abort_while_queued_fails_the_request_without_a_slot() {
    let (settings, _dir) = settings(&serde_json::json!({ "providerMaxInFlight": { "test": 1 } }));
    let limits_settings = Arc::clone(&settings);
    let admission = AdmissionHandle::new(Arc::new(LocalAdmission::new(
        Arc::new(AdmissionRegistry::default()),
        move || limits_settings.manager().get_admission_limits(),
    )));
    let provider = Arc::new(Provider::default());
    let (sink, seen) = recording_sink();
    let gate = AdmissionGate::new(admission, settings, Some(sink));
    let stream = gate_stream_fn(gate, "test".to_owned(), provider.stream_fn());
    let held = call(&stream, "test", ProviderStreamOptions::default());
    settle().await;
    let controller = AbortController::new();
    let mut options = ProviderStreamOptions::default();
    options.stream.request.signal = Some(controller.signal());
    let waiting = call(&stream, "test", options);
    settle().await;
    controller.abort(None);
    let aborted = waiting.result().await;
    assert_eq!(
        (aborted.stop_reason, aborted.error_message.as_deref()),
        (StopReason::Aborted, Some("Request was aborted"))
    );
    provider.finish_one();
    held.result().await;
    settle().await;
    assert_eq!(
        (
            provider.calls.load(Ordering::SeqCst),
            seen.lock().unwrap().clone()
        ),
        (1, vec![Some(ModelAdmission::Generating), None])
    );
}

#[tokio::test]
async fn a_full_queue_fails_the_request_at_once() {
    let (settings, _dir) = settings(&serde_json::json!({
        "providerMaxInFlight": { "test": 1 },
        "providerMaxQueued": 0,
    }));
    let limits_settings = Arc::clone(&settings);
    let admission = AdmissionHandle::new(Arc::new(LocalAdmission::new(
        Arc::new(AdmissionRegistry::default()),
        move || limits_settings.manager().get_admission_limits(),
    )));
    let provider = Arc::new(Provider::default());
    let gate = AdmissionGate::new(admission, settings, None);
    let stream = gate_stream_fn(gate, "test".to_owned(), provider.stream_fn());
    let _held = call(&stream, "test", ProviderStreamOptions::default());
    settle().await;
    let rejected = call(&stream, "test", ProviderStreamOptions::default())
        .result()
        .await;
    assert_eq!(
        (rejected.stop_reason, rejected.error_message.as_deref()),
        (
            StopReason::Error,
            Some(
                "provider admission queue is full for test: 0 requests already wait \
                 (providerMaxQueued)"
            )
        )
    );
    assert!(!eukhe_ai::utils::retry::is_retryable_assistant_error(
        &rejected
    ));
}
