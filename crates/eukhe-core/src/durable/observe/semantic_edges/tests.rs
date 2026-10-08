//! The semantic-edge recorder battery: the ledger lifecycle and replay,
//! retry parking, the torn-tail rule, and the stream wrapper.

use std::sync::{Arc, Mutex};

use eukhe_pi_ai::api::StreamFn;
use eukhe_pi_ai::providers::faux::{faux_assistant_message, FauxAssistantMessageOptions};
use eukhe_pi_ai::types::ProviderStreamOptions;
use eukhe_pi_ai::utils::event_stream::AssistantMessageEventStream;
use eukhe_types::pi_ai::{
    DoneReason, ErrorReason, Model, ModelCost, StopReason, TranscriptContext,
};
use tempfile::TempDir;

use super::{
    wrap_stream_fn, SemanticEdgeIdentity, SemanticEdgeLedgerEvent, SemanticEdgeRecorder,
    IDEMPOTENCY_KEY_HEADER, MODEL_REQUEST_ID_HEADER,
};

const FINGERPRINT_A: [u8; 32] = [1; 32];
const FINGERPRINT_B: [u8; 32] = [2; 32];

/// One identity over a fresh tempdir ledger.
fn identity(session_id: &str) -> (SemanticEdgeIdentity, TempDir) {
    let dir = TempDir::new().unwrap();
    let identity = SemanticEdgeIdentity {
        session_id: session_id.to_string(),
        ledger_path: Some(dir.path().join(super::SEMANTIC_EDGES_LEDGER_FILENAME)),
        parent_session_id: Some("parent-session".to_string()),
        spawned_by_request_id: Some("parent-request".to_string()),
    };
    (identity, dir)
}

fn read_ledger(identity: &SemanticEdgeIdentity) -> Vec<SemanticEdgeLedgerEvent> {
    super::ledger::read_events(identity.ledger_path.as_ref().unwrap())
        .unwrap()
        .unwrap_or_default()
}

fn session_registered(session_id: &str) -> SemanticEdgeLedgerEvent {
    SemanticEdgeLedgerEvent::SessionRegistered {
        session_id: session_id.to_string(),
        parent_session_id: Some("parent-session".to_string()),
        spawned_by_request_id: Some("parent-request".to_string()),
    }
}

fn request_started(session_id: &str, request_id: &str) -> SemanticEdgeLedgerEvent {
    SemanticEdgeLedgerEvent::RequestStarted {
        request_id: request_id.to_string(),
        session_id: session_id.to_string(),
        compaction_id: None,
    }
}

#[test]
fn a_turn_lifecycle_is_ledgered_and_reopening_replays_without_reregistering() {
    let (identity, _dir) = identity("session-a");
    let recorder = SemanticEdgeRecorder::open(identity.clone());
    let first = recorder
        .start_turn_request(FINGERPRINT_A)
        .expect("the recorder mints ids");
    recorder.finish_request(&first);
    let second = recorder
        .start_turn_request(FINGERPRINT_A)
        .expect("the recorder mints ids");
    recorder.fail_request(&second);
    drop(recorder);
    // Reopen: the ledger replays without re-registering, and the last
    // replayed request_started restores the in-flight turn a resumed
    // child's spawn anchors to.
    let reopened = SemanticEdgeRecorder::open(identity.clone());
    assert_eq!(
        reopened.last_turn_request_id().as_deref(),
        Some(second.as_str())
    );
    assert_eq!(
        read_ledger(&identity),
        vec![
            session_registered("session-a"),
            request_started("session-a", &first),
            SemanticEdgeLedgerEvent::RequestFinished {
                request_id: first.clone(),
            },
            request_started("session-a", &second),
            SemanticEdgeLedgerEvent::RequestFailed { request_id: second },
        ]
    );
}

#[test]
fn a_parked_retry_reuses_its_id_only_for_an_identical_body() {
    let (identity, _dir) = identity("session-b");
    let recorder = Arc::new(SemanticEdgeRecorder::open(identity.clone()));
    let first = recorder
        .start_turn_request(FINGERPRINT_A)
        .expect("the recorder mints ids");
    // The parked retry reuses the id for the identical body and re-logs
    // its request_started; a different body mints a fresh id.
    recorder.prepare_turn_retry();
    assert_eq!(
        recorder.start_turn_request(FINGERPRINT_A).as_deref(),
        Some(first.as_str())
    );
    let different_body = recorder
        .start_turn_request(FINGERPRINT_B)
        .expect("the recorder mints ids");
    assert_ne!(different_body, first);
    assert_eq!(
        read_ledger(&identity),
        vec![
            session_registered("session-b"),
            request_started("session-b", &first),
            request_started("session-b", &first),
            request_started("session-b", &different_body),
        ]
    );
}

#[test]
fn a_ledger_failure_drops_the_spawn_anchor() {
    let (identity, _dir) = identity("session-e");
    let recorder = SemanticEdgeRecorder::open(identity.clone());
    recorder
        .start_turn_request(FINGERPRINT_A)
        .expect("the recorder mints ids");
    // A directory at the ledger path fails the next append (works as
    // root too).
    let path = identity.ledger_path.as_ref().unwrap();
    std::fs::remove_file(path).unwrap();
    std::fs::create_dir(path).unwrap();
    assert_eq!(
        (
            recorder.start_turn_request(FINGERPRINT_B),
            recorder.last_turn_request_id()
        ),
        (None, None)
    );
}

#[test]
fn a_torn_final_line_is_ignored_on_replay_and_truncated_before_the_next_append() {
    let (identity, _dir) = identity("session-c");
    let registered = session_registered("session-c");
    let mut torn = serde_json::to_string(&registered).unwrap();
    torn.push('\n');
    torn.push_str("{\"type\":\"request_st");
    std::fs::write(identity.ledger_path.as_ref().unwrap(), torn).unwrap();
    // The replay skips the unterminated final line even though its prefix
    // parses: no turn is restored.
    let recorder = SemanticEdgeRecorder::open(identity.clone());
    assert_eq!(recorder.last_turn_request_id(), None);
    let request_id = recorder
        .start_turn_request(FINGERPRINT_A)
        .expect("the recorder mints ids");
    // The append truncated the torn tail at its byte offset first: the
    // file bytes are exactly the registered line and the new event.
    let mut expected = serde_json::to_string(&registered).unwrap().into_bytes();
    expected.push(b'\n');
    expected.extend(
        serde_json::to_string(&request_started("session-c", &request_id))
            .unwrap()
            .into_bytes(),
    );
    expected.push(b'\n');
    let bytes = std::fs::read(identity.ledger_path.as_ref().unwrap()).unwrap();
    assert_eq!(bytes, expected);
}

/// A stream fn that records the request options and serves the scripted
/// events as one stream (an empty script serves a closed, unsettled
/// stream).
fn capturing_stream_fn(
    events: Vec<eukhe_types::pi_ai::AssistantMessageEvent>,
) -> (Arc<Mutex<Vec<ProviderStreamOptions>>>, StreamFn) {
    let captured: Arc<Mutex<Vec<ProviderStreamOptions>>> = Arc::new(Mutex::new(Vec::new()));
    let stream_fn: StreamFn = {
        let captured = Arc::clone(&captured);
        Arc::new(
            move |_model: &Model, _context: &TranscriptContext, options: ProviderStreamOptions| {
                captured.lock().unwrap().push(options);
                let stream = AssistantMessageEventStream::new();
                for event in events.clone() {
                    stream.push(event);
                }
                stream.end(None);
                stream
            },
        )
    };
    (captured, stream_fn)
}

fn terminal_event(reason: StopReason) -> eukhe_types::pi_ai::AssistantMessageEvent {
    let message = faux_assistant_message(
        "test",
        FauxAssistantMessageOptions {
            stop_reason: Some(reason),
            timestamp: Some(0),
            ..Default::default()
        },
    );
    match reason {
        StopReason::Error => eukhe_types::pi_ai::AssistantMessageEvent::Error {
            reason: ErrorReason::Error,
            error: message,
        },
        StopReason::Aborted => eukhe_types::pi_ai::AssistantMessageEvent::Error {
            reason: ErrorReason::Aborted,
            error: message,
        },
        _ => eukhe_types::pi_ai::AssistantMessageEvent::Done {
            reason: DoneReason::Stop,
            message,
        },
    }
}

/// The request id a wrapped call carried (both headers present, equal).
fn bound_request_id(captured: &Mutex<Vec<ProviderStreamOptions>>) -> String {
    let options = captured.lock().unwrap().first().expect("one call").clone();
    let headers = options
        .stream
        .request
        .headers
        .expect("the wrapped call carries headers");
    let id = headers
        .get(MODEL_REQUEST_ID_HEADER)
        .and_then(|value| value.as_deref())
        .expect("the request-id header")
        .to_string();
    assert_eq!(
        headers
            .get(IDEMPOTENCY_KEY_HEADER)
            .and_then(|value| value.as_deref()),
        Some(id.as_str())
    );
    assert_eq!(headers.len(), 2);
    id
}

/// The minimal model a wrapped call names (the fingerprint only reads its
/// identity fields).
fn test_model() -> Model {
    Model {
        id: "m".to_string(),
        name: "m".to_string(),
        api: "test".to_string(),
        provider: "test".to_string(),
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
fn wrapped_call(
    recorder: &Arc<SemanticEdgeRecorder>,
    inner: StreamFn,
) -> AssistantMessageEventStream {
    wrap_stream_fn(Arc::clone(recorder), inner)(
        &test_model(),
        &TranscriptContext::from_normalized_messages(Vec::new()),
        ProviderStreamOptions::default(),
    )
}

/// Let the wrapper's forwarding task run to its stream's end.
async fn settle_forwarding_task() {
    for _ in 0..20 {
        tokio::task::yield_now().await;
    }
}

#[tokio::test]
async fn turn_requests_carry_both_headers_and_settle_by_stop_reason() {
    let (identity, _dir) = identity("session-d");
    let recorder = Arc::new(SemanticEdgeRecorder::open(identity.clone()));
    // A stop stream commits, an error stream fails, and a dropped
    // unsettled stream fails.
    let (captured_stop, stop_fn) = capturing_stream_fn(vec![terminal_event(StopReason::Stop)]);
    let (captured_error, error_fn) = capturing_stream_fn(vec![terminal_event(StopReason::Error)]);
    let (captured_dropped, dropped_fn) = capturing_stream_fn(Vec::new());
    let committed_id = {
        let stream = wrapped_call(&recorder, stop_fn);
        let message = stream.result().await;
        assert_eq!(message.stop_reason, StopReason::Stop);
        bound_request_id(&captured_stop)
    };
    let failed_id = {
        let stream = wrapped_call(&recorder, error_fn);
        let message = stream.result().await;
        assert_eq!(message.stop_reason, StopReason::Error);
        bound_request_id(&captured_error)
    };
    let dropped_id = {
        let stream = wrapped_call(&recorder, dropped_fn);
        let id = bound_request_id(&captured_dropped);
        drop(stream);
        settle_forwarding_task().await;
        id
    };
    assert_eq!(
        read_ledger(&identity),
        vec![
            session_registered("session-d"),
            request_started("session-d", &committed_id),
            SemanticEdgeLedgerEvent::RequestFinished {
                request_id: committed_id,
            },
            request_started("session-d", &failed_id),
            SemanticEdgeLedgerEvent::RequestFailed {
                request_id: failed_id,
            },
            request_started("session-d", &dropped_id),
            SemanticEdgeLedgerEvent::RequestFailed {
                request_id: dropped_id,
            },
        ]
    );
}
