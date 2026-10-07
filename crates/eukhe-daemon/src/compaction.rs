//! The worker's compaction commands.
//!
//! Port of the TS daemon-mode compaction surface: the `compact` /
//! `abort_compaction` handlers over the durable session ([`durable`]), and
//! the `compaction_start`/`compaction_end` event payloads with their exact
//! TS shapes (shared with the old engine paths).

use std::sync::{Arc, Mutex};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::types::ConversationAbortOptions;
use serde_json::{json, Value};

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::{emit_worker_event_with, EventPump, SessionCore, SessionSlot, Worker};
use durable::{abort_compactions, run_manual_compaction, ManualCompactionError};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// The worker's `compact` / `abort_compaction` commands over the hosted
/// durable session. The `compaction_start`/`compaction_end` frames of a run
/// come from the event bridge (the task's `pi.live` status); only a skip,
/// which starts no task, emits its frame pair here.
pub(crate) struct CompactionManager {
    session: SessionSlot,
    events: Arc<EventPump>,
    core: Arc<Mutex<SessionCore>>,
}

impl CompactionManager {
    pub(crate) fn new(
        session: SessionSlot,
        events: Arc<EventPump>,
        core: Arc<Mutex<SessionCore>>,
    ) -> Self {
        CompactionManager {
            session,
            events,
            core,
        }
    }

    /// `compact` (TS `session.compact(customInstructions)`): abort the
    /// running turn, run one manual compaction, and answer the TS
    /// `CompactionResult`; skips, aborts, and failures answer the session's
    /// error message exactly like the TS daemon catch.
    pub(crate) async fn run(&self, custom_instructions: Option<String>) -> DaemonResponse {
        let Some(hosted) = self.session.get() else {
            return response_failure(None, "compact", "Session is still initializing", None);
        };
        let main = match hosted.main() {
            Ok(main) => main,
            Err(error) => return response_failure(None, "compact", &error.to_string(), None),
        };
        // TS `compact()` aborts the agent first: the compaction summarizes a
        // settled transcript.
        let busy = self.core.lock().unwrap().is_busy();
        if busy {
            if let Err(error) = main.abort(ConversationAbortOptions::default(), cx()).await {
                return response_failure(None, "compact", &error.to_string(), None);
            }
        }
        let outcome = run_manual_compaction(
            hosted.harness(),
            hosted.deps(),
            &main,
            custom_instructions.clone(),
            cx(),
        )
        .await;
        match outcome {
            Ok(result) => response_success(None, "compact", Some(result)),
            Err(ManualCompactionError::Skipped(message)) => {
                // A skip starts no task, so the bridge sees nothing: the TS
                // run still announced its start and the warning end.
                let instructions = custom_instructions.as_deref();
                emit_worker_event_with(
                    &self.core,
                    &self.events,
                    compaction_start_event("manual", instructions),
                );
                emit_worker_event_with(
                    &self.core,
                    &self.events,
                    compaction_end_unsuccessful(
                        "manual",
                        false,
                        Some(message),
                        Some("warning"),
                        instructions,
                    ),
                );
                response_failure(None, "compact", message, None)
            }
            Err(ManualCompactionError::Aborted) => {
                response_failure(None, "compact", durable::COMPACTION_CANCELLED, None)
            }
            Err(ManualCompactionError::Failed(error)) => {
                response_failure(None, "compact", &error, None)
            }
        }
    }

    /// `abort_compaction` (TS `abortCompaction`): abort every live
    /// compaction of the shown conversation (the manual run and the
    /// automatic threshold/overflow runs alike). Succeeds whether or not a
    /// run is in flight; the TS handler always replies success.
    pub(crate) async fn abort(&self) -> DaemonResponse {
        let Some(hosted) = self.session.get() else {
            return response_success(None, "abort_compaction", None);
        };
        let aborted = async {
            let main = hosted.main()?;
            abort_compactions(hosted.harness(), &main, cx()).await
        }
        .await;
        match aborted {
            Ok(_) => response_success(None, "abort_compaction", None),
            Err(error) => response_failure(None, "abort_compaction", &error.to_string(), None),
        }
    }
}

impl Worker {
    /// `compact { customInstructions? }`.
    pub(crate) async fn handle_compaction(&self, payload: &Value) -> DaemonResponse {
        if let Err(response) = self.require_created("compact") {
            return response;
        }
        let custom_instructions = payload
            .get("customInstructions")
            .and_then(Value::as_str)
            .map(str::to_string);
        self.compaction.run(custom_instructions).await
    }

    /// `abort_compaction`.
    pub(crate) async fn handle_abort_compaction(&self) -> DaemonResponse {
        self.compaction.abort().await
    }
}

/// The `compaction_start` event payload (TS `AgentSessionEvent`). Shared by
/// every compaction surface: the `compact` RPC, the `/compact` session
/// command, and the automatic threshold compaction all emit the same shape
/// with their own `reason` (`manual` / `threshold`; TS
/// `CompactionOutcomeReason`).
pub(crate) fn compaction_start_event(reason: &str, custom_instructions: Option<&str>) -> Value {
    let mut event = json!({ "type": "compaction_start", "reason": reason });
    if let Some(custom_instructions) = custom_instructions {
        event["customInstructions"] = json!(custom_instructions);
    }
    event
}

/// The client-facing `CompactionResult` of a successful compaction (TS
/// `_performCompaction`'s return, the `data` of the `compact` response and
/// the `result` of the settled `compaction_end` event): summary,
/// firstKeptEntryId, tokensBefore, and the durable entry's file-op
/// `details` verbatim. `usage` never rides the wire result (TS keeps it on
/// the persisted entry), and a run whose entry carries no `details` drops
/// the key exactly like TS's `undefined` under JSON serialization.
pub(crate) fn compaction_result_value(
    result: &eukhe_core::session_engine::compaction_exec::CompactionResult,
    entry: &eukhe_types::session::CompactionEntry,
) -> Value {
    let mut value = json!({
        "summary": result.summary,
        "firstKeptEntryId": result.first_kept_entry_id,
        "tokensBefore": result.tokens_before,
    });
    if let Some(details) = &entry.details {
        value["details"] = details.clone();
    }
    value
}

/// The `compaction_end` event payload of a successful compaction (TS
/// `AgentSessionEvent`): the client-facing `CompactionResult` plus whether
/// the session retries the failed turn on the compacted context (the
/// overflow compact-and-retry arm is the only `willRetry: true` source).
/// `reason` is the TS `CompactionOutcomeReason` (`manual` for user-initiated
/// runs, `requested` for model-requested boundary compactions).
pub(crate) fn compaction_end_success(
    reason: &str,
    result: &Value,
    will_retry: bool,
    custom_instructions: Option<&str>,
) -> Value {
    let mut event = json!({
        "type": "compaction_end",
        "reason": reason,
        "result": result,
        "aborted": false,
        "willRetry": will_retry,
    });
    if let Some(custom_instructions) = custom_instructions {
        event["customInstructions"] = json!(custom_instructions);
    }
    event
}

/// The `compaction_end` event payload of an unsuccessful compaction (TS
/// `_endCompactionUnsuccessfully`'s event shape): `aborted` marks a
/// cancelled run; a skip or failure carries its `errorMessage` with the
/// matching `errorSeverity`.
pub(crate) fn compaction_end_unsuccessful(
    reason: &str,
    aborted: bool,
    error_message: Option<&str>,
    error_severity: Option<&str>,
    custom_instructions: Option<&str>,
) -> Value {
    let mut event = json!({
        "type": "compaction_end",
        "reason": reason,
        "aborted": aborted,
        "willRetry": false,
    });
    if let Some(error_message) = error_message {
        event["errorMessage"] = json!(error_message);
    }
    if let Some(error_severity) = error_severity {
        event["errorSeverity"] = json!(error_severity);
    }
    if let Some(custom_instructions) = custom_instructions {
        event["customInstructions"] = json!(custom_instructions);
    }
    event
}

pub(crate) mod durable;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::durable_test_support::{answer, ask, hosted, kinds, Fixture};

    #[test]
    fn compaction_result_value_mirrors_the_ts_datakeys() {
        let result = eukhe_core::session_engine::compaction_exec::CompactionResult {
            summary: "the story so far".to_string(),
            first_kept_entry_id: "abcd1234".to_string(),
            tokens_before: 1234,
            usage: Some(eukhe_types::ai::Usage::default()),
        };
        let entry = eukhe_types::session::CompactionEntry {
            summary: result.summary.clone(),
            first_kept_entry_id: result.first_kept_entry_id.clone(),
            tokens_before: result.tokens_before,
            details: Some(json!({ "readFiles": ["a.rs"], "modifiedFiles": ["b.rs"] })),
            from_hook: Some(false),
            custom_instructions: None,
            usage: result.usage,
            harness_digest: None,
            harness_state_fingerprint: None,
        };
        // The TS `compact` response dataKeys (the live golden,
        // `tests/goldens/compaction-live-ts.json`): summary,
        // firstKeptEntryId, tokensBefore, details — with the entry's
        // `details` verbatim and the summarizer usage never on the wire.
        assert_eq!(
            compaction_result_value(&result, &entry),
            json!({
                "summary": "the story so far",
                "firstKeptEntryId": "abcd1234",
                "tokensBefore": 1234,
                "details": { "readFiles": ["a.rs"], "modifiedFiles": ["b.rs"] },
            })
        );
        // Byte order: the TS `compact` response dataKeys are summary,
        // firstKeptEntryId, tokensBefore, details (the JSON map preserves
        // insertion order), and the `details` block keeps the TS
        // readFiles-first literal order.
        assert_eq!(
            serde_json::to_string(&compaction_result_value(&result, &entry)).unwrap(),
            "{\"summary\":\"the story so far\",\"firstKeptEntryId\":\"abcd1234\",\"tokensBefore\":1234,\"details\":{\"readFiles\":[\"a.rs\"],\"modifiedFiles\":[\"b.rs\"]}}"
        );
        // A run whose entry carries no details drops the key, like TS's
        // `undefined` under JSON serialization.
        let bare = eukhe_types::session::CompactionEntry {
            details: None,
            ..entry
        };
        assert_eq!(
            compaction_result_value(&result, &bare),
            json!({
                "summary": "the story so far",
                "firstKeptEntryId": "abcd1234",
                "tokensBefore": 1234,
            })
        );
    }

    #[test]
    fn event_shapes_match_ts() {
        assert_eq!(
            compaction_start_event("manual", Some("focus on the goal")),
            json!({
                "type": "compaction_start",
                "reason": "manual",
                "customInstructions": "focus on the goal",
            })
        );
        assert_eq!(
            compaction_start_event("manual", None),
            json!({ "type": "compaction_start", "reason": "manual" })
        );
        assert_eq!(
            compaction_end_success(
                "manual",
                &json!({ "summary": "the story so far", "tokensBefore": 1234 }),
                false,
                Some("focus"),
            ),
            json!({
                "type": "compaction_end",
                "reason": "manual",
                "result": { "summary": "the story so far", "tokensBefore": 1234 },
                "aborted": false,
                "willRetry": false,
                "customInstructions": "focus",
            })
        );
        assert_eq!(
            compaction_end_unsuccessful(
                "manual",
                false,
                Some(durable::TOO_SHORT_TO_COMPACT),
                Some("warning"),
                None,
            ),
            json!({
                "type": "compaction_end",
                "reason": "manual",
                "aborted": false,
                "willRetry": false,
                "errorMessage": "Session is too short to compact -- try again once it grows",
                "errorSeverity": "warning",
            })
        );
        assert_eq!(
            compaction_end_unsuccessful("manual", true, None, Some("error"), None),
            json!({
                "type": "compaction_end",
                "reason": "manual",
                "aborted": true,
                "willRetry": false,
                "errorSeverity": "error",
            })
        );
    }

    fn manager(slot: &SessionSlot) -> (CompactionManager, Arc<EventPump>) {
        let pump = Arc::new(EventPump::new());
        let core = Arc::new(Mutex::new(SessionCore::test_core("/tmp".to_string())));
        (
            CompactionManager::new(slot.clone(), Arc::clone(&pump), core),
            pump,
        )
    }

    fn session_events(
        receiver: &mut tokio::sync::broadcast::Receiver<Arc<crate::worker::OutboundFrame>>,
    ) -> Vec<Value> {
        let mut events = Vec::new();
        while let Ok(frame) = receiver.try_recv() {
            let payload: Value = serde_json::from_slice(&frame.payload).expect("frame json");
            events.push(payload["event"].clone());
        }
        events
    }

    /// A session with nothing before the keep window answers the TS skip
    /// message and announces the start/warning-end pair itself (no task
    /// ran, so the bridge has nothing to translate).
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_skipped_compaction_fails_with_its_frame_pair() {
        let fixture = Fixture::new();
        let slot = SessionSlot::default();
        slot.replace(hosted(&fixture).await);
        let (manager, pump) = manager(&slot);
        let mut receiver = pump.subscribe();

        let response = manager.run(Some("focus".to_string())).await;
        assert!(!response.success);
        assert_eq!(
            response.error.as_deref(),
            Some(durable::TOO_SHORT_TO_COMPACT)
        );
        assert_eq!(
            session_events(&mut receiver),
            [
                json!({ "type": "compaction_start", "reason": "manual", "customInstructions": "focus" }),
                json!({
                    "type": "compaction_end", "reason": "manual", "aborted": false,
                    "willRetry": false, "errorMessage": durable::TOO_SHORT_TO_COMPACT,
                    "errorSeverity": "warning", "customInstructions": "focus",
                }),
            ]
        );
        close(&slot).await;
    }

    /// A compaction over a long enough transcript answers the TS
    /// `CompactionResult` and places the summary entry.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn compact_answers_the_compaction_result() {
        let fixture = Fixture::new();
        fixture.settings(&json!({ "compaction": { "keepRecentTokens": 1 } }));
        let slot = SessionSlot::default();
        let session = hosted(&fixture).await;
        slot.replace(Arc::clone(&session));
        let main = session.main().expect("main");
        ask(&fixture, &main, "first", "one").await;
        ask(&fixture, &main, "second", "two").await;
        fixture.faux.append_responses(vec![answer("SUMMARY")]);
        let (manager, _pump) = manager(&slot);

        let response = manager.run(None).await;
        assert!(response.success, "{response:?}");
        let data = response.data.expect("result");
        assert_eq!(data["summary"], json!("SUMMARY"));
        assert!(data["tokensBefore"]
            .as_u64()
            .is_some_and(|tokens| tokens > 0));
        assert!(kinds(&main)
            .await
            .iter()
            .any(|kind| kind == "pi.compaction"));
        close(&slot).await;
    }

    /// `abort_compaction` always succeeds: with no live run, and before the
    /// session exists.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn abort_without_a_live_compaction_succeeds() {
        let slot = SessionSlot::default();
        let (manager, _pump) = manager(&slot);
        assert!(manager.abort().await.success);

        let fixture = Fixture::new();
        slot.replace(hosted(&fixture).await);
        assert!(manager.abort().await.success);
        close(&slot).await;
    }

    async fn close(slot: &SessionSlot) {
        if let Some(session) = slot.take() {
            session.close(cx()).await.expect("close");
        }
    }
}
