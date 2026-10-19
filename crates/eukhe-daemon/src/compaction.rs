//! The worker's compaction commands.
//!
//! Port of the TS daemon-mode compaction surface: the `compact` /
//! `abort_compaction` handlers over the durable session ([`durable`]), and
//! the unsuccessful `compaction_end` event they and the event bridge share.

use std::sync::{Arc, Mutex};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::types::ConversationAbortOptions;
use eukhe_types::daemon::{CompactionReason, CompactionResult, ErrorSeverity, SessionEvent};
use serde_json::Value;

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::durable_host::translator::ManualSettle;
use crate::worker::{emit_worker_event_with, EventPump, SessionCore, SessionSlot, Worker};
use durable::{abort_compactions, run_manual_compaction, ManualCompactionError};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// The worker's `compact` / `abort_compaction` commands over the hosted
/// durable session. The `compaction_start` frame of a run comes from the
/// event bridge (the task's `pi.live` status) carrying the command's
/// instructions; its `compaction_end` is this command's (the TS
/// `CompactionResult` the response carries, or the abort), and a skip,
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
        match self.compact(custom_instructions).await {
            Ok(result) => match serde_json::to_value(result) {
                Ok(result) => response_success(None, "compact", Some(result)),
                Err(error) => response_failure(None, "compact", &error.to_string(), None),
            },
            Err(error) => response_failure(None, "compact", &error.to_string(), None),
        }
    }

    /// One manual compaction with its `compaction_start`/`compaction_end`
    /// frame pair, settled: the `compact` command and the `/compact`
    /// session command share it. A compaction that compacted continues an
    /// active goal (the abort ended its in-run loop).
    pub(crate) async fn compact(
        &self,
        custom_instructions: Option<String>,
    ) -> Result<CompactionResult, ManualCompactionError> {
        let Some(hosted) = self.session.get() else {
            return Err(ManualCompactionError::Failed(
                "Session is still initializing".to_string(),
            ));
        };
        let main = hosted
            .main()
            .map_err(|error| ManualCompactionError::Failed(error.to_string()))?;
        // TS `compact()` aborts the agent first: the compaction summarizes a
        // settled transcript.
        let busy = self.core.lock().unwrap().is_busy();
        if busy {
            main.abort(ConversationAbortOptions::default(), cx())
                .await
                .map_err(|error| ManualCompactionError::Failed(error.to_string()))?;
        }
        // The claim ties the run's task frames to this command.
        if let Some(view) = self.core.lock().unwrap().view.as_mut() {
            view.translator
                .claim_manual_compaction(custom_instructions.clone());
        }
        let outcome = run_manual_compaction(
            hosted.harness(),
            hosted.deps(),
            &main,
            custom_instructions.clone(),
            cx(),
        )
        .await;
        match &outcome {
            Ok(result) => {
                self.settle(
                    SessionEvent::CompactionEnd {
                        reason: CompactionReason::Manual,
                        result: Some(result.clone()),
                        aborted: false,
                        will_retry: false,
                        error_message: None,
                        error_severity: None,
                        custom_instructions: custom_instructions.clone(),
                    },
                    true,
                );
                // The abort before the compaction ended an active goal's
                // in-run loop: a compaction that compacted continues it.
                if let Err(error) = eukhe_core::durable::goals::continue_goal_after_compaction(
                    hosted.harness(),
                    main.id(),
                    cx(),
                )
                .await
                {
                    eprintln!(
                        "eukhe-daemon: the post-compaction goal continuation failed: {error}"
                    );
                }
            }
            Err(ManualCompactionError::Skipped(message)) => {
                let end = compaction_end_unsuccessful(
                    CompactionReason::Manual,
                    false,
                    Some((*message).to_owned()),
                    Some(ErrorSeverity::Warning),
                    custom_instructions.clone(),
                );
                // A skip before the task starts reaches the bridge as
                // nothing: the TS run still announced its start and the
                // warning end.
                if !self.settle(end.clone(), false) {
                    emit_worker_event_with(
                        &self.core,
                        &self.events,
                        SessionEvent::CompactionStart {
                            reason: CompactionReason::Manual,
                            custom_instructions,
                        },
                    );
                    emit_worker_event_with(&self.core, &self.events, end);
                }
            }
            Err(ManualCompactionError::Aborted) => {
                self.settle(
                    compaction_end_unsuccessful(
                        CompactionReason::Manual,
                        true,
                        None,
                        Some(ErrorSeverity::Error),
                        custom_instructions,
                    ),
                    true,
                );
            }
            Err(ManualCompactionError::Failed(error)) => {
                self.settle(
                    compaction_end_unsuccessful(
                        CompactionReason::Manual,
                        false,
                        Some(error.clone()),
                        Some(ErrorSeverity::Error),
                        custom_instructions,
                    ),
                    false,
                );
            }
        }
        outcome
    }

    /// Settle this command's claim with its `compaction_end` frame,
    /// emitting it now when the claimed task already ended (else the
    /// task's end emits it). `false` when no task started: nothing of the
    /// run reached the wire.
    fn settle(&self, end: SessionEvent, task_started: bool) -> bool {
        let settled = match self.core.lock().unwrap().view.as_mut() {
            Some(view) => view.translator.settle_manual_compaction(end, task_started),
            None => ManualSettle::NoTask,
        };
        match settled {
            ManualSettle::Emit(frame) => {
                emit_worker_event_with(&self.core, &self.events, *frame);
                true
            }
            ManualSettle::Deferred => true,
            ManualSettle::NoTask => false,
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
        // A compaction is work a stop interrupts: it holds the run gate
        // until it ends.
        let _admission = crate::worker::RunAdmission::enter(&self.core).await;
        self.compaction.run(custom_instructions).await
    }

    /// `abort_compaction`.
    pub(crate) async fn handle_abort_compaction(&self) -> DaemonResponse {
        self.compaction.abort().await
    }
}

/// The `compaction_end` event of an unsuccessful compaction (TS
/// `_endCompactionUnsuccessfully`'s event shape): `aborted` marks a
/// cancelled run; a skip or failure carries its `error_message` with the
/// matching `error_severity`.
pub(crate) fn compaction_end_unsuccessful(
    reason: CompactionReason,
    aborted: bool,
    error_message: Option<String>,
    error_severity: Option<ErrorSeverity>,
    custom_instructions: Option<String>,
) -> SessionEvent {
    SessionEvent::CompactionEnd {
        reason,
        result: None,
        aborted,
        will_retry: false,
        error_message,
        error_severity,
        custom_instructions,
    }
}

pub(crate) mod durable;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::durable_test_support::{answer, ask, hosted, kinds, Fixture};
    use serde_json::json;

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
