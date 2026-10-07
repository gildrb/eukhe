//! Session lifecycle on the worker: the graceful shutdown, the scheduled
//! jobs binding, and the wait-for-idle arms.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use serde_json::Value;

use super::{response_failure, response_success, DaemonResponse, Worker};

impl Worker {
    /// Graceful stop: abort the run, close the session (the Harness
    /// flushes, the lease releases), and release the pane. The resume entry
    /// stays: a later create resumes the session where it stopped. The
    /// connection loop exits the process after replying.
    pub(crate) async fn handle_shutdown(&self) -> DaemonResponse {
        // The admission gate closes first: a racing command must see the
        // stop before the close starts.
        self.core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .shutdown_requested = true;
        self.side_questions
            .abort_all_and_settle(super::SIDE_QUESTION_SETTLE_TIMEOUT)
            .await;
        self.user_bash.abort().await;
        self.close_hosted_session().await;
        let reporter = self
            .herdr
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        reporter.release().await;
        response_success(None, "shutdown", None)
    }

    /// Bind the live session's schedule catalog (TS `rebindCronJobsToState`):
    /// the artifact partition, the job rebind, the scheduler start. Runs at
    /// create and after every session replacement.
    pub(crate) async fn bind_scheduled_jobs(&self) {
        let binding = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            crate::scheduled_jobs::live_binding(&core)
        };
        if let Some((binding, artifact_dir)) = binding {
            self.scheduled.bind_session(binding, artifact_dir).await;
        }
    }

    /// Wait until the main conversation is idle (no live run, nothing
    /// queued) and every event batch reached the wire. `waitForRlmQuiescence`
    /// is covered: RLM children are conversation-owned tasks, so the idle
    /// scope waits for them too.
    async fn wait_until_idle(&self) -> Result<(), String> {
        let hosted = self.session.get().ok_or("Session is still initializing")?;
        let main = hosted.main().map_err(|error| error.to_string())?;
        main.wait_for_idle(&BACKGROUND_CONTEXT)
            .await
            .map_err(|error| error.to_string())?;
        hosted.events_delivered().await;
        Ok(())
    }

    /// `wait_for_idle`: park until the session is idle.
    pub(crate) async fn handle_wait_for_idle(&self, _payload: &Value) -> DaemonResponse {
        match self.wait_until_idle().await {
            Ok(()) => response_success(None, "wait_for_idle", None),
            Err(error) => response_failure(None, "wait_for_idle", &error, None),
        }
    }

    /// `wait_for_headless_completion`: settle the headless run first (the
    /// same idle wait), then answer the autonomous-run accounting snapshot
    /// of the main conversation.
    pub(crate) async fn handle_wait_for_headless_completion(
        &self,
        _payload: &Value,
    ) -> DaemonResponse {
        const COMMAND: &str = "wait_for_headless_completion";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        if let Err(error) = self.wait_until_idle().await {
            return response_failure(None, COMMAND, &error, None);
        }
        let main = match hosted.main() {
            Ok(main) => main,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        match eukhe_core::durable::goals::autonomous_state(
            hosted.harness(),
            main.id(),
            &BACKGROUND_CONTEXT,
        )
        .await
        {
            Ok(state) => response_success(
                None,
                COMMAND,
                Some(serde_json::to_value(state.status()).unwrap_or(Value::Null)),
            ),
            Err(error) => response_failure(None, COMMAND, &error.to_string(), None),
        }
    }
}

/// TS `activeLifecycleForSession`: a resident subagent is visible before
/// its first message; a message-less top-level session is a draft; a busy
/// run is live even before its first message lands.
pub(super) fn active_lifecycle(runtime_kind: &str, messageless: bool, busy: bool) -> &'static str {
    if runtime_kind == "subagent" || !messageless || busy {
        "live"
    } else {
        "draft"
    }
}
