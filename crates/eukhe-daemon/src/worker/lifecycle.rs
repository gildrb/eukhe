//! Session lifecycle on the worker: the graceful shutdown, the scheduled
//! jobs binding, and the wait-for-idle arms.

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::children::unsettled_child_tasks;
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
    ///
    /// # Errors
    ///
    /// Returns the bind failure: the artifact directory or the durable job
    /// rebind could not be written.
    pub(crate) async fn bind_scheduled_jobs(&self) -> anyhow::Result<()> {
        let binding = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            crate::scheduled_jobs::live_binding(&core)
        };
        if let Some((binding, artifact_dir)) = binding {
            self.scheduled.bind_session(binding, artifact_dir).await?;
        }
        Ok(())
    }

    /// Wait until the main conversation is idle (no live run, nothing
    /// queued) and every event batch reached the wire. With
    /// `waitForRlmQuiescence` (TS `waitForRlmQuiescence`) the barrier also
    /// owns descendant work: the `eukhe.rlm.child` tasks are background
    /// tasks the idle scope does not reach, so it waits for every
    /// unsettled child task to end, then for the idle the report it
    /// submitted (the terminal notice turn) leads to, until no child is
    /// left unsettled.
    async fn wait_until_idle(&self, payload: &Value) -> Result<(), String> {
        let cx = &BACKGROUND_CONTEXT;
        let rlm_quiescence = payload
            .get("waitForRlmQuiescence")
            .and_then(Value::as_bool)
            .unwrap_or(false);
        let hosted = self.session.get().ok_or("Session is still initializing")?;
        let main = hosted.main().map_err(|error| error.to_string())?;
        loop {
            main.wait_for_idle(cx)
                .await
                .map_err(|error| error.to_string())?;
            if !rlm_quiescence {
                break;
            }
            let unsettled = unsettled_child_tasks(hosted.harness(), main.id(), cx)
                .await
                .map_err(|error| error.to_string())?;
            if unsettled.is_empty() {
                break;
            }
            for task in unsettled {
                hosted
                    .harness()
                    .wait_for_task(task, cx)
                    .await
                    .map_err(|error| error.to_string())?;
            }
        }
        hosted.events_delivered().await;
        Ok(())
    }

    /// `wait_for_idle`: park until the session is idle.
    pub(crate) async fn handle_wait_for_idle(&self, payload: &Value) -> DaemonResponse {
        match self.wait_until_idle(payload).await {
            Ok(()) => response_success(None, "wait_for_idle", None),
            Err(error) => response_failure(None, "wait_for_idle", &error, None),
        }
    }

    /// `wait_for_headless_completion`: settle the headless run first (the
    /// same idle wait), then answer the autonomous-run accounting snapshot
    /// of the main conversation.
    pub(crate) async fn handle_wait_for_headless_completion(
        &self,
        payload: &Value,
    ) -> DaemonResponse {
        const COMMAND: &str = "wait_for_headless_completion";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        if let Err(error) = self.wait_until_idle(payload).await {
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
