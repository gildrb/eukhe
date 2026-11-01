//! Session lifecycle on the worker: the graceful shutdown, the scheduled
//! jobs binding, and the wait-for-idle arms.

use eukhe_bend::rules::headless::{settle, Settle, SettleFacts};
use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::children::unsettled_child_tasks;
use eukhe_core::durable::pending::pending_work;
use eukhe_core::durable::rlm::kernel_background_jobs_settled;
use eukhe_core::durable::workflow::unsettled_run_tasks;
use futures::FutureExt;
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
        self.user_bash.abort();
        self.close_hosted_session().await;
        let reporter = self
            .herdr
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        reporter.release().await;
        response_success(None, "shutdown", None)
    }

    /// `worker_handover`: a supervisor of another build takes the session
    /// to its own build. The admission closes first, then the work is
    /// recorded resumable through the handover exit (no abort, no close:
    /// the next worker resumes the run from the storage). The connection
    /// loop exits the process after replying.
    pub(crate) async fn handle_handover(&self) -> DaemonResponse {
        self.core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .shutdown_requested = true;
        crate::supervisor_lost::hand_over(self, crate::supervisor_lost::HandoverCause::Replaced)
            .await;
        response_success(None, "worker_handover", None)
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
    /// left unsettled. A background workflow run (`eukhe.workflow.run`)
    /// counts the same: the barrier waits for its task and the turn its
    /// report starts. With `waitForBackgroundJobs` too (a parent's child
    /// settle watch, an ACP prompt's settle) it also holds while the work
    /// a turn's end leaves running runs ([`pending_work`]: the session's
    /// jobs and the kernel's background jobs) and while a settled job's
    /// notice is being admitted: each wakes the session into another run,
    /// so the session is not quiescent before they end.
    async fn wait_until_idle(&self, payload: &Value) -> Result<(), String> {
        let cx = &BACKGROUND_CONTEXT;
        let flag = |name: &str| payload.get(name).and_then(Value::as_bool).unwrap_or(false);
        let rlm_quiescence = flag("waitForRlmQuiescence");
        let background_jobs = flag("waitForBackgroundJobs");
        let hosted = self.session.get().ok_or("Session is still initializing")?;
        let main = hosted.main().map_err(|error| error.to_string())?;
        // The hosted session's notice seam: wired with its config, so a
        // hosted session always has one.
        let notices = self
            .job_notices
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone()
            .ok_or("Session is still initializing")?;
        loop {
            main.wait_for_idle(cx)
                .await
                .map_err(|error| error.to_string())?;
            if !rlm_quiescence {
                break;
            }
            let mut unsettled = unsettled_child_tasks(hosted.harness(), main.id(), cx)
                .await
                .map_err(|error| error.to_string())?;
            unsettled.extend(
                unsettled_run_tasks(hosted.harness(), main.id(), cx)
                    .await
                    .map_err(|error| error.to_string())?,
            );
            if !unsettled.is_empty() {
                for task in unsettled {
                    hosted
                        .harness()
                        .wait_for_task(task, cx)
                        .await
                        .map_err(|error| error.to_string())?;
                }
                continue;
            }
            if !background_jobs {
                break;
            }
            // The read order that never misses a wake: the running work,
            // then the notices in flight, then the conversation's
            // idleness. A job reads ended only after its notice entered
            // the in-flight count, and an admitted notice holds the
            // conversation busy. The compiled core's quiescence rule (the
            // one every frontend holds by) decides; this barrier states no
            // wait limit. A result held for a watching wait needs no hold
            // of its own: the wait runs inside a turn, and a wait that ends
            // without taking it hands it to a notice.
            let pending = pending_work(hosted.deps(), hosted.harness(), main.id(), cx)
                .await
                .map_err(|error| error.to_string())?;
            let changed = notices.changed();
            tokio::pin!(changed);
            changed.as_mut().enable();
            let wakes = notices.in_flight();
            let busy = main
                .wait_for_idle(cx)
                .now_or_never()
                .transpose()
                .map_err(|error| error.to_string())?
                .is_none();
            let count = |count: usize| u64::try_from(count).unwrap_or(u64::MAX);
            let facts = SettleFacts {
                busy,
                jobs: count(pending.jobs.len()),
                kernel_jobs: count(pending.kernel_jobs),
                children: count(pending.children),
                workflow_runs: count(pending.workflow_runs),
                wakes: count(wakes),
                unknown: false,
                limit_hit: false,
            };
            match settle(&facts).map_err(|error| error.to_string())? {
                // With no limit stated the rule never gives up; a give-up
                // would end the hold like a finish.
                Settle::Done | Settle::GiveUp => break,
                Settle::Wait => {}
            }
            // Wait for the first pending work to move, then check again;
            // a busy conversation, a child or a workflow run is waited on
            // at the loop's top.
            if let Some(first) = pending.jobs.first() {
                if let Some(job) = hosted.deps().jobs.get(first.id.as_str()) {
                    job.ended().await;
                }
            } else if pending.kernel_jobs > 0 {
                // The last job's completion notice is admitted before the
                // settle fires, so the next idle wait holds for its turn.
                kernel_background_jobs_settled(hosted.deps(), main.id()).await;
            } else if wakes > 0 {
                changed.await;
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
