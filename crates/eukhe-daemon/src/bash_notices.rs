//! The detached kernel bash completion notice: the port of the TS
//! async-bash-completion wake (agent-session.ts `_createKernelHostHandlers`'
//! `bash.completed`/`bash.consumed` arms + rlm-runtime.ts's validated host
//! handlers + messages.ts `createAsyncBashCompletionMessage`).
//!
//! The kernel runtime (`eukhe-runtime`'s `bash.py`) starts a notice
//! task for every background `bash()` whose creating cell ends before the
//! command settles: when the process finishes (still detached, its result
//! unconsumed), the kernel sends a `bash.completed` host request. The TS
//! session answers it by injecting the `[bash-done pid:N exit:M]` custom
//! row with `queueIfBusy` + `resumeIfIdle` — a busy session queues the
//! notice as a steering row, an idle session wakes into a new turn that
//! runs on the row. A later kernel read that reaches the model first
//! sends `bash.consumed`, and the undelivered notice withdraws.
//!
//! The durable mapping ([`BashNotices`]): the handlers ride the session's
//! extra kernel host handlers (wired by [`Worker::wire_session_host`]). A
//! completion is admitted on the main conversation like the agent-message
//! delivery — the `async_bash_completion` row as an `eukhe.custom` write,
//! then the `[bash-done ...]` input on the steer lane, under the request id
//! `bash-done:<uuid>` (`:row` for the card) — so a busy session queues it
//! for the next boundary and an idle one wakes into the turn; the Harness
//! inbox makes the admission durable. A `bash.consumed` withdraws the
//! front-most still-queued notice for the same pid and command.
//!
//! The old engine's seam (`AgentSessionEngine` sinks) stays compiled until
//! the engine is removed.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::{SessionConfig, SessionStorage};
use eukhe_durable::harness::types::WhenBusy;
use serde_json::Value;

use eukhe_core::kernel::shared::{host_handler, HostRequestHandlers};

use crate::agent_engine::AgentSessionEngine;
use crate::agent_message_ingest::{withdraw_queued, WithdrawnLane};
use crate::engine::{BashCompletionNotice, BashConsumedNotice};
use crate::worker::{submit_input, InputRequest, SessionCore, SessionSlot, Worker};

impl AgentSessionEngine {
    /// Wire the worker's bash-completion queue seams. The worker calls
    /// this once at construction, before the first prompt's session
    /// build reads them in [`AgentSessionEngine::extra_host_handlers`].
    ///
    /// # Panics
    ///
    /// Panics when a sink mutex is poisoned (a holder panicked while
    /// holding the completion or consumed-sink lock).
    pub fn set_bash_notice_sinks(
        &self,
        completion: crate::engine::BashCompletionSink,
        consumed: crate::engine::BashConsumedSink,
    ) {
        *self
            .bash_completion_sink
            .lock()
            .expect("bash completion sink lock") = Some(completion);
        *self
            .bash_consumed_sink
            .lock()
            .expect("bash consumed sink lock") = Some(consumed);
    }

    /// The `bash.completed`/`bash.consumed` kernel host handlers (TS
    /// `createAsyncBashCompletionHostHandler` /
    /// `createAsyncBashConsumedHostHandler`): validated details, the
    /// notice admitted (or withdrawn) through the worker's queue
    /// seams. Registered only when both seams are wired — the daemon
    /// worker wires them at construction; anything without a worker
    /// queue leaves the requests honestly unavailable.
    pub(crate) fn register_bash_notice_host_handlers(&self, handlers: &mut HostRequestHandlers) {
        let Some(completion) = self
            .bash_completion_sink
            .lock()
            .expect("bash completion sink lock")
            .clone()
        else {
            return;
        };
        let Some(consumed) = self
            .bash_consumed_sink
            .lock()
            .expect("bash consumed sink lock")
            .clone()
        else {
            return;
        };
        handlers.register(
            "bash.completed",
            host_handler(move |payload| {
                let completion = completion.clone();
                Box::pin(async move {
                    let notice = validate_completion(&payload.data)?;
                    // The closed-session gate lives in the sink: the
                    // worker's kill/shutdown set the marker and parked the
                    // runner, and the sink (which holds the engine) refuses
                    // the injection exactly like TS `_disposed` /
                    // `session_closed` refuse it.
                    completion(notice);
                    Ok(serde_json::json!({}))
                })
            }),
        );
        handlers.register(
            "bash.consumed",
            host_handler(move |payload| {
                let consumed = consumed.clone();
                Box::pin(async move {
                    let notice = validate_consumed(&payload.data)?;
                    consumed(notice);
                    Ok(serde_json::json!({}))
                })
            }),
        );
    }
}

/// One admitted notice a later `bash.consumed` may still withdraw.
struct PendingNotice {
    request_id: String,
    pid: u32,
    command: String,
}

/// The `bash.completed`/`bash.consumed` seam of one durable session: the
/// worker's session slot it admits into, the closed-session gate, and the
/// notices admitted so far (process memory: the kernel that sends the
/// withdrawals dies with the worker).
#[derive(Clone)]
pub(crate) struct BashNotices {
    session: SessionSlot,
    core: Arc<Mutex<SessionCore>>,
    pending: Arc<Mutex<Vec<PendingNotice>>>,
}

impl BashNotices {
    pub(crate) fn new(session: SessionSlot, core: Arc<Mutex<SessionCore>>) -> Self {
        Self {
            session,
            core,
            pending: Arc::default(),
        }
    }

    fn pending(&self) -> std::sync::MutexGuard<'_, Vec<PendingNotice>> {
        self.pending.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Register the validated `bash.completed`/`bash.consumed` handlers
    /// (TS `createAsyncBashCompletionHostHandler` /
    /// `createAsyncBashConsumedHostHandler`).
    pub(crate) fn register(&self, handlers: &mut HostRequestHandlers) {
        let completion = self.clone();
        handlers.register(
            "bash.completed",
            host_handler(move |payload| {
                let notices = completion.clone();
                async move {
                    let notice = validate_completion(&payload.data)?;
                    notices.deliver(notice).await?;
                    Ok(serde_json::json!({}))
                }
            }),
        );
        let consumed = self.clone();
        handlers.register(
            "bash.consumed",
            host_handler(move |payload| {
                let notices = consumed.clone();
                async move {
                    let notice = validate_consumed(&payload.data)?;
                    notices.withdraw(&notice).await?;
                    Ok(serde_json::json!({}))
                }
            }),
        );
    }

    /// Admit one completion notice (TS `bash.completed` ->
    /// `_promptInjectedMessage(message, { streamingBehavior: "steer",
    /// queueIfBusy: true, resumeIfIdle: true })`). A closed or closing
    /// session refuses it silently, like TS `_disposed`.
    async fn deliver(&self, notice: BashCompletionNotice) -> anyhow::Result<()> {
        {
            let core = self.core.lock().unwrap_or_else(PoisonError::into_inner);
            if !core.created || core.shutdown_requested {
                return Ok(());
            }
        }
        let Some(hosted) = self.session.get() else {
            return Ok(());
        };
        let row = eukhe_core::session_engine::messages::create_async_bash_completion_message(
            notice.pid,
            &notice.command,
            notice.exit_code,
            crate::util::now_ms(),
        );
        let request_id = format!("bash-done:{}", uuid::Uuid::new_v4());
        let request = InputRequest {
            text: row.content.text(),
            images: Vec::new(),
            custom_row: Some(crate::session_commands::custom_message_value(&row)),
            when_busy: WhenBusy::Steer,
            request_id: Some(request_id.clone()),
        };
        submit_input(&hosted.main()?, &request, &BACKGROUND_CONTEXT).await?;
        self.pending().push(PendingNotice {
            request_id,
            pid: notice.pid,
            command: notice.command,
        });
        Ok(())
    }

    /// Withdraw one queued notice (TS `bash.consumed` ->
    /// `_withdrawAsyncBashCompletionNotice`): the kernel read the finished
    /// command's result before the notice delivered. One read withdraws
    /// one notice — the front-most still-queued one for this pid and
    /// command (pids are reused across handles).
    async fn withdraw(&self, notice: &BashConsumedNotice) -> anyhow::Result<()> {
        let Some(hosted) = self.session.get() else {
            return Ok(());
        };
        let candidates: Vec<String> = self
            .pending()
            .iter()
            .filter(|pending| pending.pid == notice.pid && pending.command == notice.command)
            .map(|pending| pending.request_id.clone())
            .collect();
        for request_id in candidates {
            let row_id = format!("{request_id}:row");
            let withdrawn = withdraw_queued(&hosted, |queued| {
                queued == request_id.as_str() || queued == row_id.as_str()
            })
            .await?;
            // Withdrawn or already placed, the notice is settled either way.
            self.pending()
                .retain(|pending| pending.request_id != request_id);
            if withdrawn
                .iter()
                .any(|item| item.lane != WithdrawnLane::Write)
            {
                break;
            }
        }
        Ok(())
    }
}

impl Worker {
    /// Wire this worker's kernel host seams into a session it opens: the
    /// scheduled-jobs cron wiring (`rlm_heartbeat.*`) and the bash
    /// completion notices (`bash.completed`/`bash.consumed`), merged into
    /// the config's extra host handlers.
    pub(crate) fn wire_session_host(&self, config: &mut SessionConfig) {
        let storage_dir = match &config.storage {
            SessionStorage::Jsonl { dir, .. } => Some(dir.clone()),
            SessionStorage::Memory => None,
        };
        config.cron = Some(self.kernel_cron_wiring(
            &config.session_id,
            storage_dir.as_deref(),
            &config.cwd.to_string_lossy(),
        ));
        let handlers = config
            .extra_host_handlers
            .get_or_insert_with(HostRequestHandlers::default);
        BashNotices::new(self.session.clone(), Arc::clone(&self.core)).register(handlers);
    }
}

/// TS `createAsyncBashCompletionHostHandler` validation: a positive
/// integer pid, a non-empty string command, an integer exit code.
fn validate_completion(data: &Value) -> anyhow::Result<BashCompletionNotice> {
    let consumed = validate_consumed(data)?;
    let exit_code = data
        .get("exitCode")
        .and_then(Value::as_i64)
        .ok_or_else(|| anyhow::anyhow!("bash.completed exitCode must be an integer"))?;
    Ok(BashCompletionNotice {
        pid: consumed.pid,
        command: consumed.command,
        exit_code,
    })
}

/// TS `createAsyncBashConsumedHostHandler` validation: a positive
/// integer pid and a non-empty string command (pids are reused across
/// handles, so the command disambiguates).
fn validate_consumed(data: &Value) -> anyhow::Result<BashConsumedNotice> {
    let pid = data
        .get("pid")
        .and_then(Value::as_u64)
        .filter(|pid| *pid > 0 && u32::try_from(*pid).is_ok())
        .ok_or_else(|| anyhow::anyhow!("bash.completed pid must be a positive integer"))?
        as u32;
    let command = data
        .get("command")
        .and_then(Value::as_str)
        .filter(|command| !command.is_empty())
        .ok_or_else(|| anyhow::anyhow!("bash.completed command must be a non-empty string"))?
        .to_string();
    Ok(BashConsumedNotice { pid, command })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::durable_test_support::{created_worker, wait_busy, worker_inbox, worker_rows};
    use serde_json::json;

    const SESSION: &str = "notice-session";
    const NOTICE: &str = "[bash-done pid:4321 exit:0]\n\nCommand: \"sleep 1\"";

    fn completion() -> BashCompletionNotice {
        BashCompletionNotice {
            pid: 4321,
            command: "sleep 1".to_owned(),
            exit_code: 0,
        }
    }

    fn consumed() -> BashConsumedNotice {
        BashConsumedNotice {
            pid: 4321,
            command: "sleep 1".to_owned(),
        }
    }

    /// A busy session queues the notice (card + steer prompt); the kernel's
    /// read withdraws exactly one queued notice, and a read for another
    /// command withdraws nothing.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_queued_notice_is_withdrawn_by_its_read() {
        let (_dir, worker) =
            created_worker(SESSION, json!([{ "text": "held", "delayMs": 600_000 }])).await;
        let prompt = worker
            .dispatch(
                "prompt",
                &json!({ "activeSessionId": SESSION, "message": "work" }),
            )
            .await;
        assert!(prompt.success, "{prompt:?}");
        wait_busy(&worker, true).await;
        let notices = BashNotices::new(worker.session.clone(), Arc::clone(&worker.core));
        notices.deliver(completion()).await.expect("first notice");
        notices.deliver(completion()).await.expect("second notice");
        let queued = |count: usize| {
            let mut items = Vec::new();
            for _ in 0..count {
                items.push(("write".to_owned(), String::new()));
                items.push(("steer".to_owned(), NOTICE.to_owned()));
            }
            items
        };
        assert_eq!(worker_inbox(&worker).await, queued(2));

        notices
            .withdraw(&BashConsumedNotice {
                pid: 4321,
                command: "other".to_owned(),
            })
            .await
            .expect("foreign read");
        assert_eq!(worker_inbox(&worker).await, queued(2));
        notices.withdraw(&consumed()).await.expect("read");
        assert_eq!(
            worker_inbox(&worker).await,
            queued(1),
            "one read, one notice"
        );
        let aborted = worker
            .dispatch("abort", &json!({ "activeSessionId": SESSION }))
            .await;
        assert!(aborted.success, "{aborted:?}");
    }

    /// An idle session wakes into the turn that carries the
    /// `async_bash_completion` row.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn an_idle_session_wakes_on_the_notice() {
        let (_dir, worker) = created_worker(SESSION, json!(["woken"])).await;
        let notices = BashNotices::new(worker.session.clone(), Arc::clone(&worker.core));
        notices.deliver(completion()).await.expect("notice");
        let waited = worker
            .dispatch("wait_for_idle", &json!({ "activeSessionId": SESSION }))
            .await;
        assert!(waited.success, "{waited:?}");
        let rows = worker_rows(&worker, "eukhe.custom").await;
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0]["customType"], json!("async_bash_completion"));
        assert_eq!(
            rows[0]["details"],
            json!({ "pid": 4321, "command": "sleep 1", "exitCode": 0 })
        );
        let users = worker_rows(&worker, "pi.user").await;
        assert_eq!(users.len(), 1);
        let answers = worker_rows(&worker, "pi.assistant").await;
        assert_eq!(answers.len(), 1);
    }

    #[test]
    fn completion_validation_matches_the_ts_contract() {
        assert!(validate_completion(&serde_json::json!({
            "pid": 4321,
            "command": "sleep 1",
            "exitCode": 0,
        }))
        .is_ok());
        assert!(validate_completion(&serde_json::json!({
            "pid": 0,
            "command": "sleep 1",
            "exitCode": 0,
        }))
        .is_err());
        assert!(validate_completion(&serde_json::json!({
            "pid": 4321,
            "command": "",
            "exitCode": 0,
        }))
        .is_err());
        assert!(validate_completion(&serde_json::json!({
            "pid": 4321,
            "command": "sleep 1",
            "exitCode": "0",
        }))
        .is_err());
    }
}
