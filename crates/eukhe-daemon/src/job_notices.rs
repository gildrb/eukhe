//! The one job-settled wake (ADR 0010): every job a session started that
//! settles after its call stopped blocking the turn — a background kernel
//! `bash()` command, a detached `ipython` cell — wakes the session through
//! [`JobNotices::deliver`].
//!
//! Bash commands are the port of the TS async-bash-completion wake
//! (agent-session.ts `_createKernelHostHandlers`' `bash.completed`/
//! `bash.consumed` arms + rlm-runtime.ts's validated host handlers +
//! messages.ts `createAsyncBashCompletionMessage`): the kernel runtime
//! (`eukhe-runtime`'s `bash.py`) starts a notice task for every
//! background `bash()` whose creating cell ends before the command
//! settles, and sends a `bash.completed` host request when the process
//! finishes still unconsumed. A later kernel read that reaches the model
//! first sends `bash.consumed`, and the undelivered notice withdraws.
//! Detached cells settle through the session's
//! [`SessionConfig::job_settled`] sink.
//!
//! The durable mapping: a settled job is admitted on the main conversation
//! like the agent-message delivery — its row
//! ([`create_job_settled_message`]) as an `eukhe.custom` write, then its
//! report input on the steer lane, under the request id
//! `job-settled:<uuid>` (`:row` for the card) — so a busy session queues
//! it for the next boundary and an idle one wakes into the turn; the
//! Harness inbox makes the admission durable. A `bash.consumed` withdraws
//! the front-most still-queued notice for the same pid and command.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::messages::create_job_settled_message;
use eukhe_core::durable::{SessionConfig, SessionStorage};
use eukhe_durable::harness::types::WhenBusy;
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::job::JobSettled;
use serde_json::Value;

use eukhe_core::kernel::shared::{host_handler, HostRequestHandlers};

use crate::agent_message_ingest::{withdraw_queued, WithdrawnLane};
use crate::worker::{submit_input, InputRequest, SessionCore, SessionSlot, Worker};

/// The kernel read a finished command's result before its notice
/// delivered (the `bash.consumed` host request): the queued notice is
/// stale and must withdraw (TS `_withdrawAsyncBashCompletionNotice`).
#[derive(Debug, Clone)]
struct BashConsumedNotice {
    pid: u32,
    command: String,
}

/// One admitted bash notice a later `bash.consumed` may still withdraw.
struct PendingNotice {
    request_id: String,
    pid: u32,
    command: String,
}

/// The job-settled seam of one durable session: the worker's session slot
/// it admits into, the closed-session gate, and the bash notices admitted
/// so far (process memory: the kernel that sends the withdrawals dies with
/// the worker).
#[derive(Clone)]
pub(crate) struct JobNotices {
    session: SessionSlot,
    core: Arc<Mutex<SessionCore>>,
    pending: Arc<Mutex<Vec<PendingNotice>>>,
}

impl JobNotices {
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
                    let settled = validate_completion(&payload.data)?;
                    notices.deliver(settled).await?;
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

    /// Admit one settled job (TS `bash.completed` ->
    /// `_promptInjectedMessage(message, { streamingBehavior: "steer",
    /// queueIfBusy: true, resumeIfIdle: true })`). A closed or closing
    /// session refuses it silently, like TS `_disposed`.
    async fn deliver(&self, settled: JobSettled) -> anyhow::Result<()> {
        {
            let core = self.core.lock().unwrap_or_else(PoisonError::into_inner);
            if !core.created || core.shutdown_requested {
                return Ok(());
            }
        }
        let Some(hosted) = self.session.get() else {
            return Ok(());
        };
        let row = create_job_settled_message(&settled, crate::util::now_ms());
        let request_id = format!("job-settled:{}", uuid::Uuid::new_v4());
        let request = InputRequest {
            text: row.content.text(),
            images: Vec::new(),
            custom_row: Some(crate::session_custom::custom_row_value(&row)),
            when_busy: WhenBusy::Steer,
            request_id: Some(request_id.clone()),
            origin: InputOrigin::Report {
                report: settled.report(),
            },
        };
        submit_input(&hosted.main()?, &request, &BACKGROUND_CONTEXT).await?;
        match settled {
            JobSettled::Bash { pid, command, .. } => self.pending().push(PendingNotice {
                request_id,
                pid,
                command,
            }),
            // A cell's output rides its notice; no read withdraws it.
            JobSettled::Cell { .. } => {}
        }
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
    /// scheduled-jobs cron wiring (`rlm_heartbeat.*`), the job-settled wake
    /// (`bash.completed`/`bash.consumed` and the detached-cell sink), and
    /// the agent messaging bridges (`agent_message.*`/`agent_observe.*`),
    /// merged into the config's extra host handlers.
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
        let notices = JobNotices::new(self.session.clone(), Arc::clone(&self.core));
        let handlers = config
            .extra_host_handlers
            .get_or_insert_with(HostRequestHandlers::default);
        notices.register(handlers);
        self.register_agent_messaging(handlers);
        config.job_settled = Some(Arc::new(move |settled: JobSettled| {
            let notices = notices.clone();
            tokio::spawn(async move {
                if let Err(error) = notices.deliver(settled).await {
                    eprintln!("eukhe-daemon settled job not delivered: {error:#}");
                }
            });
        }));
    }
}

/// TS `createAsyncBashCompletionHostHandler` validation: a positive
/// integer pid, a non-empty string command, an integer exit code.
fn validate_completion(data: &Value) -> anyhow::Result<JobSettled> {
    let consumed = validate_consumed(data)?;
    let exit_code = data
        .get("exitCode")
        .and_then(Value::as_i64)
        .ok_or_else(|| anyhow::anyhow!("bash.completed exitCode must be an integer"))?;
    Ok(JobSettled::Bash {
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

    fn completion() -> JobSettled {
        JobSettled::Bash {
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
        let notices = JobNotices::new(worker.session.clone(), Arc::clone(&worker.core));
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
        let notices = JobNotices::new(worker.session.clone(), Arc::clone(&worker.core));
        notices.deliver(completion()).await.expect("notice");
        let waited = worker
            .dispatch("wait_for_idle", &json!({ "activeSessionId": SESSION }))
            .await;
        assert!(waited.success, "{waited:?}");
        let rows = worker_rows(&worker, "eukhe.custom").await;
        // The harness-digest row rides the turn's first request (the rows
        // scan oldest-first: the notice row precedes it).
        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0]["customType"], json!("async_bash_completion"));
        assert_eq!(rows[1]["customType"], json!("harness_digest"));
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
