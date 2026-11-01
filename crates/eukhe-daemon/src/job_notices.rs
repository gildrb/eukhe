//! The one job-settled wake (ADR 0010): every job a session started that
//! settles after its call stopped blocking the turn — a background kernel
//! `bash()` command, a detached `ipython` cell — wakes the session through
//! [`JobNotices::deliver`]; the end of a `bash()` command the agent itself
//! stopped (`handle.kill()`) is dropped, never a wake.
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
//!
//! A headless (print/json/RPC) session gets the same wake through
//! [`HeadlessWakes`]: its notices admit straight into the in-process
//! session's main conversation.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock, PoisonError, Weak};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::messages::create_job_settled_message;
use eukhe_core::durable::{EukheSession, SessionConfig, SessionStorage};
use eukhe_durable::harness::types::WhenBusy;
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::job::{BashStopper, JobSettled};
use serde_json::Value;
use tokio::sync::futures::Notified;
use tokio::sync::Notify;

use eukhe_core::kernel::shared::{host_handler, HostRequestHandlers};

use crate::agent_message_ingest::{withdraw_queued, WithdrawnLane};
use crate::worker::{submit_input, InputRequest, RunAdmission, SessionCore, SessionSlot, Worker};

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

/// Where one session's settle notices are admitted.
#[derive(Clone)]
enum WakeTarget {
    /// A daemon worker's hosted session, admitted through its run gate;
    /// a closed or closing session refuses notices silently.
    Worker {
        session: SessionSlot,
        core: Arc<Mutex<SessionCore>>,
    },
    /// A headless (print/json/RPC) session of this process, bound once it
    /// opened ([`HeadlessWakes::bind`]); a dropped session refuses notices
    /// silently.
    Headless(Arc<OnceLock<Weak<EukheSession>>>),
}

/// The settle notices being admitted right now, shared by every clone of
/// one [`JobNotices`]: a job reads ended only after its notice entered
/// this count, so a quiescence check that reads the running jobs, then
/// this count, then the conversation's idleness never misses a wake.
#[derive(Default)]
struct InFlight {
    count: AtomicUsize,
    changed: Notify,
}

/// One notice being admitted; dropping it leaves the count.
struct Admitting(Arc<InFlight>);

impl Admitting {
    fn start(in_flight: &Arc<InFlight>) -> Self {
        in_flight.count.fetch_add(1, Ordering::SeqCst);
        Self(Arc::clone(in_flight))
    }
}

impl Drop for Admitting {
    fn drop(&mut self) {
        self.0.count.fetch_sub(1, Ordering::SeqCst);
        self.0.changed.notify_waiters();
    }
}

/// The job-settled seam of one durable session: where it admits, the bash
/// notices admitted so far (process memory: the kernel that sends the
/// withdrawals dies with the process), and the notices in flight.
#[derive(Clone)]
pub(crate) struct JobNotices {
    target: WakeTarget,
    pending: Arc<Mutex<Vec<PendingNotice>>>,
    in_flight: Arc<InFlight>,
}

impl JobNotices {
    pub(crate) fn new(session: SessionSlot, core: Arc<Mutex<SessionCore>>) -> Self {
        Self::with_target(WakeTarget::Worker { session, core })
    }

    fn with_target(target: WakeTarget) -> Self {
        Self {
            target,
            pending: Arc::default(),
            in_flight: Arc::default(),
        }
    }

    fn pending(&self) -> std::sync::MutexGuard<'_, Vec<PendingNotice>> {
        self.pending.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// The settle notices being admitted right now.
    pub(crate) fn in_flight(&self) -> usize {
        self.in_flight.count.load(Ordering::SeqCst)
    }

    /// Resolves after the in-flight count next drops. Enable it before a
    /// check so a drop racing the check still wakes the waiter.
    pub(crate) fn changed(&self) -> Notified<'_> {
        self.in_flight.changed.notified()
    }

    /// The `job_settled` sink: the notice counts as in flight from the
    /// call (before the job reads ended) until its admission is done.
    fn sink(&self) -> eukhe_core::durable::JobSettledSink {
        let notices = self.clone();
        Arc::new(move |settled: JobSettled| {
            let admitting = Admitting::start(&notices.in_flight);
            let notices = notices.clone();
            tokio::spawn(async move {
                if let Err(error) = notices.deliver(settled).await {
                    eprintln!("eukhe settled job not delivered: {error:#}");
                }
                drop(admitting);
            });
        })
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
                    // The kernel keeps the command active until this reply.
                    let admitting = Admitting::start(&notices.in_flight);
                    notices.deliver(settled).await?;
                    drop(admitting);
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
    /// session refuses it silently, like TS `_disposed`. A `bash()` command
    /// the agent itself stopped (`handle.kill()`) is dropped: its end is no
    /// news to the agent, so it neither wakes the session nor steers its
    /// turn.
    async fn deliver(&self, settled: JobSettled) -> anyhow::Result<()> {
        if let JobSettled::Bash {
            stopped_by: Some(BashStopper::Agent),
            ..
        } = &settled
        {
            return Ok(());
        }
        let row = create_job_settled_message(&settled, crate::util::now_ms());
        let report = settled.report();
        let request_id = format!("job-settled:{}", uuid::Uuid::new_v4());
        let request = InputRequest {
            text: row.content.text(),
            images: Vec::new(),
            custom_row: Some(crate::session_custom::custom_row_value(&row)),
            when_busy: WhenBusy::Steer,
            request_id: Some(request_id.clone()),
            origin: InputOrigin::Report { report },
        };
        match &self.target {
            WakeTarget::Worker { session, core } => {
                {
                    let core = core.lock().unwrap_or_else(PoisonError::into_inner);
                    if !core.created || core.shutdown_requested {
                        return Ok(());
                    }
                }
                let Some(hosted) = session.get() else {
                    return Ok(());
                };
                let admission = RunAdmission::enter(core).await;
                submit_input(&hosted.main()?, &request, &admission, &BACKGROUND_CONTEXT).await?;
                drop(admission);
            }
            WakeTarget::Headless(slot) => {
                let Some(session) = slot.get().and_then(Weak::upgrade) else {
                    return Ok(());
                };
                session
                    .main()
                    .submit(request.draft()?, &BACKGROUND_CONTEXT)
                    .await?;
            }
        }
        match settled {
            JobSettled::Bash { pid, command, .. } => self.pending().push(PendingNotice {
                request_id,
                pid,
                command,
            }),
            // A cell's or script's output rides its notice; no read
            // withdraws it.
            JobSettled::Cell { .. } | JobSettled::Shell { .. } => {}
        }
        Ok(())
    }

    /// Withdraw one queued notice (TS `bash.consumed` ->
    /// `_withdrawAsyncBashCompletionNotice`): the kernel read the finished
    /// command's result before the notice delivered. One read withdraws
    /// one notice — the front-most still-queued one for this pid and
    /// command (pids are reused across handles).
    async fn withdraw(&self, notice: &BashConsumedNotice) -> anyhow::Result<()> {
        let (harness, main) = match &self.target {
            WakeTarget::Worker { session, .. } => {
                let Some(hosted) = session.get() else {
                    return Ok(());
                };
                (hosted.harness().clone(), hosted.main()?)
            }
            WakeTarget::Headless(slot) => {
                let Some(session) = slot.get().and_then(Weak::upgrade) else {
                    return Ok(());
                };
                (session.harness().clone(), session.main())
            }
        };
        let candidates: Vec<String> = self
            .pending()
            .iter()
            .filter(|pending| pending.pid == notice.pid && pending.command == notice.command)
            .map(|pending| pending.request_id.clone())
            .collect();
        for request_id in candidates {
            // A notice queued before inputs carried their row as their entry
            // may still have its row queued as a separate `:row` write.
            let row_id = format!("{request_id}:row");
            let withdrawn = withdraw_queued(&harness, &main, |queued| {
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
    /// merged into the config's extra host handlers. Returns the session's
    /// notices (their in-flight count is part of its quiescence).
    pub(crate) fn wire_session_host(&self, config: &mut SessionConfig) -> JobNotices {
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
        config.job_settled = Some(notices.sink());
        notices
    }
}

/// The job-settled wake of one headless (print/json/RPC) session: the
/// same notices a daemon worker admits (a settled detached cell or `bash`
/// tool script, a finished background kernel `bash()` command), admitted
/// straight into the session's main conversation, so an idle session
/// wakes into the turn and a busy one takes the notice at its next
/// boundary.
#[derive(Clone)]
pub struct HeadlessWakes {
    session: Arc<OnceLock<Weak<EukheSession>>>,
    notices: JobNotices,
}

impl Default for HeadlessWakes {
    fn default() -> Self {
        let session = Arc::new(OnceLock::new());
        Self {
            notices: JobNotices::with_target(WakeTarget::Headless(Arc::clone(&session))),
            session,
        }
    }
}

impl HeadlessWakes {
    /// Wire the wake into a session about to open: the `job_settled` sink
    /// and the `bash.completed`/`bash.consumed` host handlers.
    pub fn wire(&self, config: &mut SessionConfig) {
        let handlers = config
            .extra_host_handlers
            .get_or_insert_with(HostRequestHandlers::default);
        self.notices.register(handlers);
        config.job_settled = Some(self.notices.sink());
    }

    /// Admit into `session` from now on (a notice before the bind, or
    /// after the session dropped, is refused silently).
    pub fn bind(&self, session: &Arc<EukheSession>) {
        // A second bind of the same wake keeps the first session: one
        // wake belongs to one open.
        let _first_bind_wins = self.session.set(Arc::downgrade(session));
    }

    /// The settle notices being admitted right now.
    #[must_use]
    pub fn in_flight(&self) -> usize {
        self.notices.in_flight()
    }

    /// Resolves after the in-flight count next drops (see
    /// [`HeadlessWakes::in_flight`]); enable it before a check.
    pub fn changed(&self) -> Notified<'_> {
        self.notices.changed()
    }
}

/// TS `createAsyncBashCompletionHostHandler` validation: a positive
/// integer pid, a non-empty string command, an integer exit code, and an
/// optional `stoppedBy` naming who stopped the command.
fn validate_completion(data: &Value) -> anyhow::Result<JobSettled> {
    let consumed = validate_consumed(data)?;
    let exit_code = data
        .get("exitCode")
        .and_then(Value::as_i64)
        .ok_or_else(|| anyhow::anyhow!("bash.completed exitCode must be an integer"))?;
    let stopped_by = match data.get("stoppedBy") {
        None => None,
        Some(stopper) => Some(
            serde_json::from_value::<BashStopper>(stopper.clone()).map_err(|error| {
                anyhow::anyhow!("bash.completed stoppedBy {stopper} is not a stopper: {error}")
            })?,
        ),
    };
    Ok(JobSettled::Bash {
        pid: consumed.pid,
        command: consumed.command,
        exit_code,
        stopped_by,
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
    const NOTICE: &str =
        "[bash-done pid:4321 exit:0]\n\nResume your work using the result below.\n\nCommand: \"sleep 1\"";

    fn completion() -> JobSettled {
        JobSettled::Bash {
            pid: 4321,
            command: "sleep 1".to_owned(),
            exit_code: 0,
            stopped_by: None,
        }
    }

    fn consumed() -> BashConsumedNotice {
        BashConsumedNotice {
            pid: 4321,
            command: "sleep 1".to_owned(),
        }
    }

    /// A busy session queues the notice (a steer placed as its card); the
    /// kernel's read withdraws exactly one queued notice, and a read for
    /// another command withdraws nothing.
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
        let queued = |count: usize| vec![("steer".to_owned(), NOTICE.to_owned()); count];
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

    /// An idle session wakes into the turn whose input is placed as the
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
        assert_eq!(users.len(), 0, "the notice row is the input's entry");
        let answers = worker_rows(&worker, "pi.assistant").await;
        assert_eq!(answers.len(), 1);
    }

    /// The drill's dev server, stopped by the agent's own `kill()` after
    /// its final answer: an idle session stays idle, with no row; no turn
    /// repeats the answer.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn an_agent_stopped_command_does_not_wake_an_idle_session() {
        let (_dir, worker) = created_worker(SESSION, json!(["repeated report"])).await;
        let notices = JobNotices::new(worker.session.clone(), Arc::clone(&worker.core));
        notices
            .deliver(JobSettled::Bash {
                pid: 4321,
                command: "npm run dev".to_owned(),
                exit_code: -15,
                stopped_by: Some(BashStopper::Agent),
            })
            .await
            .expect("notice");
        let waited = worker
            .dispatch("wait_for_idle", &json!({ "activeSessionId": SESSION }))
            .await;
        assert!(waited.success, "{waited:?}");
        assert_eq!(
            (
                worker_rows(&worker, "eukhe.custom").await,
                worker_rows(&worker, "pi.assistant").await,
                worker_inbox(&worker).await,
            ),
            (Vec::new(), Vec::new(), Vec::new())
        );
    }

    /// A busy session gets nothing queued for the agent's own stop: no
    /// steer into its turn.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn an_agent_stopped_command_never_steers_a_busy_turn() {
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
        notices
            .deliver(JobSettled::Bash {
                pid: 4321,
                command: "npm run dev".to_owned(),
                exit_code: -15,
                stopped_by: Some(BashStopper::Agent),
            })
            .await
            .expect("notice");
        assert_eq!(worker_inbox(&worker).await, Vec::new());
        let aborted = worker
            .dispatch("abort", &json!({ "activeSessionId": SESSION }))
            .await;
        assert!(aborted.success, "{aborted:?}");
    }

    #[test]
    fn completion_validation_matches_the_ts_contract() {
        assert!(validate_completion(&serde_json::json!({
            "pid": 4321,
            "command": "sleep 1",
            "exitCode": 0,
        }))
        .is_ok());
        assert_eq!(
            validate_completion(&serde_json::json!({
                "pid": 4321,
                "command": "sleep 30",
                "exitCode": -15,
                "stoppedBy": "agent",
            }))
            .expect("a stopped completion"),
            JobSettled::Bash {
                pid: 4321,
                command: "sleep 30".to_owned(),
                exit_code: -15,
                stopped_by: Some(BashStopper::Agent),
            }
        );
        assert!(validate_completion(&serde_json::json!({
            "pid": 4321,
            "command": "sleep 30",
            "exitCode": -15,
            "stoppedBy": "someone",
        }))
        .is_err());
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
