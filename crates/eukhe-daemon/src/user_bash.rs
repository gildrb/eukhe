//! The user bash surface (protocol breadth wave b5): the worker arms for
//! `execute_bash`, `execute_bash_and_wait`, and `abort_bash` (TS
//! daemon-mode cases over `AgentSession.runUserBash` / `executeBash` /
//! `abortBash`, with `bash_start`/`bash_output`/`bash_end` session events
//! and the durable `eukhe.bash` row, rendered as `bashExecution`).
//!
//! The execution port follows the TS stack: the local bash operations
//! (shell config, cwd guard, merged stdout+stderr streaming, kill on
//! abort), the executor (ANSI/binary sanitization, then the one bound with
//! its artifact, `eukhe_core::durable::bounded_output`), and the user-bash
//! wrapper (the already-running guard, the
//! identity echoed on start/end, transient rows staying unrecorded).
//!
//! Every run is a job of the session (`eukhe_core::durable::jobs`,
//! docs/harness.md S2): its process leads its own process group, and its
//! kill (`abort_bash`, a rewind) kills the group. `execute_bash_and_wait`
//! blocks at most the session's blocking budget: past it the call answers
//! detached with the output so far, the run goes on in the background, and
//! its end records its row as a settled run does.

use std::path::Path;
use std::process::Stdio;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::jobs::{self, Job, JobEvent, JobKind, JobSpec, JobTable, Wait};
use eukhe_core::durable::rlm::{kernel_bash_activity, BashActivityAction, BashActivityRequest};
use eukhe_core::durable::{bash_entry_draft, BashEntryData};
use eukhe_durable::harness::types::WriteSubmissionDraft;
use eukhe_durable::harness::Truncation;
use eukhe_types::daemon::{BashRun, SessionEvent};
use eukhe_types::job::JobId;
use serde_json::{json, Value};
use tokio::io::{AsyncRead, AsyncReadExt};
use tokio_util::sync::CancellationToken;

use eukhe_core::durable::bounded_output::BoundedOutput;
use eukhe_types::output::OmittedOutput;

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::{emit_worker_event_with, HostedSession, Worker};

/// The user-bash slot: one command runs at a time (TS `_userBashRunning`
/// plus the per-invocation abort controllers), with a kill switch the
/// `abort_bash` command pulls.
pub(crate) struct UserBash {
    /// The user-bash claim (`execute_bash` only; TS `runUserBash` guard).
    running: AtomicBool,
    /// Awaited bash runs in flight (TS `_bashAbortControllers.size`:
    /// `execute_bash_and_wait` runs count toward `isBashRunning` without
    /// claiming the exclusive user slot).
    awaited: AtomicUsize,
    /// An abort was requested: the settled result reports cancelled.
    abort_requested: AtomicBool,
    /// The jobs of the runs in flight (user bash and awaited runs):
    /// `abort_bash` kills them.
    runs: std::sync::Mutex<Vec<Job>>,
}

impl UserBash {
    pub(crate) fn new() -> Self {
        Self {
            running: AtomicBool::new(false),
            awaited: AtomicUsize::new(0),
            abort_requested: AtomicBool::new(false),
            runs: std::sync::Mutex::new(Vec::new()),
        }
    }

    /// Claim the slot; `false` when a user command is already running.
    /// A fresh claim clears any stale abort request (TS clears
    /// `_userBashAbortRequested` at each start, so a leftover flag cannot
    /// cancel an unrelated later run).
    fn claim(&self) -> bool {
        let claimed = self
            .running
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok();
        if claimed {
            self.abort_requested.store(false, Ordering::SeqCst);
        }
        claimed
    }

    fn release(&self) {
        self.running.store(false, Ordering::SeqCst);
    }

    /// Whether a user bash or an awaited bash run is in flight (TS
    /// `isBashRunning`: `_bashAbortControllers.size > 0 ||
    /// _userBashRunning`).
    pub(crate) fn is_running(&self) -> bool {
        self.running.load(Ordering::SeqCst) || self.awaited.load(Ordering::SeqCst) > 0
    }

    /// Count one awaited run (`execute_bash_and_wait`) toward
    /// [`Self::is_running`]; the awaited path owns no exclusive slot. The
    /// returned bracket decrements on drop, so a run future dropped
    /// mid-await (a task teardown) cannot leave the count stuck on.
    pub(crate) fn begin_awaited(&self) -> AwaitedRun<'_> {
        self.awaited.fetch_add(1, Ordering::SeqCst);
        AwaitedRun { user_bash: self }
    }

    /// Start the job of one run of `command` on the session's `jobs`: its
    /// kill cancels the returned token, on which the run kills its process
    /// group.
    fn start_run(&self, jobs: &JobTable, command: &str) -> (Job, CancellationToken) {
        let cancel = CancellationToken::new();
        let job = jobs.start(JobSpec {
            id: JobId::new(format!("bash-{}", uuid::Uuid::new_v4().simple()))
                .expect("a simple uuid is a header-safe job id"),
            kind: JobKind::UserBash,
            label: command.to_owned(),
            truncation: Truncation::default(),
            written: 0,
            kill: {
                let cancel = cancel.clone();
                Box::new(move |_| cancel.cancel())
            },
        });
        lock(&self.runs).push(job.clone());
        (job, cancel)
    }

    /// Kill every run in flight (TS `abortBash` aborts every controller);
    /// the settled runs report cancelled.
    pub(crate) fn abort(&self) {
        self.abort_requested.store(true, Ordering::SeqCst);
        for job in lock(&self.runs).iter() {
            job.kill();
        }
    }
}

impl Worker {
    /// Rust-native kernel bash activity commands. These inspect the Python
    /// handle registry of the main conversation's kernel (never booting
    /// one), not the user-bash slot or a client-supplied PID.
    pub(crate) async fn handle_kernel_bash_activity(
        &self,
        command_type: &str,
        payload: &Value,
    ) -> DaemonResponse {
        let hosted = match self.hosted(command_type) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let action = match command_type {
            "list_kernel_bash" => BashActivityAction::List,
            "tail_kernel_bash" => BashActivityAction::Tail,
            "kill_kernel_bash" => BashActivityAction::Kill,
            _ => return response_failure(None, command_type, "Unknown kernel bash command", None),
        };
        let activity_id = payload.get("activityId").and_then(Value::as_str);
        if action != BashActivityAction::List && activity_id.is_none_or(str::is_empty) {
            return response_failure(None, command_type, "activityId is required", None);
        }
        let lines = if action == BashActivityAction::Tail {
            match payload.get("lines") {
                None => 50,
                Some(value) => match value.as_u64().and_then(|lines| usize::try_from(lines).ok()) {
                    Some(lines) if (1..=200).contains(&lines) => lines,
                    _ => {
                        return response_failure(
                            None,
                            command_type,
                            "lines must be between 1 and 200",
                            None,
                        )
                    }
                },
            }
        } else {
            50
        };
        let main = match hosted.main() {
            Ok(main) => main,
            Err(error) => return response_failure(None, command_type, &error.to_string(), None),
        };
        let request = BashActivityRequest {
            action,
            activity_id: activity_id.map(str::to_string),
            lines,
        };
        match kernel_bash_activity(hosted.deps(), main.id(), request).await {
            Ok(mut fields) => {
                if let Some(object) = fields.as_object_mut() {
                    object.remove("event");
                    object.remove("status");
                    object.remove("reason");
                    object.remove("id"); // kernel request id, not activity id
                    object.remove("activityId");
                    if let Some(activity_id) = activity_id {
                        object.insert("id".to_string(), json!(activity_id));
                    }
                }
                response_success(None, command_type, Some(fields))
            }
            Err(error) => response_failure(None, command_type, &error.to_string(), None),
        }
    }

    /// `execute_bash { command, excludeFromContext?, transient?, runId? }`
    /// (TS `runUserBash`): the already-running guard rejects a second
    /// command, the response goes out before the run completes, output
    /// streams as `bash_output` events, and the settled `bash_end` (plus
    /// the durable `eukhe.bash` row, unless transient) follows. The row is a
    /// write submission keyed by the run's request id, so a retried write
    /// never records the run twice; the Harness inbox places it at the next
    /// boundary while a run is busy.
    pub(crate) fn handle_execute_bash(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted("execute_bash") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(command) = payload.get("command").and_then(Value::as_str) else {
            return response_failure(
                None,
                "execute_bash",
                "execute_bash requires a command",
                None,
            );
        };
        // Claim the slot synchronously (TS claims before the async dispatch
        // could slip a second command through).
        if !self.user_bash.claim() {
            return response_failure(
                None,
                "execute_bash",
                "A bash command is already running",
                None,
            );
        }
        let exclude_from_context = payload
            .get("excludeFromContext")
            .and_then(Value::as_bool)
            .unwrap_or(false);
        let transient = payload
            .get("transient")
            .and_then(Value::as_bool)
            .unwrap_or(false);
        let run_id = payload.get("runId").and_then(Value::as_str);
        let request_id = bash_request_id(run_id);
        let run = BashRun {
            transient,
            run_id: run_id.map(str::to_owned),
        };
        self.emit_worker_event(SessionEvent::BashStart {
            command: command.to_owned(),
            exclude_from_context,
            run: run.clone(),
        });
        // The run outlives the response (bash can exceed the client's
        // request timeout); completion streams via bash_end.
        let core = Arc::clone(&self.core);
        let events = Arc::clone(&self.events);
        let session = self.session.clone();
        let user_bash = Arc::clone(&self.user_bash);
        let (job, cancel) = user_bash.start_run(&hosted.deps().jobs, command);
        let stream = OutputStream::shared(
            hosted.storage_dir(),
            Some((Arc::clone(&core), Arc::clone(&events))),
            job.clone(),
        );
        let command = command.to_string();
        let agent_dir = self.config.agent_dir.clone();
        tokio::spawn(async move {
            let cwd = lock(&core).cwd.clone();
            let settings = eukhe_core::settings::SettingsManager::create(&cwd, &agent_dir);
            let prefix = settings.settings().shell_command_prefix.clone();
            let shell_path = settings.settings().shell_path.clone();
            let end = run_bash(RunBash {
                command: &command,
                cwd: &cwd,
                prefix: prefix.as_deref(),
                shell_path: shell_path.as_deref(),
                user_bash: &user_bash,
                job,
                cancel,
                stream,
            })
            .await;
            // Persist the durable row (transient runs live only in their
            // pane; reloads and rebuilds cannot resurface them).
            if !transient {
                let result = BashResult {
                    output: end.output.clone(),
                    exit_code: end.exit_code,
                    cancelled: end.cancelled,
                    omitted: end.omitted,
                    artifact: end.artifact.clone(),
                    detached: None,
                };
                if let Some(hosted) = session.get() {
                    let row = BashRow {
                        command: &command,
                        result: &result,
                        exclude_from_context,
                        request_id,
                    };
                    if let Err(error) = record_bash_result(&hosted, row).await {
                        eprintln!("eukhe-daemon worker: recording the bash run failed: {error:#}");
                    }
                }
            }
            user_bash.release();
            emit_worker_event_with(
                &core,
                &events,
                SessionEvent::BashEnd {
                    exit_code: end.exit_code,
                    cancelled: end.cancelled,
                    output: end.output,
                    omitted: end.omitted,
                    artifact: end.artifact,
                    error_message: end.error_message,
                    run,
                },
            );
        });
        response_success(None, "execute_bash", None)
    }

    /// `execute_bash_and_wait { command }` (TS `executeBash` over the
    /// awaited path): run, record the row, and answer the `BashResult` wire
    /// shape. The call blocks at most the session's blocking budget: past
    /// it the answer is detached (`detached: {job, budgetMs}`, the output
    /// so far), and the run's end records its row in the background.
    pub(crate) async fn handle_execute_bash_and_wait(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted("execute_bash_and_wait") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(command) = payload.get("command").and_then(Value::as_str) else {
            return response_failure(
                None,
                "execute_bash_and_wait",
                "execute_bash_and_wait requires a command",
                None,
            );
        };
        // A fresh run owns a fresh abort state (each TS invocation owns its
        // own controller).
        self.user_bash
            .abort_requested
            .store(false, Ordering::SeqCst);
        let (cwd, prefix, shell_path) = {
            let cwd = lock(&self.core).cwd.clone();
            let settings =
                eukhe_core::settings::SettingsManager::create(&cwd, &self.config.agent_dir);
            let settings = settings.settings();
            (
                cwd,
                settings.shell_command_prefix.clone(),
                settings.shell_path.clone(),
            )
        };
        let request_id = bash_request_id(payload.get("runId").and_then(Value::as_str));
        let (job, cancel) = self.user_bash.start_run(&hosted.deps().jobs, command);
        // The awaited path emits nothing (TS passes no `onChunk`).
        let stream = OutputStream::shared(hosted.storage_dir(), None, job.clone());
        let job_id = job.id().clone();
        let mut run = {
            let user_bash = Arc::clone(&self.user_bash);
            let command = command.to_owned();
            let stream = Arc::clone(&stream);
            tokio::spawn(async move {
                // The awaited run counts toward the session's
                // `isBashRunning` (TS's `executeBash` registers an abort
                // controller, so the flag is true for its whole duration);
                // it owns no exclusive slot, so a streamed user bash is not
                // blocked by it. The bracket releases the count on drop, so
                // a dropped run cannot leave the flag stuck on.
                let _awaited = user_bash.begin_awaited();
                run_bash(RunBash {
                    command: &command,
                    cwd: &cwd,
                    prefix: prefix.as_deref(),
                    shell_path: shell_path.as_deref(),
                    user_bash: &user_bash,
                    job,
                    cancel,
                    stream,
                })
                .await
            })
        };
        let budget = hosted.deps().blocking_budget();
        let joined = match jobs::wait_until(tokio::time::Instant::now() + budget, &mut run).await {
            Wait::Settled(joined) => joined,
            Wait::Detached => {
                let (output, bounded) = lock(&stream).output.projection();
                let (omitted, artifact) = bounded.map_or((None, None), |diagnostic| {
                    (diagnostic.omitted, diagnostic.artifact)
                });
                let roster_pushes = self.roster_pushes.clone();
                let command = command.to_owned();
                tokio::spawn(async move {
                    let settled = match run.await {
                        Ok(end) => {
                            settle_awaited_run(&hosted, &roster_pushes, &command, request_id, end)
                                .await
                                .map(drop)
                        }
                        Err(error) => Err(format!("the bash run failed: {error}")),
                    };
                    if let Err(error) = settled {
                        eprintln!("eukhe-daemon worker: a detached bash run: {error}");
                    }
                });
                let result = BashResult {
                    output,
                    exit_code: None,
                    cancelled: false,
                    omitted,
                    artifact,
                    detached: Some(DetachedRun {
                        job: job_id,
                        budget_ms: u64::try_from(budget.as_millis()).unwrap_or(u64::MAX),
                    }),
                };
                return response_success(
                    None,
                    "execute_bash_and_wait",
                    Some(serde_json::to_value(&result).unwrap_or(Value::Null)),
                );
            }
        };
        let end = match joined {
            Ok(end) => end,
            Err(error) => {
                return response_failure(
                    None,
                    "execute_bash_and_wait",
                    &format!("the bash run failed: {error}"),
                    None,
                )
            }
        };
        match settle_awaited_run(&hosted, &self.roster_pushes, command, request_id, end).await {
            Ok(result) => response_success(
                None,
                "execute_bash_and_wait",
                Some(serde_json::to_value(&result).unwrap_or(Value::Null)),
            ),
            Err(error) => response_failure(None, "execute_bash_and_wait", &error, None),
        }
    }

    /// `abort_bash` (TS `abortBash`): kill the in-flight command; the
    /// settled run reports cancelled. Always a success.
    pub(crate) fn handle_abort_bash(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("abort_bash") {
            return response;
        }
        self.user_bash.abort();
        response_success(None, "abort_bash", None)
    }
}

/// The write-submission request id of one bash run: the client's `runId`
/// when it names the run, else a fresh id minted when the run starts (one
/// run, one row).
fn bash_request_id(run_id: Option<&str>) -> String {
    match run_id.filter(|run_id| !run_id.is_empty()) {
        Some(run_id) => format!("user-bash:{run_id}"),
        None => format!("user-bash:{}", uuid::Uuid::new_v4()),
    }
}

fn lock<T>(mutex: &std::sync::Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// The wire identity echoed on `bash_start`/`bash_end` (TS `identity`).
/// The drop-bracket [`UserBash::begin_awaited`] returns: one awaited run's
/// contribution to the `isBashRunning` flag, released even when the run's
/// future is dropped mid-await.
pub(crate) struct AwaitedRun<'a> {
    user_bash: &'a UserBash,
}

impl Drop for AwaitedRun<'_> {
    fn drop(&mut self) {
        self.user_bash.awaited.fetch_sub(1, Ordering::SeqCst);
    }
}

/// The `BashResult` wire shape.
#[derive(Debug, Clone, serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct BashResult {
    output: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    exit_code: Option<i64>,
    cancelled: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    omitted: Option<OmittedOutput>,
    #[serde(skip_serializing_if = "Option::is_none")]
    artifact: Option<String>,
    /// Set when the awaited call outlived the blocking budget: the run
    /// goes on as this job.
    #[serde(skip_serializing_if = "Option::is_none")]
    detached: Option<DetachedRun>,
}

/// An awaited run that outlived the blocking budget.
#[derive(Debug, Clone, serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct DetachedRun {
    job: JobId,
    budget_ms: u64,
}

/// The settled user-bash run (TS `UserBashEndDetails` plus the output it
/// carries for the durable row).
struct BashEnd {
    output: String,
    exit_code: Option<i64>,
    cancelled: bool,
    omitted: Option<OmittedOutput>,
    artifact: Option<String>,
    error_message: Option<String>,
}

/// One process run (TS `executeBashWithOperations` over the local bash
/// operations), its output bounded once.
struct RunBash<'a> {
    command: &'a str,
    cwd: &'a str,
    prefix: Option<&'a str>,
    shell_path: Option<&'a str>,
    user_bash: &'a UserBash,
    /// The run's job ([`UserBash::start_run`]), which the run ends.
    job: Job,
    /// Cancelled by the job's kill.
    cancel: CancellationToken,
    stream: Arc<std::sync::Mutex<OutputStream>>,
}

/// The streaming emit target of a run's chunks (the executor's `onChunk`).
type ChunkTarget = (
    Arc<std::sync::Mutex<crate::worker::SessionCore>>,
    Arc<crate::worker::EventPump>,
);

/// The streaming accumulator (TS `onData`): the sanitizing decode, the one
/// bound with its artifact, the chunk callback, and the job's output.
struct OutputStream {
    output: BoundedOutput,
    /// `None` on the awaited path, which emits nothing.
    on_chunk: Option<ChunkTarget>,
    job: Job,
}

impl OutputStream {
    /// The accumulator of `job`'s run; an output past the bound keeps its
    /// artifact in `storage_dir` (the session's storage).
    fn shared(
        storage_dir: Option<&Path>,
        on_chunk: Option<ChunkTarget>,
        job: Job,
    ) -> Arc<std::sync::Mutex<Self>> {
        Arc::new(std::sync::Mutex::new(Self {
            output: BoundedOutput::in_session(
                storage_dir,
                job.id().as_str(),
                Truncation::default(),
            ),
            on_chunk,
            job,
        }))
    }

    fn push(&mut self, data: &[u8]) {
        let text = sanitize_output(&String::from_utf8_lossy(data));
        if text.is_empty() {
            return;
        }
        self.output.push(&text);
        self.job.record(JobEvent::Output(text.len() as u64));
        if let Some((core, events)) = &self.on_chunk {
            emit_worker_event_with(core, events, SessionEvent::BashOutput { chunk: text });
        }
    }
}

/// Run one command to its end, then end its job: a run that could not
/// spawn exits 127 (the shell's code for a command it cannot run), a
/// cancelled run or a signal death is killed, else it exits with its
/// code.
async fn run_bash(run: RunBash<'_>) -> BashEnd {
    let RunBash {
        command,
        cwd,
        prefix,
        shell_path,
        user_bash,
        job,
        cancel,
        stream,
    } = run;
    let spawn_failure = |message: String| BashEnd {
        output: String::new(),
        exit_code: None,
        cancelled: false,
        omitted: None,
        artifact: None,
        error_message: Some(message),
    };
    let end = 'run: {
        let resolved = match prefix.filter(|prefix| !prefix.is_empty()) {
            Some(prefix) => format!("{prefix}\n{command}"),
            None => command.to_string(),
        };
        if !Path::new(cwd).exists() {
            // TS local operations reject before spawning.
            break 'run spawn_failure(format!(
                "Working directory does not exist: {cwd}\nCannot execute bash commands."
            ));
        }
        let shell = match eukhe_core::platform::shell::get_shell_config(shell_path) {
            Ok(shell) => shell,
            Err(error) => break 'run spawn_failure(error.to_string()),
        };
        let mut process = tokio::process::Command::new(&shell.shell);
        process
            .args(&shell.args)
            .arg(&resolved)
            .current_dir(cwd)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        // Its own process group, so a kill reaches every process it starts.
        eukhe_core::platform::process::set_new_process_group(process.as_std_mut());
        let mut child = match process.spawn() {
            Ok(child) => child,
            Err(error) => break 'run spawn_failure(error.to_string()),
        };
        let group = child.id().and_then(|pid| i32::try_from(pid).ok());
        // A late abort that arrived before the process spawned kills it
        // immediately (TS honors `_userBashAbortRequested` before
        // executing); the flag still settles the run cancelled.
        if user_bash.abort_requested.load(Ordering::SeqCst) {
            cancel.cancel();
        }
        let stdout = child.stdout.take();
        let stderr = child.stderr.take();
        // stdout and stderr merge into one stream (TS wires both pipes to
        // the same `onData`); order between them is arrival order. The
        // shared accumulator keeps the merged order the interleaved reads
        // produce.
        let pump = |mut reader: Box<dyn AsyncRead + Unpin + Send>| {
            let stream = Arc::clone(&stream);
            async move {
                let mut buffer = [0u8; 8192];
                loop {
                    match reader.read(&mut buffer).await {
                        Ok(0) | Err(_) => break,
                        Ok(read) => lock(&stream).push(&buffer[..read]),
                    }
                }
            }
        };
        let stdout_pump = stdout.map(|pipe| pump(Box::new(pipe)));
        let stderr_pump = stderr.map(|pipe| pump(Box::new(pipe)));
        let pumps = async move {
            match (stdout_pump, stderr_pump) {
                (Some(stdout_pump), Some(stderr_pump)) => {
                    futures::future::join(stdout_pump, stderr_pump).await;
                }
                (Some(pump), None) | (None, Some(pump)) => pump.await,
                (None, None) => {}
            }
        };
        tokio::pin!(pumps);
        tokio::select! {
            () = &mut pumps => {}
            () = cancel.cancelled() => {
                if let Some(group) = group {
                    // A group already gone has nothing left to kill.
                    let _ = eukhe_core::platform::process::kill_process_group_or_pid(group);
                }
                pumps.await;
            }
        }
        // A command that closed its pipes still runs: the cancel kills its
        // group while the wait runs too. A signal death reports no exit
        // code.
        let waited = tokio::select! {
            biased;
            waited = child.wait() => waited,
            () = cancel.cancelled() => {
                if let Some(group) = group {
                    // A group already gone has nothing left to kill.
                    let _ = eukhe_core::platform::process::kill_process_group_or_pid(group);
                }
                child.wait().await
            }
        };
        let exit_code = waited.ok().and_then(|status| status.code()).map(i64::from);
        let cancelled = user_bash.abort_requested.load(Ordering::SeqCst) || cancel.is_cancelled();
        let (output, bounded) = lock(&stream).output.projection();
        let (omitted, artifact) = match bounded {
            Some(diagnostic) => {
                if diagnostic.artifact.is_none() {
                    eprintln!("eukhe-daemon: user bash: {}", diagnostic.message);
                }
                (diagnostic.omitted, diagnostic.artifact)
            }
            None => (None, None),
        };
        BashEnd {
            output,
            exit_code: if cancelled { None } else { exit_code },
            cancelled,
            omitted,
            artifact,
            error_message: None,
        }
    };
    job.record(match (&end.error_message, end.exit_code) {
        (Some(_), _) => JobEvent::Exited(127),
        (None, Some(code)) => JobEvent::Exited(code),
        (None, None) => JobEvent::Killed,
    });
    lock(&user_bash.runs).retain(|run| run.id() != job.id());
    end
}

/// One settled run's durable row.
struct BashRow<'a> {
    command: &'a str,
    result: &'a BashResult,
    exclude_from_context: bool,
    request_id: String,
}

/// Record one bash outcome as the durable `eukhe.bash` row (TS
/// `recordBashResult`; the row renders as a `bashExecution` message and
/// joins the model context unless excluded) through a write submission on
/// the main conversation, then wait until its `message_start`/`message_end`
/// pair reached the wire (so `bash_end` follows the row, as before).
async fn record_bash_result(hosted: &HostedSession, row: BashRow<'_>) -> anyhow::Result<()> {
    let data = BashEntryData {
        command: row.command.to_string(),
        output: row.result.output.clone(),
        exit_code: row.result.exit_code,
        cancelled: row.result.cancelled,
        omitted: row.result.omitted,
        artifact: row.result.artifact.clone(),
        exclude_from_context: row.exclude_from_context.then_some(true),
    };
    let entry = bash_entry_draft(data, crate::util::now_ms())?;
    hosted
        .main()?
        .submit(
            WriteSubmissionDraft {
                request_id: Some(row.request_id),
                entry,
            },
            &BACKGROUND_CONTEXT,
        )
        .await?;
    hosted.events_delivered().await;
    Ok(())
}

/// Settle one awaited run (`execute_bash_and_wait`): flush the roster, then
/// record its row. The awaited path emits no session events, so the live
/// roster feed has no trigger of its own — TS's `execute_bash_and_wait`
/// flushes in the command's `finally`; the port enqueues the same flush
/// (the summary composes fresh, so the settled run reads idle on the
/// roster). The result, or the error the call answers.
async fn settle_awaited_run(
    hosted: &HostedSession,
    roster_pushes: &crate::roster_activity::RosterPushQueue,
    command: &str,
    request_id: String,
    end: BashEnd,
) -> Result<BashResult, String> {
    roster_pushes.push();
    if let Some(error) = end.error_message {
        return Err(error);
    }
    let result = BashResult {
        output: end.output,
        exit_code: end.exit_code,
        cancelled: end.cancelled,
        omitted: end.omitted,
        artifact: end.artifact,
        detached: None,
    };
    let row = BashRow {
        command,
        result: &result,
        exclude_from_context: false,
        request_id,
    };
    record_bash_result(hosted, row)
        .await
        .map_err(|error| format!("{error:#}"))?;
    Ok(result)
}

/// Sanitize one output chunk (TS `strip-ansi` + `sanitizeBinaryOutput` +
/// the `\r` strip in the executor's `onData`).
fn sanitize_output(text: &str) -> String {
    let stripped = strip_ansi(text);
    let mut out = String::with_capacity(stripped.len());
    for character in stripped.chars() {
        let code = character as u32;
        // Tab, newline, carriage return stay.
        if matches!(code, 0x09 | 0x0a | 0x0d) {
            out.push(character);
            continue;
        }
        // Control characters and the format characters that break width
        // rendering drop (TS `sanitizeBinaryOutput`).
        if code <= 0x1f || (0xfff9..=0xfffb).contains(&code) {
            continue;
        }
        out.push(character);
    }
    out.replace('\r', "")
}

/// Strip ANSI escape sequences (CSI sequences and the simple two-byte
/// escapes the `strip-ansi` package handles).
fn strip_ansi(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(character) = chars.next() {
        if character != '\u{1b}' {
            out.push(character);
            continue;
        }
        match chars.next() {
            // CSI: parameters and intermediates run to the final byte
            // (0x40-0x7e).
            Some('[') => {
                for next in chars.by_ref() {
                    if ('\u{40}'..='\u{7e}').contains(&next) {
                        break;
                    }
                }
            }
            // A simple escape sequence: one following byte.
            Some(_) => {}
            // A trailing escape with nothing after it drops.
            None => break,
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::durable_test_support::{created_worker, created_worker_with, worker_rows};
    use eukhe_core::durable::jobs::JobEnd;
    use serde_json::json;
    use std::time::{Duration, Instant};

    const SESSION: &str = "bash-session";

    async fn bash_rows(worker: &Worker) -> Vec<Value> {
        worker_rows(worker, "eukhe.bash").await
    }

    async fn bash_running(worker: &Worker) -> bool {
        let state = worker
            .dispatch(
                "get_connection_state",
                &json!({ "activeSessionId": SESSION }),
            )
            .await;
        state.data.expect("state data")["isBashRunning"] == json!(true)
    }

    /// Poll the connection state until the bash flag reads `running`.
    async fn wait_bash_running(worker: &Worker, running: bool) {
        let deadline = Instant::now() + Duration::from_secs(10);
        while bash_running(worker).await != running {
            assert!(
                Instant::now() < deadline,
                "isBashRunning never became {running}"
            );
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }

    /// `execute_bash_and_wait` answers the TS `BashResult` wire shape and
    /// records the durable `eukhe.bash` row (rendered `bashExecution`).
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn execute_bash_and_wait_matches_the_ts_result_shape() {
        let (_dir, worker) = created_worker(SESSION, json!(["ack"])).await;
        let response = worker
            .dispatch(
                "execute_bash_and_wait",
                &json!({ "activeSessionId": SESSION, "command": "echo hello" }),
            )
            .await;
        assert!(response.success, "failed: {response:?}");
        let data = response.data.expect("data");
        assert_eq!(
            data,
            json!({ "output": "hello\n", "exitCode": 0, "cancelled": false })
        );

        let rows = bash_rows(&worker).await;
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0]["role"], json!("bashExecution"));
        assert_eq!(rows[0]["command"], json!("echo hello"));
        assert_eq!(rows[0]["output"], json!("hello\n"));
        assert_eq!(rows[0]["exitCode"], json!(0));
        assert!(rows[0].get("excludeFromContext").is_none());

        // Failures carry the exit status and the merged stderr.
        let response = worker
            .dispatch(
                "execute_bash_and_wait",
                &json!({ "activeSessionId": SESSION, "command": "echo boom >&2; exit 3" }),
            )
            .await;
        assert!(response.success);
        let data = response.data.expect("data");
        assert_eq!(data["exitCode"], json!(3));
        assert_eq!(data["output"], json!("boom\n"));

        let response = worker
            .dispatch(
                "execute_bash_and_wait",
                &json!({ "activeSessionId": SESSION }),
            )
            .await;
        assert!(!response.success);
        assert_eq!(
            response.error.as_deref(),
            Some("execute_bash_and_wait requires a command")
        );
    }

    /// A long run is bounded once, by the shared owner: the end of the
    /// output survives, the typed `omitted` names the middle, and the
    /// artifact holds every line.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_long_run_keeps_its_end_and_names_the_artifact() {
        let (_dir, worker) = created_worker(SESSION, json!(["ack"])).await;
        let response = worker
            .dispatch(
                "execute_bash_and_wait",
                &json!({ "activeSessionId": SESSION, "command": "seq 1 5000" }),
            )
            .await;
        assert!(response.success, "failed: {response:?}");
        let data = response.data.expect("data");
        let lines = |range: std::ops::RangeInclusive<u32>| {
            range.map(|n| n.to_string() + "\n").collect::<String>()
        };
        let (all, head, tail) = (lines(1..=5000), lines(1..=1000), lines(4001..=5000));
        assert_eq!(data["output"], json!(format!("{head}{tail}")));
        assert_eq!(
            data["omitted"],
            json!({
                "bytes": all.len() - head.len() - tail.len(),
                "lines": 3000,
                "at": { "afterLine": 1000 },
            })
        );
        let artifact = Path::new(data["artifact"].as_str().expect("artifact path"));
        let hosted = worker.session.get().expect("hosted session");
        let storage_dir = hosted.storage_dir().expect("storage dir");
        assert!(
            artifact.starts_with(storage_dir.join("tool-output")),
            "{artifact:?} is in the session"
        );
        assert_eq!(std::fs::read_to_string(artifact).expect("artifact"), all);
    }

    /// A run's row is a write submission keyed by its `runId`: a retried
    /// run with the same id never records a second row.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_retried_run_id_records_one_row() {
        let (_dir, worker) = created_worker(SESSION, json!(["ack"])).await;
        for _ in 0..2 {
            let response = worker
                .dispatch(
                    "execute_bash_and_wait",
                    &json!({ "activeSessionId": SESSION, "command": "echo once", "runId": "run-1" }),
                )
                .await;
            assert!(response.success, "failed: {response:?}");
        }
        assert_eq!(bash_rows(&worker).await.len(), 1);
    }

    /// The awaited-run bracket releases its count on drop even when the
    /// run's future never completes (a task teardown mid-await must not
    /// leave `isBashRunning` stuck on).
    #[test]
    fn an_abandoned_awaited_run_releases_the_flag() {
        let user_bash = UserBash::new();
        assert!(!user_bash.is_running());
        {
            let _awaited = user_bash.begin_awaited();
            assert!(user_bash.is_running());
        }
        assert!(
            !user_bash.is_running(),
            "the dropped bracket left the awaited count stuck on"
        );
    }

    /// The awaited run counts toward the session's `isBashRunning` (TS's
    /// `executeBash` registers an abort controller for the run's
    /// duration): the flag reads true while it runs and false once it
    /// settles — without claiming the exclusive user slot.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn an_awaited_bash_run_reports_running_to_the_connection_state() {
        let (dir, worker) = created_worker(SESSION, json!(["ack"])).await;
        let gate = dir.path().join("gate");
        let command = format!("while [ ! -f {} ]; do sleep 0.01; done", gate.display());
        let runner = Arc::clone(&worker);
        let run = tokio::spawn(async move {
            runner
                .dispatch(
                    "execute_bash_and_wait",
                    &json!({ "activeSessionId": SESSION, "command": command }),
                )
                .await
        });
        wait_bash_running(&worker, true).await;
        std::fs::write(&gate, "").expect("open the gate");
        let response = run.await.expect("the awaited run task panicked");
        assert!(response.success, "failed: {response:?}");
        assert!(
            !bash_running(&worker).await,
            "the settled run left the flag on"
        );
    }

    /// Past the session's blocking budget an awaited run answers detached
    /// with its job and the output so far; the run goes on as a job (still
    /// `isBashRunning`), and its end records its row.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn an_awaited_run_past_the_budget_answers_detached_and_its_end_records_its_row() {
        let (dir, worker) = created_worker(SESSION, json!(["ack"])).await;
        std::fs::write(
            dir.path().join("agent").join("settings.json"),
            r#"{"toolBlockingBudgetMs":300}"#,
        )
        .expect("settings");
        let gate = dir.path().join("gate");
        let command = format!(
            "echo started; while [ ! -f {} ]; do sleep 0.01; done; echo done",
            gate.display()
        );
        let response = worker
            .dispatch(
                "execute_bash_and_wait",
                &json!({ "activeSessionId": SESSION, "command": command }),
            )
            .await;
        assert!(response.success, "failed: {response:?}");
        let data = response.data.expect("data");
        let job = data["detached"]["job"].clone();
        assert_eq!(
            data,
            json!({
                "output": "started\n",
                "cancelled": false,
                "detached": { "job": job, "budgetMs": 300 },
            })
        );
        let hosted = worker.session.get().expect("hosted session");
        let running = hosted
            .deps()
            .jobs
            .get(job.as_str().expect("job id"))
            .expect("the run's job");
        assert!(running.is_running() && bash_running(&worker).await);
        assert_eq!(bash_rows(&worker).await.len(), 0);

        std::fs::write(&gate, "").expect("open the gate");
        assert_eq!(
            tokio::time::timeout(Duration::from_secs(10), running.ended())
                .await
                .expect("the run ends"),
            JobEnd::Exited(0)
        );
        let deadline = Instant::now() + Duration::from_secs(10);
        let rows = loop {
            let rows = bash_rows(&worker).await;
            if !rows.is_empty() {
                break rows;
            }
            assert!(Instant::now() < deadline, "the detached run never recorded");
            tokio::time::sleep(Duration::from_millis(10)).await;
        };
        assert_eq!(
            (
                rows.len(),
                rows[0]["output"].clone(),
                rows[0]["exitCode"].clone()
            ),
            (1, json!("started\ndone\n"), json!(0))
        );
        wait_bash_running(&worker, false).await;
    }

    /// `execute_bash` responds before completion (no data), claims the
    /// slot (a second command answers the TS already-running refusal),
    /// `abort_bash` kills the run, and the excluded row carries the
    /// `excludeFromContext` flag.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn execute_bash_claims_the_slot_and_aborts() {
        let (_dir, worker) = created_worker(SESSION, json!(["ack"])).await;
        let response = worker
            .dispatch(
                "execute_bash",
                &json!({
                    "activeSessionId": SESSION,
                    "command": "sleep 30",
                    "excludeFromContext": true,
                }),
            )
            .await;
        assert!(response.success, "failed: {response:?}");
        assert!(response.data.is_none(), "responds before completion");

        // The slot is claimed while the command runs.
        assert!(bash_running(&worker).await);
        let refusal = worker
            .dispatch(
                "execute_bash",
                &json!({ "activeSessionId": SESSION, "command": "echo nope" }),
            )
            .await;
        assert!(!refusal.success);
        assert_eq!(
            refusal.error.as_deref(),
            Some("A bash command is already running")
        );

        // Abort settles the run; the durable row records the cancelled
        // outcome with the context-exclusion flag.
        let aborted = worker
            .dispatch("abort_bash", &json!({ "activeSessionId": SESSION }))
            .await;
        assert!(aborted.success, "failed: {aborted:?}");
        wait_bash_running(&worker, false).await;
        let rows = bash_rows(&worker).await;
        assert_eq!(rows.len(), 1, "the cancelled run still records");
        assert_eq!(rows[0]["cancelled"], json!(true));
        assert_eq!(rows[0]["excludeFromContext"], json!(true));
        assert!(
            rows[0].get("exitCode").is_none(),
            "killed runs carry no exit code"
        );
    }

    /// `abort_bash` kills a command that closed its stdout and stderr: the
    /// pipes end at once, but the process runs until the kill.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn abort_bash_kills_a_command_that_closed_its_pipes() {
        let (dir, worker) = created_worker(SESSION, json!(["ack"])).await;
        let closed = dir.path().join("closed");
        let command = format!(
            "touch {}; exec >/dev/null 2>&1; sleep 1e6",
            closed.display()
        );
        let response = worker
            .dispatch(
                "execute_bash",
                &json!({ "activeSessionId": SESSION, "command": command }),
            )
            .await;
        assert!(response.success, "failed: {response:?}");
        let deadline = Instant::now() + Duration::from_secs(10);
        while !closed.exists() {
            assert!(Instant::now() < deadline, "the command never ran");
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
        // Let the pumps see the closed pipes.
        tokio::time::sleep(Duration::from_millis(200)).await;
        assert!(bash_running(&worker).await);

        let aborted = worker
            .dispatch("abort_bash", &json!({ "activeSessionId": SESSION }))
            .await;
        assert!(aborted.success, "failed: {aborted:?}");
        wait_bash_running(&worker, false).await;
        let rows = bash_rows(&worker).await;
        assert_eq!((rows.len(), rows[0]["cancelled"].clone()), (1, json!(true)));
    }

    /// Transient runs stay unrecorded (they live only in their pane).
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn transient_execute_bash_records_nothing() {
        let (_dir, worker) = created_worker(SESSION, json!(["ack"])).await;
        let response = worker
            .dispatch(
                "execute_bash",
                &json!({
                    "activeSessionId": SESSION,
                    "command": "echo transient",
                    "transient": true,
                }),
            )
            .await;
        assert!(response.success, "failed: {response:?}");
        wait_bash_running(&worker, false).await;
        assert_eq!(
            bash_rows(&worker).await.len(),
            0,
            "transient runs record nothing"
        );
    }

    /// A missing cwd answers the TS local-operations refusal.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn execute_bash_and_wait_refuses_a_missing_cwd() {
        let (_dir, worker) = created_worker(SESSION, json!(["ack"])).await;
        lock(&worker.core).cwd = "/nonexistent-bash-cwd".to_string();
        let response = worker
            .dispatch(
                "execute_bash_and_wait",
                &json!({ "activeSessionId": SESSION, "command": "pwd" }),
            )
            .await;
        assert!(!response.success);
        assert_eq!(
            response.error.as_deref(),
            Some(
                "Working directory does not exist: /nonexistent-bash-cwd\nCannot execute bash commands."
            )
        );
    }

    /// The kernel bash lane never boots a kernel: before any cell ran it
    /// answers the definitive refusal; a malformed request fails first. A
    /// child session (no prewarm) keeps the kernel down for the whole test.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn kernel_bash_activity_answers_not_running_before_a_kernel_boots() {
        let (_dir, worker) =
            created_worker_with(SESSION, json!(["ack"]), json!({ "rlmDepth": 1 })).await;
        let listed = worker
            .dispatch("list_kernel_bash", &json!({ "activeSessionId": SESSION }))
            .await;
        assert!(!listed.success);
        assert_eq!(listed.error.as_deref(), Some("Kernel is not running"));
        let missing = worker
            .dispatch("tail_kernel_bash", &json!({ "activeSessionId": SESSION }))
            .await;
        assert_eq!(missing.error.as_deref(), Some("activityId is required"));
        let lines = worker
            .dispatch(
                "tail_kernel_bash",
                &json!({ "activeSessionId": SESSION, "activityId": "a", "lines": 0 }),
            )
            .await;
        assert_eq!(
            lines.error.as_deref(),
            Some("lines must be between 1 and 200")
        );
    }

    /// The sanitizer matches the TS chain: ANSI escapes, control
    /// characters, and carriage returns drop; tab and newline stay.
    #[test]
    fn sanitize_output_matches_the_ts_chain() {
        assert_eq!(sanitize_output("clean\r\noutput"), "clean\noutput");
        assert_eq!(
            sanitize_output("\u{1b}[32mgreen\u{1b}[0m plain"),
            "green plain"
        );
        assert_eq!(
            sanitize_output("keep\ttab\nand\x00drop"),
            "keep\ttab\nanddrop"
        );
        assert_eq!(sanitize_output("format\u{fff9}gone"), "formatgone");
    }
}
