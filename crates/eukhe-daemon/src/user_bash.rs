//! The user bash surface (protocol breadth wave b5): the worker arms for
//! `execute_bash`, `execute_bash_and_wait`, and `abort_bash` (TS
//! daemon-mode cases over `AgentSession.runUserBash` / `executeBash` /
//! `abortBash`, with `bash_start`/`bash_output`/`bash_end` session events
//! and the durable `eukhe.bash` row, rendered as `bashExecution`).
//!
//! The execution port follows the TS stack: the local bash operations
//! (shell config, cwd guard, merged stdout+stderr streaming, kill on
//! abort), the executor (ANSI/binary sanitization, the 50KB streaming
//! window with the tail kept, the 2000-line/50KB tail truncation, the
//! spill file), and the user-bash wrapper (the already-running guard, the
//! identity echoed on start/end, transient rows staying unrecorded).

use std::io::Write;
use std::process::Stdio;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::rlm::{kernel_bash_activity, BashActivityAction, BashActivityRequest};
use eukhe_core::durable::{bash_entry_draft, BashEntryData};
use eukhe_durable::harness::types::WriteSubmissionDraft;
use serde_json::{json, Value};
use tokio::io::{AsyncRead, AsyncReadExt};
use tokio::sync::Mutex;

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::{emit_worker_event_with, HostedSession, Worker};

/// Streaming window: chunks are retained (spilled to disk beyond this).
const DEFAULT_MAX_BYTES: usize = 50 * 1024;
/// Streaming retention cap: the in-memory tail (TS `maxOutputBytes`).
const STREAM_MAX_BYTES: usize = DEFAULT_MAX_BYTES * 2;
/// Tail truncation line budget (TS `DEFAULT_MAX_LINES`).
const DEFAULT_MAX_LINES: usize = 2000;
/// The TS spill prefix (temp file names in `$TMPDIR`).
const SPILL_PREFIX: &str = "pa-bash";

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
    /// The in-flight process (user bash or an awaited run): `abort_bash`
    /// kills it.
    child: Mutex<Option<tokio::process::Child>>,
}

impl UserBash {
    pub(crate) fn new() -> Self {
        Self {
            running: AtomicBool::new(false),
            awaited: AtomicUsize::new(0),
            abort_requested: AtomicBool::new(false),
            child: Mutex::new(None),
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

    /// Kill the in-flight process (TS `abortBash` aborts every
    /// controller); the settled runs report cancelled.
    pub(crate) async fn abort(&self) {
        self.abort_requested.store(true, Ordering::SeqCst);
        let mut child = self.child.lock().await;
        if let Some(child) = child.as_mut() {
            let _ = child.start_kill();
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
        if let Err(response) = self.require_created("execute_bash") {
            return response;
        }
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
        let identity = bash_identity(transient, run_id);
        let start = json!({
            "type": "bash_start",
            "command": command,
            "excludeFromContext": exclude_from_context,
        });
        let start = merge_identity(start, &identity);
        self.emit_worker_event(start);
        // The run outlives the response (bash can exceed the client's
        // request timeout); completion streams via bash_end.
        let core = Arc::clone(&self.core);
        let events = Arc::clone(&self.events);
        let session = self.session.clone();
        let user_bash = Arc::clone(&self.user_bash);
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
                on_chunk: Some((Arc::clone(&core), Arc::clone(&events))),
            })
            .await;
            // Persist the durable row (transient runs live only in their
            // pane; reloads and rebuilds cannot resurface them).
            if !transient {
                let result = BashResult {
                    output: end.output.clone(),
                    exit_code: end.exit_code,
                    cancelled: end.cancelled,
                    truncated: end.truncated,
                    full_output_path: end.full_output_path.clone(),
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
            let mut event = json!({
                "type": "bash_end",
                "exitCode": end.exit_code,
                "cancelled": end.cancelled,
                "truncated": end.truncated,
            });
            if let Some(path) = &end.full_output_path {
                event["fullOutputPath"] = json!(path);
            }
            if let Some(error) = &end.error_message {
                event["errorMessage"] = json!(error);
            }
            let event = merge_identity(event, &identity);
            emit_worker_event_with(&core, &events, event);
        });
        response_success(None, "execute_bash", None)
    }

    /// `execute_bash_and_wait { command }` (TS `executeBash` over the
    /// awaited path): run to completion, record the row, and answer the
    /// `BashResult` wire shape.
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
        let user_bash = Arc::clone(&self.user_bash);
        let command = command.to_string();
        let request_id = bash_request_id(payload.get("runId").and_then(Value::as_str));
        // The awaited run counts toward the session's `isBashRunning` (TS's
        // `executeBash` registers an abort controller, so the flag is true
        // for its whole duration); it owns no exclusive slot, so a streamed
        // user bash is not blocked by it. The bracket releases the count on
        // drop, so a dropped run future cannot leave the flag stuck on.
        let awaited = user_bash.begin_awaited();
        let end = run_bash(RunBash {
            command: &command,
            cwd: &cwd,
            prefix: prefix.as_deref(),
            shell_path: shell_path.as_deref(),
            user_bash: &user_bash,
            // The awaited path emits nothing (TS passes no `onChunk`).
            on_chunk: None,
        })
        .await;
        drop(awaited);
        // The awaited path emits no session events, so the live roster
        // feed has no trigger of its own — TS's `execute_bash_and_wait`
        // flushes in the command's `finally`; the port enqueues the same
        // flush here (the summary composes fresh, so the settled run reads
        // idle on the roster).
        self.roster_pushes.push();
        if let Some(error) = &end.error_message {
            return response_failure(None, "execute_bash_and_wait", error, None);
        }
        let result = BashResult {
            output: end.output,
            exit_code: end.exit_code,
            cancelled: end.cancelled,
            truncated: end.truncated,
            full_output_path: end.full_output_path,
        };
        let row = BashRow {
            command: &command,
            result: &result,
            exclude_from_context: false,
            request_id,
        };
        if let Err(error) = record_bash_result(&hosted, row).await {
            return response_failure(None, "execute_bash_and_wait", &format!("{error:#}"), None);
        }
        response_success(
            None,
            "execute_bash_and_wait",
            Some(serde_json::to_value(&result).unwrap_or(Value::Null)),
        )
    }

    /// `abort_bash` (TS `abortBash`): kill the in-flight command; the
    /// settled run reports cancelled. Always a success.
    pub(crate) async fn handle_abort_bash(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("abort_bash") {
            return response;
        }
        self.user_bash.abort().await;
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
fn bash_identity(transient: bool, run_id: Option<&str>) -> Value {
    let mut identity = serde_json::Map::new();
    if transient {
        identity.insert("transient".to_string(), json!(true));
    }
    if let Some(run_id) = run_id {
        identity.insert("runId".to_string(), json!(run_id));
    }
    Value::Object(identity)
}

fn merge_identity(mut event: Value, identity: &Value) -> Value {
    if let (Some(event), Some(identity)) = (event.as_object_mut(), identity.as_object()) {
        for (key, value) in identity {
            event.insert(key.clone(), value.clone());
        }
    }
    event
}

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

/// The TS `BashResult` wire shape.
#[derive(Debug, Clone, serde::Serialize)]
#[serde(rename_all = "camelCase")]
struct BashResult {
    output: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    exit_code: Option<i64>,
    cancelled: bool,
    truncated: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    full_output_path: Option<String>,
}

/// The settled user-bash run (TS `UserBashEndDetails` plus the output it
/// carries for the durable row).
struct BashEnd {
    output: String,
    exit_code: Option<i64>,
    cancelled: bool,
    truncated: bool,
    full_output_path: Option<String>,
    error_message: Option<String>,
}

/// One process run (TS `executeBashWithOperations` over the local bash
/// operations): the streaming window, the spill, and the tail truncation.
struct RunBash<'a> {
    command: &'a str,
    cwd: &'a str,
    prefix: Option<&'a str>,
    shell_path: Option<&'a str>,
    user_bash: &'a UserBash,
    /// The streaming emit target for each sanitized chunk (the
    /// executor's `onChunk`; `None` on the awaited path, which emits
    /// nothing).
    on_chunk: Option<(
        Arc<std::sync::Mutex<crate::worker::SessionCore>>,
        Arc<crate::worker::EventPump>,
    )>,
}

/// The streaming accumulator (TS `onData`): the sanitizing decode, the
/// spill, the in-memory tail window, and the chunk callback.
struct OutputStream {
    chunks: Vec<String>,
    retained_bytes: usize,
    total_bytes: usize,
    spill: OutputSpill,
    on_chunk: Option<(
        Arc<std::sync::Mutex<crate::worker::SessionCore>>,
        Arc<crate::worker::EventPump>,
    )>,
}

impl Clone for OutputStream {
    fn clone(&self) -> Self {
        Self {
            chunks: self.chunks.clone(),
            retained_bytes: self.retained_bytes,
            total_bytes: self.total_bytes,
            spill: OutputSpill::new(),
            on_chunk: self.on_chunk.clone(),
        }
    }
}

impl OutputStream {
    /// The collected view (the shared clone path): this port never clones
    /// mid-run, but the fallback keeps the collected chunks.
    fn clone_stream(&self) -> Self {
        self.clone()
    }

    fn push(&mut self, data: &[u8]) {
        let text = sanitize_output(&String::from_utf8_lossy(data));
        if text.is_empty() {
            return;
        }
        self.total_bytes += text.len();
        if self.total_bytes > DEFAULT_MAX_BYTES {
            self.spill.open(&self.chunks);
        }
        self.spill.write(&text);
        self.chunks.push(text.clone());
        self.retained_bytes += self.chunks.last().map(String::len).unwrap_or_default();
        // The in-memory window keeps the tail (TS `maxOutputBytes`).
        while self.retained_bytes > STREAM_MAX_BYTES && self.chunks.len() > 1 {
            let removed = self.chunks.remove(0);
            self.retained_bytes -= removed.len();
        }
        if let Some((core, events)) = &self.on_chunk {
            emit_worker_event_with(
                core,
                events,
                json!({ "type": "bash_output", "chunk": text }),
            );
        }
    }
}

async fn run_bash(run: RunBash<'_>) -> BashEnd {
    let resolved = match run.prefix.filter(|prefix| !prefix.is_empty()) {
        Some(prefix) => format!("{prefix}\n{}", run.command),
        None => run.command.to_string(),
    };
    let spawn_failure = |message: String| BashEnd {
        output: String::new(),
        exit_code: None,
        cancelled: false,
        truncated: false,
        full_output_path: None,
        error_message: Some(message),
    };
    if !std::path::Path::new(run.cwd).exists() {
        // TS local operations reject before spawning.
        return spawn_failure(format!(
            "Working directory does not exist: {}\nCannot execute bash commands.",
            run.cwd
        ));
    }
    let shell = match eukhe_core::platform::shell::get_shell_config(run.shell_path) {
        Ok(shell) => shell,
        Err(error) => return spawn_failure(error.to_string()),
    };
    let mut command = tokio::process::Command::new(&shell.shell);
    command
        .args(&shell.args)
        .arg(&resolved)
        .current_dir(run.cwd)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = match command.spawn() {
        Ok(child) => child,
        Err(error) => return spawn_failure(error.to_string()),
    };
    let stdout = child.stdout.take();
    let stderr = child.stderr.take();
    {
        let mut slot = run.user_bash.child.lock().await;
        // A late abort that arrived before the process spawned kills it
        // immediately (TS honors `_userBashAbortRequested` before
        // executing); the flag still settles the run cancelled.
        if run.user_bash.abort_requested.load(Ordering::SeqCst) {
            let _ = child.start_kill();
        }
        *slot = Some(child);
    }
    let stream = std::sync::Arc::new(std::sync::Mutex::new(OutputStream {
        chunks: Vec::new(),
        retained_bytes: 0,
        total_bytes: 0,
        spill: OutputSpill::new(),
        on_chunk: run.on_chunk,
    }));
    // stdout and stderr merge into one stream (TS wires both pipes to the
    // same `onData`); order between them is arrival order. The shared
    // accumulator keeps the merged order the interleaved reads produce.
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
    match (stdout_pump, stderr_pump) {
        (Some(stdout_pump), Some(stderr_pump)) => {
            futures::future::join(stdout_pump, stderr_pump).await;
        }
        (Some(pump), None) | (None, Some(pump)) => pump.await,
        (None, None) => {}
    }
    // Take the child back for the exit status (abort_bash may have killed
    // it meanwhile; a signal death reports no exit code).
    let mut child = {
        let mut slot = run.user_bash.child.lock().await;
        slot.take()
    };
    let exit_code = match child.as_mut() {
        Some(child) => child
            .wait()
            .await
            .ok()
            .and_then(|status| status.code())
            .map(i64::from),
        None => None,
    };
    let cancelled = run.user_bash.abort_requested.load(Ordering::SeqCst);
    // The reader tasks joined, so this is the last reference; a poisoned
    // lock (a reader panicked) keeps whatever it collected.
    let mut stream = match Arc::try_unwrap(stream) {
        Ok(mutex) => mutex
            .into_inner()
            .unwrap_or_else(std::sync::PoisonError::into_inner),
        Err(stream) => stream
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone_stream(),
    };
    let full_output = stream.chunks.join("");
    let (output, truncated) = truncate_tail(&full_output);
    // A line-truncated run spills at settle even under the byte budget
    // (TS bash-executor: `if (truncationResult.truncated)
    // spill.open(outputChunks)`), so the truncation notice can always
    // name a full-output file.
    if truncated {
        stream.spill.open(&stream.chunks);
    }
    let full_output_path = stream.spill.finalize();
    BashEnd {
        output,
        exit_code: if cancelled { None } else { exit_code },
        cancelled,
        truncated,
        full_output_path,
        error_message: None,
    }
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
        truncated: row.result.truncated,
        full_output_path: row.result.full_output_path.clone(),
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

/// The output spill (TS `OutputSpill`): opened once when the output
/// outgrows the streaming window, written progressively, finalized to the
/// complete file's path. A degraded spill never advertises a path.
struct OutputSpill {
    file: Option<std::fs::File>,
    path: Option<String>,
    failed: bool,
}

impl OutputSpill {
    fn new() -> Self {
        Self {
            file: None,
            path: None,
            failed: false,
        }
    }

    fn open(&mut self, replay: &[String]) {
        if self.file.is_some() || self.failed {
            return;
        }
        let path = std::env::temp_dir().join(format!(
            "{SPILL_PREFIX}-{}.log",
            uuid::Uuid::new_v4().simple()
        ));
        let Ok(mut file) = std::fs::File::create(&path) else {
            self.failed = true;
            return;
        };
        for chunk in replay {
            if file.write_all(chunk.as_bytes()).is_err() {
                self.failed = true;
                return;
            }
        }
        self.path = Some(path.to_string_lossy().to_string());
        self.file = Some(file);
    }

    fn write(&mut self, text: &str) {
        let Some(file) = self.file.as_mut() else {
            return;
        };
        if file.write_all(text.as_bytes()).is_err() {
            self.failed = true;
            self.file = None;
            self.path = None;
        }
    }

    fn finalize(mut self) -> Option<String> {
        if let Some(file) = self.file.as_mut() {
            if file.flush().is_err() {
                self.failed = true;
            }
        }
        self.file = None;
        if self.failed {
            None
        } else {
            self.path
        }
    }
}

/// Tail truncation (TS `truncateTail`): the last 2000 lines within 50KB
/// win; an oversized last line keeps its tail, blank trailing lines
/// permitting.
fn truncate_tail(content: &str) -> (String, bool) {
    let total_bytes = content.len();
    let lines: Vec<&str> = content.split('\n').collect();
    let total_lines = lines.len();
    if total_lines <= DEFAULT_MAX_LINES && total_bytes <= DEFAULT_MAX_BYTES {
        return (content.to_string(), false);
    }
    let mut collected: Vec<&str> = Vec::new();
    let mut output_bytes = 0usize;
    for line in lines.iter().rev() {
        if collected.len() >= DEFAULT_MAX_LINES {
            break;
        }
        let line_bytes = line.len() + usize::from(!collected.is_empty());
        if output_bytes + line_bytes > DEFAULT_MAX_BYTES {
            // The oversized-line rescue: trailing blanks must not defeat
            // the rescue, so keep as many as the budget allows and unshift
            // the line's own tail (TS keeps the last `maxBytes` bytes).
            if collected.iter().all(|collected| collected.is_empty()) {
                let kept_blanks = collected.len().min(DEFAULT_MAX_BYTES.saturating_sub(1));
                let budget = DEFAULT_MAX_BYTES.saturating_sub(kept_blanks);
                let truncated_line = truncate_string_to_bytes_from_end(line, budget);
                let mut out = String::with_capacity(DEFAULT_MAX_BYTES);
                out.push_str(&truncated_line);
                for _ in 0..kept_blanks {
                    out.push('\n');
                }
                return (out, true);
            }
            break;
        }
        collected.push(line);
        output_bytes += line_bytes;
    }
    collected.reverse();
    (collected.join("\n"), true)
}

/// The tail `maxBytes` of one string, on char boundaries (TS
/// `truncateStringToBytesFromEnd`).
fn truncate_string_to_bytes_from_end(text: &str, max_bytes: usize) -> String {
    let mut end = text.len().min(max_bytes);
    while end > 0 && !text.is_char_boundary(end) {
        end -= 1;
    }
    text[text.len() - end..].to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::durable_test_support::{created_worker, worker_rows};
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
            json!({ "output": "hello\n", "exitCode": 0, "cancelled": false, "truncated": false })
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
    /// answers the definitive refusal; a malformed request fails first.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn kernel_bash_activity_answers_not_running_before_a_kernel_boots() {
        let (_dir, worker) = created_worker(SESSION, json!(["ack"])).await;
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

    /// Tail truncation keeps the last lines within the byte budget, and
    /// the oversized-line rescue keeps the line's own tail.
    #[test]
    fn truncate_tail_keeps_the_tail_budget() {
        let (content, truncated) = truncate_tail("one\ntwo\nthree\n");
        assert!(!truncated);
        assert_eq!(content, "one\ntwo\nthree\n");

        // A long output keeps only its tail (the TS window).
        let big = "x".repeat(DEFAULT_MAX_BYTES + 10_000);
        let (kept, truncated) = truncate_tail(&big);
        assert!(truncated);
        assert!(kept.len() <= DEFAULT_MAX_BYTES);
        assert!(big.ends_with(&kept), "the tail wins");
    }
}
