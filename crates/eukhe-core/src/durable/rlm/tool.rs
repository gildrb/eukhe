//! The `ipython` tool on the durable Harness: the conversation's kernel runs
//! the cell, its output streams into the call's durable output, and the
//! result content/details are the `ipython` tool result.
//!
//! The call is not replay-safe: a cell interrupted by a crash is answered
//! by the Harness with an `interrupted` result carrying the output
//! committed so far; the next boot of the conversation's kernel revives its
//! last namespace snapshot and tells the model (`ipython_state_restored`).
//! An abort the cell ignores past the grace kills the kernel: the call
//! settles `killed` with the output so far and a `kernel_killed`
//! diagnostic naming what was lost, and the next call revives the same way.
//!
//! The runtime's blocking budget bounds the call (ADR 0010): a cell still
//! running when it expires keeps running as a job, the call settles
//! `detached` with the output so far, and the cell's end settles the job
//! ([`super::jobs`]). A later call waits for the job within its own budget,
//! then settles `busy` without running its code.

use std::fmt::Write as _;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, OnceLock, PoisonError};
use std::time::Duration;

use eukhe_ai::typebox::{Options, TSchema, Type};
use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_durable::harness::define::define_tool;
use eukhe_durable::harness::types::{
    OmittedAt, OmittedOutput, OutputRetain, ToolDiagnostic, ToolDiagnosticSeverity,
    ToolExecutionApi, ToolExecutionApiExt, ToolExecutionMode, ToolExecutionResult, ToolOutputChunk,
    ToolRegistration, ToolReplay,
};
use eukhe_durable::harness::{OutputLimits, Truncation};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::job::{CellStatus, JobId, JobSettled};
use eukhe_types::output::describe_bound;
use eukhe_types::pi_ai::{ImageContent, JsonValue as PiJsonValue, TextContent, UserContentBlock};
use futures::FutureExt;
use serde_json::json;

use super::jobs::CellJobEntry;
use super::kernels::ConversationKernel;
use super::RlmRuntime;
use crate::durable::bounded_output::BoundedOutput;
use crate::durable::jobs::{self, Job, JobEvent, JobKind, JobSpec, Wait};
use crate::kernel::cancellation::AbortSignal as KernelAbortSignal;
use crate::kernel::shared::{
    CellJob, ExecuteOptions, ExecuteResult, ExecuteStatus, KernelAttachment,
    KernelSentAgentMessage, LateSentAgentMessageCallback, OutputSink, StreamCallback, StreamName,
    KERNEL_ABORT_GRACE_MS,
};
use crate::kernel::state_snapshot::snapshot_path_in;
use crate::kernel::KernelBootstrapProgressHandler;
use crate::kernel::ReplKernelManager;

/// The tool name.
pub const IPYTHON_TOOL_NAME: &str = "ipython";

/// The tool description.
const IPYTHON_TOOL_DESCRIPTION: &str = "Execute Python code in a persistent Python REPL. Top-level `await` is supported. Variables, imports, and loaded data persist across calls, and are revived on a best-effort basis when a session is resumed (objects that cannot be serialized are dropped and reported). Run shell commands with `bash('cmd')` / `await bash('cmd')`. Project imports, tests, scripts, CLIs, and dependency checks should run through the target project's own environment. A cell that outlives the runtime's blocking budget keeps running as a job: the call returns its output so far, and the job's end arrives later as a `[job-settled ...]` message.";

/// Mime types the model context accepts as images.
const IMAGE_MIME_TYPES: [&str; 4] = ["image/jpeg", "image/png", "image/gif", "image/webp"];

/// The `code` parameter description.
const CODE_DESCRIPTION: &str = "Python code to execute in the persistent Python REPL. Use the target project's own environment for project imports, tests, scripts, CLIs, and dependency checks instead of direct kernel imports.";

/// The durable identity of the tool's contract.
const IPYTHON_VERSION: &str = "ipython@1";

/// The `ipython` tool schema: the shared `i`, then `code`.
#[must_use]
pub fn ipython_parameters() -> TSchema {
    crate::durable::tool_contract::parameters([(
        "code",
        Type::string_with(Options::new().set("description", CODE_DESCRIPTION)),
    )])
}

/// The `ipython` registration: sequential (the kernel is single-threaded),
/// never replayed after a crash (a cell may have partially run).
pub(crate) fn ipython_tool(runtime: &Arc<RlmRuntime>) -> Arc<ToolRegistration> {
    let runtime = Arc::clone(runtime);
    let mut registration = ToolRegistration::new(
        IPYTHON_TOOL_NAME,
        IPYTHON_TOOL_DESCRIPTION,
        ipython_parameters(),
        move |args: PiJsonValue, api: Arc<dyn ToolExecutionApi>, cx: Context| {
            let runtime = Arc::clone(&runtime);
            async move { execute(&runtime, &args, api, &cx).await }
        },
    );
    registration.execution_mode = Some(ToolExecutionMode::Sequential);
    // The settled text is bounded once, here (`bounded_output`), to the
    // call's truncation. The running output's live copy keeps its end, so
    // the live view shows where errors are.
    registration.truncation = Truncation::On(OutputLimits {
        retain: OutputRetain::Tail,
        ..OutputLimits::default()
    });
    registration.replay = Some(ToolReplay::Unsafe);
    define_tool(registration)
}

fn session_error(error: &anyhow::Error) -> SessionError {
    SessionError::error(format!("{error:#}"))
}

/// The call's abort as the error the Harness treats as an abort.
fn aborted(cx: &Context) -> Option<SessionError> {
    cx.abort_signal()
        .and_then(|signal| signal.reason())
        .map(SessionError::Aborted)
}

/// A model-facing error result (the old agent loop's `AgentToolResult::error`).
fn error_result(message: String) -> ToolExecutionResult {
    ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(message))]),
        is_error: Some(true),
        ..ToolExecutionResult::default()
    }
}

/// Resolves when the call aborts; never for a call without an abort signal.
async fn call_aborted(cx: &Context) {
    match cx.abort_signal() {
        Some(signal) => {
            signal.cancelled().await;
        }
        None => std::future::pending().await,
    }
}

#[tracing::instrument(skip_all, fields(call = api.call_id()))]
async fn execute(
    runtime: &RlmRuntime,
    args: &PiJsonValue,
    api: Arc<dyn ToolExecutionApi>,
    cx: &Context,
) -> SessionResult<ToolExecutionResult> {
    let code = args
        .get("code")
        .and_then(PiJsonValue::as_str)
        .ok_or_else(|| SessionError::error("ipython tool requires a code string"))?
        .to_owned();
    // The runtime's one blocking budget bounds this call's waits on the
    // kernel (ADR 0010), each the one blocking wait on a job
    // ([`jobs::wait_until`]): on a detached cell still holding it, then on
    // this cell. Booting the kernel is the provisioner's, bounded by its own
    // startup deadlines, so its time extends the deadline.
    let budget = runtime.deps.blocking_budget();
    let mut deadline = tokio::time::Instant::now() + budget;
    let conversation_id = api.conversation_id();
    let cwd = api
        .agent(cx)
        .await?
        .cwd
        .clone()
        .map_or_else(|| runtime.deps.cwd.clone(), PathBuf::from);
    let kernel = runtime
        .kernels
        .kernel(conversation_id, cwd)
        .map_err(|error| session_error(&error))?;

    // A detached cell still holds the kernel: wait for it within the budget,
    // then report it instead of queueing this cell behind it.
    if let Some(running) = kernel.jobs.running() {
        let waited = tokio::select! {
            waited = jobs::wait_until(deadline, running.job.ended()) => waited,
            () = call_aborted(cx) => {
                return Err(aborted(cx).unwrap_or_else(|| SessionError::error("aborted")));
            }
        };
        match waited {
            Wait::Detached => return Ok(busy_result(&running)),
            Wait::Settled(_) => {}
        }
    }

    let signal = cx
        .abort_signal()
        .map(|signal| KernelAbortSignal::from_token(signal.cancellation_token()));
    let boot_started = tokio::time::Instant::now();
    let manager = match ensure_kernel(&kernel, &api, signal, cx).await {
        Ok(manager) => manager,
        Err(error) => {
            return match aborted(cx) {
                Some(abort) => Err(abort),
                None => Ok(error_result(format!("{error:#}"))),
            }
        }
    };
    deliver_boot_notices(&kernel, &api, cx).await?;
    deadline += boot_started.elapsed();

    let job_id = JobId::new(format!("cell-{}", uuid::Uuid::new_v4().simple()))
        .map_err(|error| SessionError::error(error.to_string()))?;
    let job = CellJob::new(job_id);
    // The cell's own stop: the call's abort while it blocks the turn, a
    // `jobs.cancel` once it detached.
    let job_signal = KernelAbortSignal::new();
    let cell_output = Arc::new(Mutex::new(BoundedOutput::in_session(
        runtime.deps.storage_dir.as_deref(),
        &api.task_id().to_string(),
        api.truncation(),
    )));
    let output_failure: Arc<Mutex<Option<SessionError>>> = Arc::default();
    // The session job of this cell, once its call detached.
    let detached_job: Arc<OnceLock<Job>> = Arc::default();
    let on_stream: StreamCallback = {
        let api = Arc::clone(&api);
        let cell_output = Arc::clone(&cell_output);
        let failure = Arc::clone(&output_failure);
        let job = job.clone();
        let detached_job = Arc::clone(&detached_job);
        Arc::new(move |chunk: &str, _stream: StreamName| {
            // Read under the lock the cell detaches under: every byte
            // counts once, in the job's start or here.
            let detached = {
                let mut output = cell_output.lock().unwrap_or_else(PoisonError::into_inner);
                output.push(chunk);
                job.is_detached().then(|| detached_job.get().cloned())
            };
            // A detached cell's call has settled; its output goes to the job.
            match detached {
                Some(Some(detached)) => {
                    detached.record(JobEvent::Output(chunk.len() as u64));
                    return;
                }
                Some(None) => return,
                None => {}
            }
            if let Err(error) = api.output(ToolOutputChunk::Text(chunk), None) {
                failure
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .get_or_insert(error);
            }
        })
    };
    // An agent message the kernel reports after this cell settled reaches
    // the embedding's sink with this call's id (TS
    // `onLateSentAgentMessage`).
    let on_late_sent_agent_message = runtime.deps.late_agent_message.as_ref().map(|sink| {
        let sink = Arc::clone(sink);
        let call_id = api.call_id().to_owned();
        Arc::new(move |message| sink(&call_id, message)) as LateSentAgentMessageCallback
    });
    let mut execution = {
        let manager = manager.clone();
        let opts = ExecuteOptions {
            signal: Some(job_signal.clone()),
            output: OutputSink::Forward(on_stream),
            call: Some(Arc::clone(&api)),
            on_late_sent_agent_message,
            job: Some(job.clone()),
            ..ExecuteOptions::default()
        };
        tokio::spawn(async move { manager.execute(&code, opts).await })
    };
    let waited = tokio::select! {
        waited = jobs::wait_until(deadline, &mut execution) => waited,
        // The abort stops the cell (interrupt, then the kill after the
        // grace); the call settles when the cell does.
        () = call_aborted(cx) => {
            job_signal.abort();
            Wait::Settled((&mut execution).await)
        }
    };
    let executed = match waited {
        Wait::Settled(joined) => joined,
        Wait::Detached => {
            // Under the output lock: a chunk counts in the job's start or,
            // once the cell detached, on the job.
            let (cell_job, partial, bounded) = {
                let mut cell_output = cell_output.lock().unwrap_or_else(PoisonError::into_inner);
                let cell_job = runtime.deps.jobs.start(JobSpec {
                    id: job.id().clone(),
                    kind: JobKind::Cell,
                    label: IPYTHON_TOOL_NAME.to_owned(),
                    truncation: api.truncation(),
                    written: cell_output.bytes(),
                    kill: {
                        let signal = job_signal.clone();
                        Box::new(move |_| signal.abort())
                    },
                });
                let _ = detached_job.set(cell_job.clone());
                job.detach();
                let (partial, bounded) = cell_output.projection();
                (cell_job, partial, bounded)
            };
            let settle = kernel.jobs.start(cell_job);
            let detached = detached_result(job.id(), budget, partial, bounded);
            let sink = runtime.deps.job_settled.clone();
            let job_id = job.id().clone();
            tokio::spawn(async move {
                let joined = execution.await;
                let (status, output) = {
                    let mut cell_output =
                        cell_output.lock().unwrap_or_else(PoisonError::into_inner);
                    settle_detached(joined, &mut cell_output, &kernel)
                };
                tracing::debug!(job = %job_id, status = status.label(), "detached cell settled");
                settle.settle(status, output.clone());
                if let Some(sink) = sink {
                    sink(JobSettled::Cell {
                        job: job_id,
                        status,
                        output,
                    });
                }
            });
            return Ok(detached);
        }
    };
    let result = match executed {
        Ok(Ok(result)) => result,
        Ok(Err(error)) => {
            return match aborted(cx) {
                Some(abort) => Err(abort),
                None => Ok(error_result(format!("{error:#}"))),
            }
        }
        Err(error) => {
            return Err(SessionError::error(format!(
                "the cell's task failed: {error}"
            )))
        }
    };
    if let Some(error) = output_failure
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
    {
        if let Some(abort) = aborted(cx) {
            return Err(abort);
        }
        return Err(error);
    }
    let (text, diagnostics) = settled_projection(
        &result,
        &mut cell_output.lock().unwrap_or_else(PoisonError::into_inner),
        &kernel,
    );
    let mut settled = tool_result(&result, text);
    settled.diagnostics = (!diagnostics.is_empty()).then_some(diagnostics);
    Ok(settled)
}

/// The settled cell's whole projection: the streamed output, then its
/// result value, traceback, and background output, bounded once, with the
/// diagnostics naming what the bound and a kill dropped.
fn settled_projection(
    result: &ExecuteResult,
    cell_output: &mut BoundedOutput,
    kernel: &ConversationKernel,
) -> (String, Vec<ToolDiagnostic>) {
    let mut diagnostics = Vec::new();
    if let Some(value) = &result.result {
        cell_output.push_part(value);
    }
    if result.status == ExecuteStatus::Error {
        if let Some(error) = &result.error {
            cell_output.push_part(&error.traceback.join("\n"));
        }
    }
    if let Some(background) = &result.background_output {
        let lines = (!background.text.is_empty()).then(|| cell_output.push_part(&background.text));
        let omitted = (background.dropped_bytes > 0).then_some(OmittedOutput {
            bytes: background.dropped_bytes as u64,
            lines: background.dropped_newlines as u64,
            at: OmittedAt::End,
        });
        diagnostics.push(ToolDiagnostic {
            severity: if omitted.is_some() {
                ToolDiagnosticSeverity::Warn
            } else {
                ToolDiagnosticSeverity::Info
            },
            code: Some("background_output".to_owned()),
            message: "Output from background work, not from this cell.".to_owned(),
            omitted,
            artifact: None,
            lines,
        });
    }
    let (text, bounded) = cell_output.projection();
    diagnostics.extend(bounded);
    if result.status == ExecuteStatus::Killed {
        let snapshot_exists = kernel
            .snapshot_dir
            .as_deref()
            .is_some_and(|dir| snapshot_path_in(dir).exists());
        let revival = if snapshot_exists {
            "The next cell starts a new kernel that revives the last namespace snapshot and lists the names it restored."
        } else {
            "No namespace snapshot exists, so the next cell starts a new kernel with an empty namespace."
        };
        diagnostics.push(ToolDiagnostic {
            severity: ToolDiagnosticSeverity::Warn,
            code: Some("kernel_killed".to_owned()),
            message: format!(
                "The cell ignored the interrupt for {KERNEL_ABORT_GRACE_MS} ms, so the Python kernel was killed. \
                 The cell's effects are unknown: it may have partially run. \
                 Lost with the kernel: namespace changes made after the last snapshot, threads, asyncio tasks, \
                 background bash() processes, and open files and connections. {revival}"
            ),
            omitted: None,
            artifact: None,
            lines: None,
        });
    }
    (text, diagnostics)
}

/// A detached cell's end as its job's status and model-facing output: the
/// same projection a foreground call settles with, its diagnostics rendered
/// after it.
fn settle_detached(
    joined: Result<anyhow::Result<ExecuteResult>, tokio::task::JoinError>,
    cell_output: &mut BoundedOutput,
    kernel: &ConversationKernel,
) -> (CellStatus, String) {
    let failure = match joined {
        Ok(Ok(result)) => {
            let (text, diagnostics) = settled_projection(&result, cell_output, kernel);
            let status = match result.status {
                ExecuteStatus::Ok => CellStatus::Ok,
                ExecuteStatus::Error => CellStatus::Error,
                ExecuteStatus::Aborted => CellStatus::Aborted,
                ExecuteStatus::Killed => CellStatus::Killed,
            };
            return (status, with_diagnostics(text, &diagnostics));
        }
        Ok(Err(error)) => format!("{error:#}"),
        Err(error) => format!("the cell's task failed: {error}"),
    };
    cell_output.push_part(&failure);
    let (text, bounded) = cell_output.projection();
    (
        CellStatus::Error,
        with_diagnostics(text, bounded.as_slice()),
    )
}

/// `text`, then one line per diagnostic (its message and what it bounded).
fn with_diagnostics(mut text: String, diagnostics: &[ToolDiagnostic]) -> String {
    for diagnostic in diagnostics {
        let severity = match diagnostic.severity {
            ToolDiagnosticSeverity::Info => "info",
            ToolDiagnosticSeverity::Warn => "warn",
            ToolDiagnosticSeverity::Error => "error",
        };
        let bound = describe_bound(diagnostic.omitted.as_ref(), diagnostic.artifact.as_deref());
        let _infallible = write!(text, "\n[{severity}] {} {bound}", diagnostic.message);
    }
    text
}

/// The call of a cell that outlived the blocking budget: the output so
/// far, and the job its cell became.
fn detached_result(
    job: &JobId,
    budget: Duration,
    partial: String,
    bounded: Option<ToolDiagnostic>,
) -> ToolExecutionResult {
    let budget_ms = budget.as_millis();
    let mut diagnostics: Vec<ToolDiagnostic> = bounded.into_iter().collect();
    diagnostics.push(ToolDiagnostic {
        severity: ToolDiagnosticSeverity::Info,
        code: Some("detached".to_owned()),
        message: format!(
            "The cell outlived the {budget_ms} ms blocking budget, so this call settled as job {job}; \
             the cell keeps running. Its end reaches this session as a [job-settled job:{job}] message \
             with its output, waking the session if idle. Until then the kernel is busy: an ipython call \
             waits for the job up to the budget, then reports it still running."
        ),
        omitted: None,
        artifact: None,
        lines: None,
    });
    ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(partial))]),
        is_error: Some(false),
        details: Some(JsonValue::from(json!({
            "status": "detached",
            "job": { "id": job.as_str(), "kind": "cell" },
            "kernelRestarted": false,
            "durationMs": u64::try_from(budget_ms).unwrap_or(u64::MAX),
        }))),
        diagnostics: Some(diagnostics),
        ..ToolExecutionResult::default()
    }
}

/// A call that found the kernel still held by a detached cell past the
/// budget: its code did not run.
fn busy_result(running: &CellJobEntry) -> ToolExecutionResult {
    let job = running.job.id();
    let elapsed_ms = running.job.elapsed().as_millis();
    ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(format!(
            "Not run: the kernel is still running job {job} (started {elapsed_ms} ms ago). \
             Its end reaches this session as a [job-settled job:{job}] message with its output."
        )))]),
        is_error: Some(true),
        details: Some(JsonValue::from(json!({
            "status": "busy",
            "job": { "id": job.as_str(), "kind": "cell" },
            "kernelRestarted": false,
        }))),
        ..ToolExecutionResult::default()
    }
}

/// Start (or reuse) the kernel; startup stages reach the call's details as
/// `{status: "starting", message}` (the old partial update's text and
/// `status`). Once the kernel is up, a call that showed a stage moves its
/// details to `{status: "running"}`, so live clients show the cell's output
/// instead of the last stage.
async fn ensure_kernel(
    kernel: &ConversationKernel,
    api: &Arc<dyn ToolExecutionApi>,
    signal: Option<KernelAbortSignal>,
    cx: &Context,
) -> anyhow::Result<ReplKernelManager> {
    let (progress_tx, mut progress_rx) = tokio::sync::mpsc::unbounded_channel::<String>();
    let on_progress: KernelBootstrapProgressHandler = Arc::new(move |message: &str| {
        // The receiver lives until the startup settles; a stage reported
        // after that has nobody to show it to.
        let _unobserved = progress_tx.send(message.to_owned());
    });
    let ensure = kernel.provisioner.ensure(Some(on_progress), signal).fuse();
    futures::pin_mut!(ensure);
    let mut progress_open = true;
    let mut showed_stage = false;
    loop {
        tokio::select! {
            manager = &mut ensure => {
                if showed_stage && manager.is_ok() {
                    let details = JsonValue::from(json!({ "status": "running" }));
                    if let Err(error) = api.details(details, cx).await {
                        tracing::debug!(%error, "ipython running status not published");
                    }
                }
                return manager;
            }
            message = progress_rx.recv(), if progress_open => match message {
                Some(message) => {
                    let details = JsonValue::from(json!({ "status": "starting", "message": message }));
                    if let Err(error) = api.details(details, cx).await {
                        tracing::debug!(%error, "ipython startup progress not published");
                    }
                    showed_stage = true;
                }
                None => progress_open = false,
            },
        }
    }
}

/// Commit the notices the kernel boot owes the model (a revived snapshot,
/// failed skill imports) into the conversation, in this call's commit.
async fn deliver_boot_notices(
    kernel: &ConversationKernel,
    api: &Arc<dyn ToolExecutionApi>,
    cx: &Context,
) -> SessionResult<()> {
    let notices = kernel.take_notices();
    if notices.is_empty() {
        return Ok(());
    }
    let conversation_id = api.conversation_id();
    let drafts = notices
        .iter()
        .map(super::CustomNotice::draft)
        .collect::<Result<Vec<_>, _>>()?;
    api.commit(
        move |tx| async move {
            for draft in drafts {
                tx.append_entry(conversation_id, draft).await?;
            }
            Ok(())
        },
        cx,
    )
    .await
}

fn image_block(attachment: &KernelAttachment) -> Option<UserContentBlock> {
    IMAGE_MIME_TYPES
        .contains(&attachment.mime_type.as_str())
        .then(|| {
            UserContentBlock::Image(ImageContent {
                data: attachment.data.clone(),
                mime_type: attachment.mime_type.clone(),
            })
        })
}

fn status_name(status: ExecuteStatus) -> &'static str {
    match status {
        ExecuteStatus::Ok => "ok",
        ExecuteStatus::Error => "error",
        ExecuteStatus::Aborted => "aborted",
        ExecuteStatus::Killed => "killed",
    }
}

/// The `ipython` tool result: the bounded text plus image attachments, and
/// the TUI card details (status, timing, bash summary, error name, sent
/// messages; never a copy of the text). The busy-kernel restart choice
/// needs a UI the durable host does not have, so `kernelRestarted` is always
/// `false` (as in every headless session).
pub(crate) fn tool_result(result: &ExecuteResult, text: String) -> ToolExecutionResult {
    let mut content = vec![UserContentBlock::Text(TextContent::new(text))];
    content.extend(result.attachments.iter().flatten().filter_map(image_block));
    let mut details = json!({
        "version": IPYTHON_VERSION,
        "status": status_name(result.status),
        "kernelRestarted": false,
    });
    details["durationMs"] = json!(result.duration_ms);
    if let Some(bash) = &result.bash_commands {
        details["bashCommands"] = json!({
            "first": bash.first,
            "count": bash.count,
            "lines": bash.lines,
        });
    }
    if let Some(error) = &result.error {
        details["error"] = json!({
            "ename": error.ename,
            "evalue": error.evalue,
        });
        details["errorEname"] = json!(error.ename);
    }
    if let Some(sent) = result
        .sent_agent_messages
        .as_ref()
        .filter(|sent| !sent.is_empty())
    {
        details["sentAgentMessages"] = json!(sent
            .iter()
            .map(KernelSentAgentMessage::to_json)
            .collect::<Vec<_>>());
    }
    ToolExecutionResult {
        output: Some(content),
        is_error: Some(matches!(
            result.status,
            ExecuteStatus::Error | ExecuteStatus::Aborted | ExecuteStatus::Killed
        )),
        details: Some(JsonValue::from(details)),
        ..ToolExecutionResult::default()
    }
}
