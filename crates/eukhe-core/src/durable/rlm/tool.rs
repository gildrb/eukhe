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

use std::path::PathBuf;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::typebox::{Options, TSchema, Type};
use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_durable::harness::define::define_tool;
use eukhe_durable::harness::types::{
    OutputRetain, ToolDiagnostic, ToolDiagnosticSeverity, ToolExecutionApi, ToolExecutionApiExt,
    ToolExecutionMode, ToolExecutionResult, ToolOutputChunk, ToolOutputLimits, ToolRegistration,
    ToolReplay,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::pi_ai::{ImageContent, JsonValue as PiJsonValue, TextContent, UserContentBlock};
use futures::FutureExt;
use serde_json::json;

use super::cell_output::CellOutput;
use super::kernels::ConversationKernel;
use super::RlmRuntime;
use crate::kernel::cancellation::AbortSignal as KernelAbortSignal;
use crate::kernel::shared::{
    ExecuteOptions, ExecuteResult, ExecuteStatus, KernelAttachment, KernelSentAgentMessage,
    LateSentAgentMessageCallback, OutputSink, StreamCallback, StreamName, KERNEL_ABORT_GRACE_MS,
    MAX_BACKGROUND_OUTPUT_CHARS,
};
use crate::kernel::state_snapshot::snapshot_path_in;
use crate::kernel::KernelBootstrapProgressHandler;
use crate::kernel::ReplKernelManager;

/// The tool name.
pub const IPYTHON_TOOL_NAME: &str = "ipython";

/// The tool description.
const IPYTHON_TOOL_DESCRIPTION: &str = "Execute Python code in a persistent Python REPL. Top-level `await` is supported. Variables, imports, and loaded data persist across calls, and are revived on a best-effort basis when a session is resumed (objects that cannot be serialized are dropped and reported). Run shell commands with `bash('cmd')` / `await bash('cmd')`. Project imports, tests, scripts, CLIs, and dependency checks should run through the target project's own environment.";

/// Mime types the model context accepts as images.
const IMAGE_MIME_TYPES: [&str; 4] = ["image/jpeg", "image/png", "image/gif", "image/webp"];

/// The directory under the session storage holding the full output of each
/// bounded call, one `<task id>.txt` file per call.
const TOOL_OUTPUT_DIR: &str = "tool-output";

/// The `code` parameter description.
const CODE_DESCRIPTION: &str = "Python code to execute in the persistent Python REPL. Use the target project's own environment for project imports, tests, scripts, CLIs, and dependency checks instead of direct kernel imports.";

/// `Type.Object({ code: Type.String({ description }) })`: the `ipython`
/// tool schema (`type`, `required: ["code"]`, `properties`).
#[must_use]
pub fn ipython_parameters() -> TSchema {
    Type::object([(
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
    // The settled text is bounded once, here (`cell_output`). The running
    // output's live copy keeps its end, so the live view and a
    // crash-interrupted call's partial result show where errors are.
    registration.output_limits = Some(ToolOutputLimits {
        retain: Some(OutputRetain::Tail),
        ..ToolOutputLimits::default()
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
    let signal = cx
        .abort_signal()
        .map(|signal| KernelAbortSignal::from_token(signal.cancellation_token()));

    let manager = match ensure_kernel(&kernel, &api, signal.clone(), cx).await {
        Ok(manager) => manager,
        Err(error) => {
            return match aborted(cx) {
                Some(abort) => Err(abort),
                None => Ok(error_result(format!("{error:#}"))),
            }
        }
    };
    deliver_boot_notices(&kernel, &api, cx).await?;

    let artifact_path = match &runtime.deps.storage_dir {
        Some(dir) => Ok(dir
            .join(TOOL_OUTPUT_DIR)
            .join(format!("{}.txt", api.task_id()))),
        None => Err("the session has no storage directory".to_owned()),
    };
    let cell_output = Arc::new(Mutex::new(CellOutput::new(artifact_path)));
    let output_failure: Arc<Mutex<Option<SessionError>>> = Arc::default();
    let on_stream: StreamCallback = {
        let api = Arc::clone(&api);
        let cell_output = Arc::clone(&cell_output);
        let failure = Arc::clone(&output_failure);
        Arc::new(move |chunk: &str, _stream: StreamName| {
            cell_output
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(chunk);
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
    let executed = manager
        .execute(
            &code,
            ExecuteOptions {
                signal,
                output: OutputSink::Forward(on_stream),
                call: Some(Arc::clone(&api)),
                on_late_sent_agent_message,
                ..ExecuteOptions::default()
            },
        )
        .await;
    let result = match executed {
        Ok(result) => result,
        Err(error) => {
            return match aborted(cx) {
                Some(abort) => Err(abort),
                None => Ok(error_result(format!("{error:#}"))),
            }
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
    let mut cell_output = Arc::try_unwrap(cell_output)
        .map_err(|_shared| SessionError::error("the cell's output is still streaming"))?
        .into_inner()
        .unwrap_or_else(PoisonError::into_inner);
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
        cell_output.push_part(&format!(
            "[background output (unattributed)]\n{}",
            background.text
        ));
        if background.dropped_chars > 0 {
            diagnostics.push(ToolDiagnostic {
                severity: ToolDiagnosticSeverity::Warn,
                code: Some("background_output_dropped".to_owned()),
                message: format!(
                    "{} characters of background output past the {MAX_BACKGROUND_OUTPUT_CHARS}-character ceiling were dropped.",
                    background.dropped_chars
                ),
                omitted: None,
                artifact: None,
            });
        }
    }
    let (text, bounded) = cell_output.finish();
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
        });
    }
    let mut settled = tool_result(&result, text);
    settled.diagnostics = (!diagnostics.is_empty()).then_some(diagnostics);
    Ok(settled)
}

/// Start (or reuse) the kernel; startup stages reach the call's details as
/// `{status: "starting", message}` (the old partial update's text and
/// `status`).
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
    loop {
        tokio::select! {
            manager = &mut ensure => return manager,
            message = progress_rx.recv(), if progress_open => match message {
                Some(message) => {
                    let details = JsonValue::from(json!({ "status": "starting", "message": message }));
                    if let Err(error) = api.details(details, cx).await {
                        tracing::debug!(%error, "ipython startup progress not published");
                    }
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
