//! The `ipython` tool on the durable Harness: the conversation's kernel runs
//! the cell, its output streams into the call's durable output, and the
//! result content/details are the old engine's `ipython` tool result
//! (`crate::tools::ipython::execute_ipython`).
//!
//! The call is not replay-safe: a cell interrupted by a crash is answered
//! by the Harness with an `interrupted` result carrying the output
//! committed so far; the next boot of the conversation's kernel revives its
//! last namespace snapshot and tells the model (`ipython_state_restored`).

use std::fmt::Write as _;
use std::path::PathBuf;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_durable::harness::define::define_tool;
use eukhe_durable::harness::types::{
    ToolExecutionApi, ToolExecutionApiExt, ToolExecutionMode, ToolExecutionResult, ToolOutputChunk,
    ToolRegistration, ToolReplay,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_pi_ai::typebox::{Options, TSchema, Type};
use eukhe_types::pi_ai::{ImageContent, JsonValue as PiJsonValue, TextContent, UserContentBlock};
use futures::FutureExt;
use serde_json::json;

use super::kernels::ConversationKernel;
use super::RlmRuntime;
use crate::kernel::cancellation::AbortSignal as KernelAbortSignal;
use crate::kernel::shared::{
    ExecuteOptions, ExecuteResult, ExecuteStatus, KernelAttachment, LateSentAgentMessageCallback,
    StreamCallback, StreamName,
};
use crate::kernel::KernelBootstrapProgressHandler;
use crate::kernel::ReplKernelManager;
use crate::tools::ipython::{ipython_tool_description, sent_agent_message_json, IMAGE_MIME_TYPES};

/// The tool name.
pub const IPYTHON_TOOL_NAME: &str = "ipython";

/// The `code` parameter description (the old `ipython_tool_schema`).
const CODE_DESCRIPTION: &str = "Python code to execute in the persistent Python REPL. Use the target project's own environment for project imports, tests, scripts, CLIs, and dependency checks instead of direct kernel imports.";

/// `Type.Object({ code: Type.String({ description }) })`: the old
/// `ipython_tool_schema` (`type`, `required: ["code"]`, `properties`).
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
        ipython_tool_description(),
        ipython_parameters(),
        move |args: PiJsonValue, api: Arc<dyn ToolExecutionApi>, cx: Context| {
            let runtime = Arc::clone(&runtime);
            async move { execute(&runtime, &args, api, &cx).await }
        },
    );
    registration.execution_mode = Some(ToolExecutionMode::Sequential);
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
        content: Some(vec![UserContentBlock::Text(TextContent::new(message))]),
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

    let output_failure: Arc<Mutex<Option<SessionError>>> = Arc::default();
    let on_stream: StreamCallback = {
        let api = Arc::clone(&api);
        let failure = Arc::clone(&output_failure);
        Arc::new(move |chunk: &str, _stream: StreamName| {
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
                on_stream: Some(on_stream),
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
    Ok(tool_result(&result))
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

/// The model-facing text: stdout, stderr, the result value, the traceback of
/// a failed cell, and the unattributed background output (the old
/// `format_execute_text`).
fn format_execute_text(result: &ExecuteResult) -> String {
    let mut text = result.stdout.clone();
    if !result.stderr.is_empty() {
        text.push_str(if text.is_empty() { "" } else { "\n" });
        text.push_str(&result.stderr);
    }
    if let Some(result_text) = &result.result {
        text.push_str(if text.is_empty() { "" } else { "\n" });
        text.push_str(result_text);
    }
    if result.status == ExecuteStatus::Error {
        if let Some(error) = &result.error {
            text.push_str(if text.is_empty() { "" } else { "\n" });
            text.push_str(&error.traceback.join("\n"));
        }
    }
    if let Some(background) = &result.background_output {
        let separator = if text.is_empty() { "" } else { "\n" };
        let _infallible = write!(
            text,
            "{separator}[background output (unattributed)]\n{background}"
        );
    }
    text
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
    }
}

/// The old `ipython` tool result: text plus image attachments, and the TUI
/// card details. The busy-kernel restart choice needs a UI the durable host
/// does not have, so `kernelRestarted` is always `false` (as in every
/// headless old session).
pub(crate) fn tool_result(result: &ExecuteResult) -> ToolExecutionResult {
    let mut content = vec![UserContentBlock::Text(TextContent::new(
        format_execute_text(result),
    ))];
    content.extend(result.attachments.iter().flatten().filter_map(image_block));
    let mut details = json!({
        "status": status_name(result.status),
        "kernelRestarted": false,
    });
    details["durationMs"] = json!(result.duration_ms);
    if !result.stdout.is_empty() {
        details["stdout"] = json!(result.stdout);
    }
    if !result.stderr.is_empty() {
        details["stderr"] = json!(result.stderr);
    }
    if let Some(result_text) = &result.result {
        details["result"] = json!(result_text);
    }
    if let Some(bash) = &result.bash_commands {
        details["bashCommands"] = json!({
            "first": bash.first,
            "count": bash.count,
            "lines": bash.lines,
        });
    }
    if let Some(background) = &result.background_output {
        details["backgroundOutput"] = json!(background);
    }
    if let Some(error) = &result.error {
        details["error"] = json!({
            "ename": error.ename,
            "evalue": error.evalue,
            "traceback": error.traceback,
        });
        details["errorEname"] = json!(error.ename);
    }
    if let Some(sent) = result
        .sent_agent_messages
        .as_ref()
        .filter(|sent| !sent.is_empty())
    {
        details["sentAgentMessages"] =
            json!(sent.iter().map(sent_agent_message_json).collect::<Vec<_>>());
    }
    ToolExecutionResult {
        content: Some(content),
        is_error: Some(matches!(
            result.status,
            ExecuteStatus::Error | ExecuteStatus::Aborted
        )),
        details: Some(JsonValue::from(details)),
        ..ToolExecutionResult::default()
    }
}
