//! The wire `edit` tool (`edit@hl.1`): one hashline payload per call,
//! applied by the session's documents, the same engine as the kernel's
//! `edit()`. The payload is a JSON string, so models write it without a
//! second layer of Python escaping; the grammar is the tool description.

use std::path::PathBuf;
use std::sync::Arc;

use eukhe_ai::typebox::{Options, TSchema, Type};
use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_durable::harness::define::define_tool;
use eukhe_durable::harness::types::{
    ToolExecutionApi, ToolExecutionMode, ToolExecutionResult, ToolRegistration, ToolReplay,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::pi_ai::{JsonValue as PiJsonValue, TextContent, UserContentBlock};
use serde_json::json;

use super::requests::{edit_rejection, edit_reply, EDIT_REV};
use super::DocumentsHost;
use crate::durable::HostDeps;

/// The tool name.
pub const EDIT_TOOL_NAME: &str = "edit";

const INTENT_DESCRIPTION: &str = "2-6 word present-participle intent, e.g. \"fixing the parser\"";
const INPUT_DESCRIPTION: &str = "One or more [PATH#TAG] sections";

fn parameters() -> TSchema {
    Type::object_with(
        [
            (
                "i",
                Type::optional(Type::string_with(
                    Options::new().set("description", INTENT_DESCRIPTION),
                )),
            ),
            (
                "input",
                Type::string_with(Options::new().set("description", INPUT_DESCRIPTION)),
            ),
        ],
        Options::new().set("additionalProperties", false),
    )
}

/// The `edit` registration: sequential with the kernel cell that may also
/// edit, and replay-unsafe (a write may have landed before a crash).
pub(super) fn edit_tool(host: &Arc<DocumentsHost>, deps: &Arc<HostDeps>) -> Arc<ToolRegistration> {
    let host = Arc::clone(host);
    let session_cwd = deps.cwd.clone();
    let mut registration = ToolRegistration::new(
        EDIT_TOOL_NAME,
        eukhe_docs::HASHLINE_DESCRIPTION,
        parameters(),
        move |args: PiJsonValue, api: Arc<dyn ToolExecutionApi>, cx: Context| {
            let host = Arc::clone(&host);
            let session_cwd = session_cwd.clone();
            async move { execute(host, session_cwd, &args, api, &cx).await }
        },
    );
    registration.execution_mode = Some(ToolExecutionMode::Sequential);
    registration.replay = Some(ToolReplay::Unsafe);
    define_tool(registration)
}

fn text_result(text: String, is_error: bool, details: serde_json::Value) -> ToolExecutionResult {
    ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
        is_error: Some(is_error),
        details: Some(JsonValue::from(details)),
        ..ToolExecutionResult::default()
    }
}

/// Paths resolve against the kernel cwd of the conversation's last `fs.*`
/// request (where its `read`/`grep` headers came from), else the agent cwd.
async fn execute(
    host: Arc<DocumentsHost>,
    session_cwd: PathBuf,
    args: &PiJsonValue,
    api: Arc<dyn ToolExecutionApi>,
    cx: &Context,
) -> SessionResult<ToolExecutionResult> {
    let input = args
        .get("input")
        .and_then(PiJsonValue::as_str)
        .ok_or_else(|| SessionError::error("edit tool requires an input string"))?
        .to_owned();
    let cwd = match host.kernel_cwd(api.conversation_id()) {
        Some(cwd) => cwd,
        None => api
            .agent(cx)
            .await?
            .cwd
            .clone()
            .map_or(session_cwd, PathBuf::from),
    };
    let edited = tokio::task::spawn_blocking(move || host.documents.edit(&cwd, &input))
        .await
        .map_err(|error| SessionError::error(format!("edit worker failed: {error}")))?;
    Ok(match edited {
        Ok(outcome) => {
            let reply = edit_reply(outcome);
            let text = reply.rendered.clone();
            text_result(text, false, json!(reply))
        }
        Err(error) => text_result(
            error.to_string(),
            true,
            json!({
                "version": EDIT_REV,
                "reason": edit_rejection(&error),
            }),
        ),
    })
}
