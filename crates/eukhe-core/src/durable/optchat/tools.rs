//! The `zoom` and `date` tools (§7.1) over the chat memory, and the cap on
//! tool results (results are resent on every later step of the call and
//! land in the permanent log).

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_durable::harness::define::define_tool;
use eukhe_durable::harness::types::{
    HookApi, HookFuture, ToolExecutionResult, ToolHookCall, ToolHooks, ToolRegistration,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::pi_ai::{TextContent, UserContentBlock};
use futures::FutureExt;

use crate::memory::{cap_text, Memory, CAP, DATE_TOOL_DESCRIPTION, ZOOM_TOOL_DESCRIPTION};

/// `zoom(id, n)` and `date(id)`.
pub(crate) fn memory_tools(memory: &Memory) -> Vec<Arc<ToolRegistration>> {
    let zoom_memory = memory.clone();
    let zoom = ToolRegistration::new(
        "zoom",
        ZOOM_TOOL_DESCRIPTION,
        serde_json::json!({
            "type": "object",
            "properties": {
                "id": { "type": "integer", "minimum": 0 },
                "n": { "type": "integer", "minimum": 1 }
            },
            "required": ["id", "n"],
            "additionalProperties": false
        }),
        move |params, _api, _cx| {
            let memory = zoom_memory.clone();
            async move {
                let id = integer_argument(&params, "id")?;
                let count = integer_argument(&params, "n")?;
                let text = memory
                    .zoom(id, count)
                    .await
                    .map_err(|error| memory_error(&error))?;
                Ok(text_result(text))
            }
        },
    );
    let date_memory = memory.clone();
    let date = ToolRegistration::new(
        "date",
        DATE_TOOL_DESCRIPTION,
        serde_json::json!({
            "type": "object",
            "properties": {
                "id": { "type": "integer", "minimum": 0 }
            },
            "required": ["id"],
            "additionalProperties": false
        }),
        move |params, _api, _cx| {
            let memory = date_memory.clone();
            async move {
                let id = integer_argument(&params, "id")?;
                let text = memory
                    .date(id)
                    .await
                    .map_err(|error| memory_error(&error))?;
                Ok(text_result(text))
            }
        },
    );
    vec![define_tool(zoom), define_tool(date)]
}

fn integer_argument(params: &serde_json::Value, name: &str) -> SessionResult<u64> {
    params
        .get(name)
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| SessionError::error(format!("`{name}` must be a non-negative integer")))
}

fn text_result(text: String) -> ToolExecutionResult {
    ToolExecutionResult {
        output: Some(vec![UserContentBlock::Text(TextContent::new(text))]),
        ..ToolExecutionResult::default()
    }
}

/// A chat memory failure as the harness reports it.
pub(crate) fn memory_error(error: &anyhow::Error) -> SessionError {
    SessionError::error(format!("{error:#}"))
}

/// The tool task hooks: every tool result capped at [`CAP`] characters,
/// head and tail kept, images after the text.
pub(crate) fn cap_hooks() -> ToolHooks {
    ToolHooks {
        before_tool: None,
        after_tool: Some(Arc::new(cap_tool_result)),
    }
}

fn cap_tool_result(
    _call: &ToolHookCall,
    result: &ToolExecutionResult,
    _api: &HookApi,
    _cx: &Context,
) -> HookFuture<ToolExecutionResult> {
    let capped = capped(result);
    futures::future::ready(Ok(capped)).boxed()
}

/// `result` with its text capped, or `None` when within [`CAP`].
pub(super) fn capped(result: &ToolExecutionResult) -> Option<ToolExecutionResult> {
    let blocks = result.output.as_deref().unwrap_or_default();
    let text = blocks
        .iter()
        .filter_map(|block| match block {
            UserContentBlock::Text(text) => Some(text.text.as_str()),
            UserContentBlock::Image(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n");
    if text.chars().count() <= CAP {
        return None;
    }
    let mut content = vec![UserContentBlock::Text(TextContent::new(cap_text(&text)))];
    content.extend(
        blocks
            .iter()
            .filter(|block| matches!(block, UserContentBlock::Image(_)))
            .cloned(),
    );
    Some(ToolExecutionResult {
        output: Some(content),
        ..result.clone()
    })
}
