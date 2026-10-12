//! The `zoom` and `date` tools (§7.1) over the chat memory.

use std::sync::Arc;

use eukhe_durable::harness::define::define_tool;
use eukhe_durable::harness::types::{ToolExecutionResult, ToolRegistration};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::pi_ai::{TextContent, UserContentBlock};

use crate::memory::{Memory, DATE_TOOL_DESCRIPTION, ZOOM_TOOL_DESCRIPTION};

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
