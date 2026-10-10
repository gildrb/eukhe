//! The `write` tool. Port of `tools/write.ts`.

use std::sync::Arc;

use eukhe_pi_ai::typebox::{Options, TSchema, Type};
use eukhe_types::pi_ai::{TextContent, UserContentBlock};
use serde::Deserialize;

use super::env::{operation_aborted, require_env};
use super::file_mutation_queue::with_file_mutation_queue;
use super::path_utils::resolve_tool_path;
use crate::harness::define::define_tool;
use crate::harness::types::{ToolExecutionResult, ToolRegistration};
use crate::session::SessionError;

fn write_schema() -> TSchema {
    Type::object([
        (
            "path",
            Type::string_with(Options::new().set(
                "description",
                "Path to the file to write (relative or absolute)",
            )),
        ),
        (
            "content",
            Type::string_with(Options::new().set("description", "Content to write to the file")),
        ),
    ])
}

/// Arguments of `write` (TS `WriteToolInput`).
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct WriteToolInput {
    pub path: String,
    pub content: String,
}

/// Writes content to a file, creating parent directories.
#[must_use]
pub fn create_write_tool() -> Arc<ToolRegistration> {
    define_tool(ToolRegistration::new(
        "write",
        "Write content to a file. Creates the file if it doesn't exist, overwrites if it does. Automatically creates parent directories.",
        write_schema(),
        |args, api, cx| async move {
            let WriteToolInput { path, content } =
                serde_json::from_value(args).map_err(SessionError::other)?;
            let env = require_env(api.as_ref())?;
            let absolute_path = resolve_tool_path(env.as_ref(), &path, &cx).await?;
            with_file_mutation_queue(
                env.as_ref(),
                &absolute_path,
                || async {
                    if cx.aborted() {
                        return Err(operation_aborted());
                    }
                    env.write_file(&absolute_path, content.as_bytes(), &cx).await?;
                    if cx.aborted() {
                        return Err(operation_aborted());
                    }
                    Ok(ToolExecutionResult {
                        output: Some(vec![UserContentBlock::Text(TextContent::new(format!(
                            "Successfully wrote to {path}"
                        )))]),
                        ..ToolExecutionResult::default()
                    })
                },
                &cx,
            )
            .await
        },
    ))
}
