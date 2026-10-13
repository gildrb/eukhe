//! The wire documents tools: `read` (`read@1`), `edit` (`edit@hl.1`),
//! `grep` (`grep@1`), and `glob` (`glob@1`). Each performs its function on
//! the session's documents, the same engine and edit store as the kernel's
//! `read()`/`edit()`/`grep()`/`glob()`, so lines either shows are anchorable
//! by both. The Harness repairs the arguments by the function's declared
//! dialect before the call; the text is bounded once by [`BoundedOutput`].

use std::path::PathBuf;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_chord::json::JsonValue;
use eukhe_durable::harness::define::define_tool;
use eukhe_durable::harness::types::{
    ToolExecutionApi, ToolExecutionMode, ToolExecutionResult, ToolRegistration, ToolReplay,
};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_types::pi_ai::{JsonValue as PiJsonValue, TextContent, UserContentBlock};

use super::contract::Function;
use super::requests::perform;
use super::DocumentsHost;
use crate::durable::bounded_output::BoundedOutput;
use crate::durable::HostDeps;

/// The registration of `function`. `edit` runs sequentially with the kernel
/// cell that may also edit and never replays (a write may have landed
/// before a crash); the others only read and replay safely.
pub(super) fn document_tool(
    function: Function,
    host: &Arc<DocumentsHost>,
    deps: &Arc<HostDeps>,
) -> Arc<ToolRegistration> {
    let host = Arc::clone(host);
    let deps = Arc::clone(deps);
    let mut registration = ToolRegistration::new(
        function.name(),
        function.description(),
        function.parameters(),
        move |args: PiJsonValue, api: Arc<dyn ToolExecutionApi>, cx: Context| {
            let host = Arc::clone(&host);
            let deps = Arc::clone(&deps);
            async move { execute(function, host, &deps, args, api, &cx).await }
        },
    );
    registration.dialect = function.dialect();
    match function {
        Function::Edit | Function::Write => {
            registration.execution_mode = Some(ToolExecutionMode::Sequential);
            registration.replay = Some(ToolReplay::Unsafe);
        }
        Function::Read | Function::Grep | Function::Glob => {
            registration.replay = Some(ToolReplay::Safe);
        }
    }
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

/// Relative paths resolve against the session's working directory (the
/// agent's cwd, else the session's).
async fn execute(
    function: Function,
    host: Arc<DocumentsHost>,
    deps: &HostDeps,
    args: PiJsonValue,
    api: Arc<dyn ToolExecutionApi>,
    cx: &Context,
) -> SessionResult<ToolExecutionResult> {
    let PiJsonValue::Object(args) = args else {
        return Err(SessionError::error(format!(
            "{} arguments must be an object",
            function.name()
        )));
    };
    let cwd = api
        .agent(cx)
        .await?
        .cwd
        .clone()
        .map_or_else(|| deps.cwd.clone(), PathBuf::from);
    let performed =
        tokio::task::spawn_blocking(move || perform(&host.documents, function, &cwd, args))
            .await
            .map_err(|error| {
                SessionError::error(format!("{} worker failed: {error}", function.name()))
            })?;
    match performed {
        Ok(done) => {
            let mut output =
                BoundedOutput::in_session(deps.storage_dir.as_deref(), &api.task_id().to_string());
            output.push(done.rendered());
            let (text, bounded) = output.finish();
            let details = serde_json::to_value(&done).map_err(SessionError::other)?;
            Ok(ToolExecutionResult {
                diagnostics: bounded.map(|diagnostic| vec![diagnostic]),
                ..text_result(text, false, details)
            })
        }
        Err(rejection) => {
            let details = serde_json::to_value(&rejection).map_err(SessionError::other)?;
            Ok(text_result(rejection.message, true, details))
        }
    }
}
