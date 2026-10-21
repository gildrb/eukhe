//! Code mode inside a durable task: [`run_codemode_task`] runs a script as
//! a phase of a background task instead of a tool call, so the script
//! outlives the turn that started it (eukhe's background `workflow` runs).
//!
//! The script's host globals and its replay state reach the task through
//! [`TaskApi`], a [`ToolExecutionApi`] over the task's
//! [`TaskRuntimeBackend`]. A task has no tool call: the script gets no
//! `tools.*` calls, and running output, details, diagnostics, and usage go
//! nowhere.

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_ai::models::Models;
use eukhe_chord::context::Context;
use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_types::pi_ai::{JsonObject as PiJsonObject, Usage};
use futures::future::BoxFuture;
use futures::FutureExt;

use super::call::execute;
use super::tool::{CodemodeToolOptions, OUTPUT_LIMITS};
use crate::documents::{AnyDocDefinition, ResolvedAddress};
use crate::env::{ExecutionEnv, ShellOutputSkip, ShellOutputWindow};
use crate::harness::types::{
    Agent, ConversationHandle, ExecuteToolOptions, InvocationTaskOptions,
    NestedToolExecutionResult, RegistrySnapshot, RetainedOutput, ToolCommitChange, ToolDiagnostic,
    ToolExecutionApi, ToolExecutionResult, ToolOutputChunk,
};
use crate::harness::Truncation;
use crate::session::{DocumentWatch, SessionError, SessionResult};
use crate::tasks::{AnyTask, SettledTask, TaskRuntimeBackend};
use crate::types::{
    AnyTaskRecord, ConversationId, DocumentObserver, DocumentReader, EntryId, TaskId, TaskOptions,
};

/// Run `source` (code mode source: an optional options line, then an
/// async function body) as a phase of the task of `runtime`, with
/// `options`'s sandbox and globals. The script's replay state lives under
/// the task, so a rerun of the phase (after a restart) must pass the same
/// source: it replays the journal, then continues live. The script cannot
/// call tools (`tools.*` calls fail).
///
/// # Errors
///
/// Invalid source, the task's environment, and the commits of the
/// script's replay state. An abort of the task (its signal) rejects with
/// [`SessionError::Aborted`] and commits no outcome, so the phase can run
/// again.
pub async fn run_codemode_task(
    options: Arc<CodemodeToolOptions>,
    runtime: Arc<dyn TaskRuntimeBackend>,
    cx: Context,
    source: &str,
) -> SessionResult<ToolExecutionResult> {
    let env = runtime.env(&cx).await?;
    let api = Arc::new(TaskApi {
        call_id: runtime.task_id().to_string(),
        runtime,
        env,
    });
    execute(options, api, cx, source).await
}

/// The [`ToolExecutionApi`] of a script that runs in a task.
struct TaskApi {
    runtime: Arc<dyn TaskRuntimeBackend>,
    env: Option<Arc<dyn ExecutionEnv>>,
    /// The task id: what host requests that anchor to a call see.
    call_id: String,
}

impl DocumentReader for TaskApi {
    fn snapshot_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        self.runtime.snapshot_definition(definition, resolved, cx)
    }

    fn snapshot_as_of_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        at: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        self.runtime
            .snapshot_as_of_definition(definition, resolved, at, cx)
    }
}

impl DocumentObserver for TaskApi {
    fn watch_doc_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentWatch>>> {
        self.runtime.watch_doc_definition(definition, resolved, cx)
    }
}

impl ToolExecutionApi for TaskApi {
    fn task_id(&self) -> TaskId {
        self.runtime.task_id()
    }

    fn conversation_id(&self) -> ConversationId {
        self.runtime.conversation_id()
    }

    fn call_id(&self) -> &str {
        &self.call_id
    }

    fn registry(&self) -> RegistrySnapshot {
        self.runtime.registry()
    }

    fn agent(&self, cx: &Context) -> BoxFuture<'static, SessionResult<Arc<Agent>>> {
        self.runtime.agent(cx)
    }

    fn models(&self) -> Models {
        self.runtime.models()
    }

    fn env(&self) -> Option<Arc<dyn ExecutionEnv>> {
        self.env.clone()
    }

    /// A task has no tool output: the chunk goes nowhere.
    fn output(
        &self,
        _chunk: ToolOutputChunk<'_>,
        _skipped: Option<ShellOutputSkip>,
    ) -> SessionResult<()> {
        Ok(())
    }

    fn output_window(&self) -> Option<ShellOutputWindow> {
        None
    }

    fn truncation(&self) -> Truncation {
        Truncation::On(OUTPUT_LIMITS)
    }

    fn retained_output(&self) -> SessionResult<RetainedOutput> {
        Ok(RetainedOutput {
            text: String::new(),
            truncated: false,
        })
    }

    /// A task has no tool result to carry the remark.
    fn diagnostic(&self, _diagnostic: ToolDiagnostic) -> SessionResult<()> {
        Ok(())
    }

    /// A task has no tool result to carry the spend.
    fn usage(&self, _usage: Usage) -> SessionResult<()> {
        Ok(())
    }

    /// A task has no tool call slot to show the details.
    fn details(&self, _value: JsonValue, _cx: &Context) -> BoxFuture<'static, SessionResult<()>> {
        futures::future::ready(Ok(())).boxed()
    }

    fn commit_erased(
        &self,
        change: ToolCommitChange,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<()>> {
        self.runtime.commit(
            Box::new(move |tx, _current| {
                async move {
                    change(tx).await?;
                    Ok(None)
                }
                .boxed()
            }),
            cx,
        )
    }

    fn memo(
        &self,
        name: &str,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<JsonValue>>> {
        self.runtime.memo(name, cx)
    }

    fn memo_or_store(
        &self,
        name: &str,
        candidate: JsonValue,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<JsonValue>> {
        self.runtime.memo_or_store(name, candidate, cx)
    }

    fn create_task_erased(
        &self,
        task: AnyTask,
        input: JsonValue,
        options: InvocationTaskOptions,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<TaskId>> {
        let created = Arc::new(Mutex::new(None));
        let slot = Arc::clone(&created);
        let committed = self.runtime.commit(
            Box::new(move |tx, _current| {
                async move {
                    let options = TaskOptions {
                        ownership: options.ownership,
                        conversation_id: None,
                        background: options.background,
                        abandon_on_restart: options.abandon_on_restart,
                    };
                    let id = tx
                        .create_task(task.as_definition_ref(), input, options)
                        .await?;
                    *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(id);
                    Ok(None)
                }
                .boxed()
            }),
            cx,
        );
        async move {
            committed.await?;
            let id = created
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .take();
            id.ok_or_else(|| SessionError::error("Task creation committed without an ID"))
        }
        .boxed()
    }

    fn get_task(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<AnyTaskRecord>>> {
        self.runtime.get_task(id, cx)
    }

    fn wait_for_task(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SettledTask>> {
        self.runtime.wait_for_task(id, cx)
    }

    fn conversation(
        &self,
        id: ConversationId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ConversationHandle>>>> {
        self.runtime.conversation(id, cx)
    }

    /// A task makes no nested tool calls.
    fn execute_tool(
        &self,
        name: &str,
        _args: PiJsonObject,
        _cx: &Context,
        _options: ExecuteToolOptions,
    ) -> BoxFuture<'static, SessionResult<NestedToolExecutionResult>> {
        let error = SessionError::error(format!(
            "a code mode script that runs in a task cannot call tools (it called {name})"
        ));
        futures::future::ready(Err(error)).boxed()
    }
}
