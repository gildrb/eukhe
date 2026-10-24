//! One execution of a tool: its [`ToolExecutionApi`], the throttled progress
//! publications of what it reports to the live observers (never to
//! storage), its nested calls, and the settled result.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Instant;

use eukhe_ai::models::Models;
use eukhe_ai::utils::validation::check_value;
use eukhe_chord::context::{await_with_context, Context};
use eukhe_chord::json::{copy_json, from_json, JsonObject, JsonValue};
use eukhe_types::pi_ai::{
    JsonObject as PiJsonObject, JsonValue as PiJsonValue, TextContent, Usage, UserContentBlock,
};
use futures::future::{BoxFuture, Shared};
use futures::FutureExt;

use super::nested::{
    check_key, fallback_result, output_value, start_nested_call, NestedCallRequest,
    NestedResultState, NESTED_RESULT_DOC,
};
use super::result::{bound_content, tool_diagnostic, truncated, ToolEnding};
use super::{settle, Repair, Runtime, ToolTaskInput, ToolTaskResult};
use crate::documents::{AnyDocDefinition, ResolvedAddress};
use crate::env::{ExecutionEnv, ShellOutputSkip, ShellOutputWindow};
use crate::harness::live::SlotProgress;
use crate::harness::output::{
    OutputBuffer, OutputLimits, Progress, Truncation, PROGRESS_BYTES_PER_SECOND,
};
use crate::harness::types::{
    Agent, ConversationHandle, ExecuteToolOptions, InvocationTaskOptions,
    NestedToolExecutionResult, OutputRetain, RegistrySnapshot, RetainedOutput, ToolCommitChange,
    ToolDiagnostic, ToolExecutionApi, ToolExecutionResult, ToolHookCall, ToolHooks,
    ToolOutputChunk, ToolRegistration, ToolReplay,
};
use crate::harness::usage::add_usage;
use crate::session::{DocumentWatch, SessionError, SessionResult};
use crate::tasks::{AnyTask, SettledTask};
use crate::types::{
    AnyTaskRecord, ConversationId, DocumentObserver, DocumentReader, DocumentReaderExt, EntryId,
    TaskId, TaskOptions, TaskOwnership,
};

/// What a running tool reported through its api: output, the last details,
/// diagnostics, and spend.
struct Reported {
    output: OutputBuffer,
    diagnostics: Vec<ToolDiagnostic>,
    details: Option<JsonValue>,
    usage: Option<Usage>,
}

impl Reported {
    /// Everything reported so far, as the call's progress.
    fn progress(&mut self) -> SlotProgress {
        let snapshot = self.output.snapshot();
        SlotProgress {
            output: (!snapshot.text.is_empty()).then_some(snapshot.text),
            dropped_bytes: (snapshot.dropped_bytes > 0).then_some(snapshot.dropped_bytes as u64),
            dropped_lines: (snapshot.dropped_lines > 0).then_some(snapshot.dropped_lines as u64),
            details: self.details.clone(),
            diagnostics: (!self.diagnostics.is_empty()).then(|| self.diagnostics.clone()),
            usage: self.usage,
        }
    }
}

/// A nested call's admission, shared by its `execute_tool()` and the
/// cleanup that waits for every admission an invocation started.
type Admission = Shared<BoxFuture<'static, SessionResult<TaskId>>>;

/// State shared by the api, the progress publications, and the settlement.
struct Reporting {
    reported: Arc<Mutex<Reported>>,
    progress: Progress,
    truncation: Truncation,
    ended: AtomicBool,
    call_id: String,
    /// Nested call admissions this invocation started; cleanup waits for
    /// them, so it sees every nested call.
    admissions: Mutex<Vec<Admission>>,
    /// Default keys: the order of this invocation's calls, so a rerun that
    /// calls in the same order reattaches.
    sequence: AtomicU64,
}

impl Reporting {
    fn assert_live(&self) -> SessionResult<()> {
        if self.ended.load(Ordering::SeqCst) {
            return Err(SessionError::error(format!(
                "Tool call {} has settled",
                self.call_id
            )));
        }
        Ok(())
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Reported> {
        self.reported.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// Throttled publications of what the tool reported to the live observers
/// of its conversation (`LiveProgress`), never to storage; none when
/// `enabled` is false. The board reads the reported state itself, so the
/// settle of an abort carries everything reported, published or not.
fn publish_progress(runtime: &Runtime, reported: &Arc<Mutex<Reported>>, enabled: bool) -> Progress {
    let live = runtime.backend().live_progress();
    let task_id = runtime.task_id().erase();
    if enabled {
        let reported = Arc::clone(reported);
        live.start(
            runtime.conversation_id(),
            task_id,
            Box::new(move || {
                reported
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .progress()
            }),
        );
    }
    let report_runtime = runtime.clone();
    Progress::new(
        Box::new(move || futures::future::ready(Ok(live.publish(task_id))).boxed()),
        Box::new(move |error| {
            // After the invocation ended there is nobody left to report to; TS throws into an unobserved promise.
            let _ended = report_runtime.report(error);
        }),
        runtime.settings().progress.output_interval_ms,
    )
}

/// The api of one execution (TS `ToolExecutionApi` built in `run`).
struct ToolInvocation {
    runtime: Runtime,
    reporting: Arc<Reporting>,
    output_window: Option<ShellOutputWindow>,
    env: Option<Arc<dyn ExecutionEnv>>,
    /// A caller that can rerun reattaches to its nested calls and child
    /// tasks after a restart; any other caller never resumes, so they are
    /// abandoned (`TaskOptions.abandon_on_restart`).
    resumes: bool,
}

impl DocumentReader for ToolInvocation {
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

impl DocumentObserver for ToolInvocation {
    fn watch_doc_definition(
        &self,
        definition: Arc<dyn AnyDocDefinition>,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentWatch>>> {
        self.runtime.watch_doc_definition(definition, resolved, cx)
    }
}

impl ToolExecutionApi for ToolInvocation {
    fn task_id(&self) -> TaskId {
        self.runtime.task_id().erase()
    }

    fn conversation_id(&self) -> ConversationId {
        self.runtime.conversation_id()
    }

    fn call_id(&self) -> &str {
        &self.reporting.call_id
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

    fn retained_output(&self) -> SessionResult<RetainedOutput> {
        self.reporting.assert_live()?;
        let retained = self.reporting.lock().output.snapshot();
        Ok(RetainedOutput {
            truncated: retained.dropped_bytes > 0,
            text: retained.text,
        })
    }

    fn env(&self) -> Option<Arc<dyn ExecutionEnv>> {
        self.env.clone()
    }

    fn output(
        &self,
        chunk: ToolOutputChunk<'_>,
        skipped: Option<ShellOutputSkip>,
    ) -> SessionResult<()> {
        self.reporting.assert_live()?;
        let changed = self
            .reporting
            .lock()
            .output
            .push(chunk, skipped.as_ref())
            .map_err(SessionError::other)?;
        if changed {
            self.reporting.progress.mark();
        }
        Ok(())
    }

    fn output_window(&self) -> Option<ShellOutputWindow> {
        self.output_window
    }

    fn truncation(&self) -> Truncation {
        self.reporting.truncation
    }

    fn diagnostic(&self, diagnostic: ToolDiagnostic) -> SessionResult<()> {
        self.reporting.assert_live()?;
        self.reporting.lock().diagnostics.push(diagnostic);
        self.reporting.progress.mark();
        Ok(())
    }

    fn usage(&self, usage: Usage) -> SessionResult<()> {
        self.reporting.assert_live()?;
        let mut reported = self.reporting.lock();
        match &mut reported.usage {
            Some(total) => add_usage(total, &usage),
            None => reported.usage = Some(usage),
        }
        Ok(())
    }

    fn details(&self, value: JsonValue, cx: &Context) -> BoxFuture<'static, SessionResult<()>> {
        let checked = self
            .reporting
            .assert_live()
            .and_then(|()| match cx.abort_signal() {
                Some(signal) => signal.throw_if_aborted().map_err(SessionError::Aborted),
                None => Ok(()),
            });
        if let Err(error) = checked {
            return futures::future::ready(Err(error)).boxed();
        }
        self.reporting.lock().details = Some(copy_json(&value));
        let committed = self.reporting.progress.mark_and_wait();
        let cx = cx.clone();
        // Cancelling the wait leaves the update in place; the commit's own outcome stays observed.
        async move {
            await_with_context(committed, &cx)
                .await
                .map_err(SessionError::Aborted)?
        }
        .boxed()
    }

    fn commit_erased(
        &self,
        change: ToolCommitChange,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<()>> {
        self.runtime.commit(
            move |tx, _current| async move {
                change(tx).await?;
                Ok(None)
            },
            cx,
        )
    }

    fn memo(
        &self,
        name: &str,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<JsonValue>>> {
        self.runtime.backend().memo(name, cx)
    }

    fn memo_or_store(
        &self,
        name: &str,
        candidate: JsonValue,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<JsonValue>> {
        self.runtime.backend().memo_or_store(name, candidate, cx)
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
        // A child of a tool that is not replay-safe defaults to `abandon_on_restart`.
        let abandon_on_restart = options.abandon_on_restart.or_else(|| {
            (matches!(options.ownership, TaskOwnership::Task { .. }) && !self.resumes)
                .then_some(true)
        });
        let committed = self.runtime.commit(
            move |tx, _current| async move {
                let options = TaskOptions {
                    ownership: options.ownership,
                    conversation_id: None,
                    background: options.background,
                    abandon_on_restart,
                };
                let id = tx
                    .create_task(task.as_definition_ref(), input, options)
                    .await?;
                *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(id);
                Ok(None)
            },
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
        self.runtime.backend().get_task(id, cx)
    }

    fn wait_for_task(
        &self,
        id: TaskId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SettledTask>> {
        self.runtime.backend().wait_for_task(id, cx)
    }

    fn conversation(
        &self,
        id: ConversationId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ConversationHandle>>>> {
        self.runtime.conversation(id, cx)
    }

    fn execute_tool(
        &self,
        name: &str,
        args: PiJsonObject,
        cx: &Context,
        options: ExecuteToolOptions,
    ) -> BoxFuture<'static, SessionResult<NestedToolExecutionResult>> {
        if let Err(error) = self.reporting.assert_live() {
            return futures::future::ready(Err(error)).boxed();
        }
        let key = match options.key {
            Some(key) => {
                if let Err(error) = check_key(&key) {
                    return futures::future::ready(Err(error)).boxed();
                }
                key
            }
            None => (self.reporting.sequence.fetch_add(1, Ordering::SeqCst) + 1).to_string(),
        };
        let request = NestedCallRequest {
            parent_call_id: self.reporting.call_id.clone(),
            name: name.to_owned(),
            args,
            key,
            progress: options.progress,
            abandon_on_restart: !self.resumes,
        };
        let admission = start_nested_call(&self.runtime, request, cx).shared();
        self.reporting
            .admissions
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(admission.clone());
        let (runtime, cx, name) = (self.runtime.clone(), cx.clone(), name.to_owned());
        async move {
            let id = admission.await?;
            let settled = runtime
                .wait_for_task(TaskId::<ToolTaskResult>::from_number(id.get()), &cx)
                .await?;
            let caller = runtime.task_id().erase();
            let stored = runtime
                .snapshot(&NESTED_RESULT_DOC, (caller, &id.to_string()), &cx)
                .await?;
            // A copy the tool may change; a nested call the scheduler faulted or orphaned stored none.
            match stored {
                Some(stored) => {
                    Ok(from_json::<NestedResultState>(&JsonValue::Object(stored))?.result)
                }
                None => Ok(fallback_result(id, &name, &settled.outcome)),
            }
        }
        .boxed()
    }
}

/// The invocation's reporting state for `tool`, with its truncation
/// resolved, and the output window a shell may skip outside of: the one
/// place a call's limits are resolved.
fn reporting_for(
    runtime: &Runtime,
    input: &ToolTaskInput,
    call: &ToolHookCall,
    tool: &ToolRegistration,
) -> (Arc<Reporting>, Option<ShellOutputWindow>) {
    let truncation = tool.truncation;
    let reported = Arc::new(Mutex::new(Reported {
        output: OutputBuffer::new(truncation),
        diagnostics: Vec::new(),
        details: None,
        usage: None,
    }));
    let publishes = match input {
        ToolTaskInput::Model { .. } => true,
        ToolTaskInput::Nested { progress, .. } => *progress != Some(false),
    };
    let reporting = Arc::new(Reporting {
        progress: publish_progress(runtime, &reported, publishes),
        reported,
        truncation,
        ended: AtomicBool::new(false),
        call_id: call.id.clone(),
        admissions: Mutex::new(Vec::new()),
        sequence: AtomicU64::new(0),
    });
    let output_window = match truncation {
        Truncation::On(OutputLimits {
            max_bytes,
            max_lines,
            retain: OutputRetain::Tail,
        }) => Some(ShellOutputWindow {
            max_bytes: max_bytes as u64,
            max_lines: max_lines as u64,
            min_interval_ms: runtime.settings().progress.output_interval_ms,
            bytes_per_second: PROGRESS_BYTES_PER_SECOND,
        }),
        Truncation::On(OutputLimits {
            retain: OutputRetain::Head,
            ..
        })
        | Truncation::Off => None,
    };
    (reporting, output_window)
}

/// Execute with the resolved implementation, then settle its result. The
/// dialect repairs lead the result's diagnostics.
pub(super) async fn run(
    runtime: &Runtime,
    input: &ToolTaskInput,
    call: &ToolHookCall,
    tool: &ToolRegistration,
    args: PiJsonObject,
    repairs: Vec<Repair>,
    cx: &Context,
) -> SessionResult<()> {
    let (reporting, output_window) = reporting_for(runtime, input, call, tool);
    reporting
        .lock()
        .diagnostics
        .extend(repairs.iter().map(Repair::diagnostic));

    let mut ending = ToolEnding::Completed;
    // Execution time of this attempt; a rerun after recovery measures only itself.
    let mut duration_ms = None;
    // Built for this call, so a rerun after recovery gets the conversation's environment at that time.
    let executed = match runtime.env(cx).await {
        Ok(env) => {
            let api = Arc::new(ToolInvocation {
                runtime: runtime.clone(),
                reporting: Arc::clone(&reporting),
                output_window,
                env,
                resumes: tool.replay == Some(ToolReplay::Safe),
            });
            let started = Instant::now();
            let executed = (tool.execute)(PiJsonValue::Object(args), api, cx.clone()).await;
            duration_ms = Some(elapsed_ms(started));
            executed
        }
        Err(error) => Err(error),
    };
    let result = match executed {
        Ok(result) => result,
        Err(error) => {
            if runtime.signal().aborted() {
                reporting.ended.store(true, Ordering::SeqCst);
                // The abort handler settles with what the call reported, read from the live board.
                for waiter in reporting.progress.stop().await {
                    // A waiter whose caller stopped waiting has nobody to tell.
                    let _gone = waiter.send(Err(error.clone()));
                }
                return Err(error);
            }
            // A throw, from `execute()` or from building the environment, ends the task `failed`, which cancels what
            // the call owned; it no longer supervises it. The error text is already in the result.
            ending = ToolEnding::Failed {
                message: format!("Tool {} threw", call.name),
            };
            ToolExecutionResult {
                is_error: Some(true),
                diagnostics: Some(vec![tool_diagnostic("tool_error", &error.to_string())]),
                ..ToolExecutionResult::default()
            }
        }
    };
    reporting.ended.store(true, Ordering::SeqCst);
    // No admission starts after `ended`; let those underway commit, so settlement aborts and lists their calls.
    let admissions = std::mem::take(
        &mut *reporting
            .admissions
            .lock()
            .unwrap_or_else(PoisonError::into_inner),
    );
    futures::future::join_all(admissions).await;
    reporting.lock().output.end();
    // Details still waiting for a progress publication settle with the terminal commit, the final flush.
    let pending = reporting.progress.stop().await;
    let settled = async {
        let settled = final_result(runtime, input, call, tool, result, &reporting, cx).await?;
        settle(
            runtime,
            input,
            call,
            ending,
            move |_| settled,
            cx,
            duration_ms,
        )
        .await
    }
    .await;
    for waiter in pending {
        let _gone = waiter.send(settled.clone());
    }
    settled
}

/// Whole milliseconds since `started` (TS `Math.round(performance.now() -
/// startedAt)`).
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "an execution time is a small non-negative number of milliseconds"
)]
fn elapsed_ms(started: Instant) -> u64 {
    (started.elapsed().as_secs_f64() * 1000.0).round() as u64
}

/// The settled result: the tool's result with the retained output and last
/// details as fallbacks, its diagnostics after those reported through the
/// api, `after_tool` applied, explicit text bounded, and `structured_output`
/// checked against the tool's schema, with the Harness's diagnostics last. A
/// nested call whose `structured_output` breaks the contract gets an error
/// result without it; a model-issued call only loses it, and the break is
/// reported to the host.
#[expect(
    clippy::too_many_lines,
    reason = "one TS function over the invocation's state"
)]
async fn final_result(
    runtime: &Runtime,
    input: &ToolTaskInput,
    call: &ToolHookCall,
    tool: &ToolRegistration,
    result: ToolExecutionResult,
    reporting: &Reporting,
    cx: &Context,
) -> SessionResult<ToolExecutionResult> {
    let mut harness = Vec::new();
    let (retained, reported_details, reported_diagnostics, reported_usage) = {
        let mut state = reporting.lock();
        let retained = result.output.is_none().then(|| state.output.snapshot());
        (
            retained,
            state.details.clone(),
            state.diagnostics.clone(),
            state.usage,
        )
    };
    let output = match (&retained, &result.output) {
        (Some(retained), _) if retained.text.is_empty() => Vec::new(),
        (Some(retained), _) => vec![UserContentBlock::Text(TextContent::new(
            retained.text.clone(),
        ))],
        (None, output) => output.clone().unwrap_or_default(),
    };
    let mut diagnostics = reported_diagnostics;
    diagnostics.extend(result.diagnostics.clone().unwrap_or_default());
    // The settle carries all spend: what the call recorded while running and its result's own.
    let usage = match (reported_usage, result.usage) {
        (Some(mut total), Some(own)) => {
            add_usage(&mut total, &own);
            Some(total)
        }
        (reported, own) => reported.or(own),
    };
    let initial = ToolExecutionResult {
        output: Some(output.clone()),
        details: result.details.clone().or(reported_details),
        diagnostics: Some(diagnostics),
        usage,
        ..result
    };
    let current = Arc::new(Mutex::new(initial));
    let hook_api = runtime.hook_api();
    runtime
        .hooks()
        .each(
            |hooks: &ToolHooks| hooks.after_tool.clone(),
            |hook| {
                let current = Arc::clone(&current);
                let hook_api = hook_api.clone();
                let call = call.clone();
                let cx = cx.clone();
                async move {
                    let input = current
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .clone();
                    if let Some(replaced) = hook(&call, &input, &hook_api, &cx).await? {
                        *current.lock().unwrap_or_else(PoisonError::into_inner) = replaced;
                    }
                    Ok(())
                }
            },
        )
        .await?;
    let mut last = current
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    let content = last.output.clone().unwrap_or_default();
    let content = match reporting.truncation {
        Truncation::On(limits) => {
            // The retained output's truncation applies only while afterTool kept that output.
            if let Some(retained) = &retained {
                harness.extend(truncated(
                    retained.dropped_lines as u64,
                    retained.dropped_bytes as u64,
                    limits.retain,
                    last.output.as_ref() == Some(&output),
                ));
            }
            let bounded = bound_content(content, &limits);
            harness.extend(truncated(
                bounded.dropped_lines as u64,
                bounded.dropped_bytes as u64,
                limits.retain,
                true,
            ));
            bounded.content
        }
        Truncation::Off => content,
    };
    let nested = matches!(input, ToolTaskInput::Nested { .. });
    if let Some(broken) = structured_output_error(tool, &last)? {
        last.structured_output = None;
        if nested {
            last.is_error = Some(true);
            harness.push(tool_diagnostic("invalid_structured_output", &broken));
        } else {
            // The model never sees structured output, so its call stands; the host learns of the broken tool.
            runtime.report(SessionError::error(broken))?;
        }
    }
    // Without a schema, programs get the output itself; the model reads only `output`, so model-issued calls skip it.
    if nested && tool.structured_output_schema.is_none() {
        last.structured_output = Some(output_value(&content)?);
    }
    let mut diagnostics = last.diagnostics.clone().unwrap_or_default();
    diagnostics.extend(harness);
    Ok(ToolExecutionResult {
        output: Some(content),
        diagnostics: Some(diagnostics),
        ..last
    })
}

/// Why a result's `structured_output` breaks the tool's contract, or `None`
/// when it keeps it.
fn structured_output_error(
    tool: &ToolRegistration,
    result: &ToolExecutionResult,
) -> SessionResult<Option<String>> {
    let name = &tool.name;
    let Some(schema) = &tool.structured_output_schema else {
        return Ok(result.structured_output.as_ref().map(|_| {
            format!("Tool {name} returned structuredOutput but declares no structuredOutputSchema")
        }));
    };
    let Some(value) = &result.structured_output else {
        return Ok((result.is_error != Some(true))
            .then(|| format!("Tool {name} returned no structuredOutput")));
    };
    let value = from_json::<PiJsonValue>(value)?;
    let checked =
        check_value(schema, &value).map_err(|error| SessionError::error(error.to_string()))?;
    let Some(first) = checked else {
        return Ok(None);
    };
    let path = first
        .as_ref()
        .map(|error| {
            let path = &error.instance_path;
            path.strip_prefix('/').unwrap_or(path).replace('/', ".")
        })
        .filter(|path| !path.is_empty())
        .unwrap_or_else(|| "root".to_owned());
    let message = first.map_or_else(|| "invalid".to_owned(), |error| error.message);
    Ok(Some(format!(
        "Tool {name} returned structuredOutput that does not match its schema: {path}: {message}"
    )))
}
