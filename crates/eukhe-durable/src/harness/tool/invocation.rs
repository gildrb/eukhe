//! One execution of a tool: its [`ToolExecutionApi`], the throttled progress
//! commits into its `pi.live.tools` or `pi.live.nestedTools` slot, its
//! nested calls, and the settled result.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Instant;

use eukhe_chord::context::{await_with_context, Context};
use eukhe_chord::delta::{overlap, DraftItem};
use eukhe_chord::json::{copy_json, from_json, to_json, JsonObject, JsonValue};
use eukhe_pi_ai::models::Models;
use eukhe_pi_ai::utils::validation::check_value;
use eukhe_types::pi_ai::{
    JsonObject as PiJsonObject, JsonValue as PiJsonValue, TextContent, UserContentBlock,
};
use futures::future::{BoxFuture, Shared};
use futures::FutureExt;

use super::nested::{
    check_key, fallback_result, output_value, start_nested_call, NestedCallRequest,
    NestedResultState, NESTED_RESULT_DOC,
};
use super::result::{bound_content, tool_diagnostic, truncated, ToolEnding};
use super::{json_bytes, settle, Runtime, ToolTaskInput, ToolTaskResult};
use crate::documents::{AnyDocDefinition, ResolvedAddress};
use crate::env::{ExecutionEnv, ShellOutputSkip, ShellOutputWindow};
use crate::harness::json::assign_json;
use crate::harness::live::{tool_slot, LIVE_DOC};
use crate::harness::output::{OutputBuffer, OutputLimits, Progress, PROGRESS_BYTES_PER_SECOND};
use crate::harness::types::{
    Agent, ConversationHandle, ExecuteToolOptions, InvocationTaskOptions,
    NestedToolExecutionResult, OutputRetain, RegistrySnapshot, RetainedOutput, ToolCommitChange,
    ToolDiagnostic, ToolExecutionApi, ToolExecutionResult, ToolHookCall, ToolHooks,
    ToolOutputChunk, ToolRegistration, ToolReplay,
};
use crate::session::{DocumentWatch, SessionError, SessionResult};
use crate::tasks::{AnyTask, SettledTask};
use crate::truncate::{DEFAULT_MAX_BYTES, DEFAULT_MAX_LINES};
use crate::types::{
    AnyTaskRecord, ConversationId, DocumentObserver, DocumentReader, DocumentReaderExt, EntryId,
    TaskId, TaskOptions, TaskOwnership,
};

/// What a running tool reported through its api: output, the last details,
/// and diagnostics.
struct Reported {
    output: OutputBuffer,
    diagnostics: Vec<ToolDiagnostic>,
    details: Option<JsonValue>,
}

/// What the last progress commit wrote.
#[derive(Default)]
struct Written {
    text: String,
    details: Option<JsonValue>,
    diagnostics: usize,
}

/// A nested call's admission, shared by its `execute_tool()` and the
/// cleanup that waits for every admission an invocation started.
type Admission = Shared<BoxFuture<'static, SessionResult<TaskId>>>;

/// State shared by the api, the progress commits, and the settlement.
struct Reporting {
    reported: Arc<Mutex<Reported>>,
    progress: Progress,
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

/// UTF-8 byte offset of `units` UTF-16 code units into `text`.
fn utf16_to_byte(text: &str, units: usize) -> usize {
    let mut count = 0;
    for (index, c) in text.char_indices() {
        if count >= units {
            return index;
        }
        count += c.len_utf16();
    }
    text.len()
}

/// Throttled commits of what the tool reported into its slot, in
/// `pi.live.tools` or `pi.live.nestedTools`, each writing only what changed
/// since the last one; none when `enabled` is false.
#[expect(
    clippy::too_many_lines,
    reason = "one TS function: the capture and the commit share its state"
)]
fn publish_progress(
    runtime: &Runtime,
    reported: &Arc<Mutex<Reported>>,
    enabled: bool,
    cx: &Context,
) -> Progress {
    let commit_cx = cx.clone();
    let written = Arc::new(Mutex::new(Written::default()));
    let write_runtime = runtime.clone();
    let reported = Arc::clone(reported);
    let report_runtime = runtime.clone();
    Progress::new(
        Box::new(move || {
            if !enabled {
                return futures::future::ready(Ok(0)).boxed();
            }
            // Capture everything synchronously: the tool keeps reporting while the commit is in flight.
            let (snapshot, details, diagnostics) = {
                let mut state = reported.lock().unwrap_or_else(PoisonError::into_inner);
                (
                    state.output.snapshot(),
                    state.details.clone(),
                    state.diagnostics.clone(),
                )
            };
            let (added, details_changed, bytes) = {
                let previous = written.lock().unwrap_or_else(PoisonError::into_inner);
                let added: Vec<ToolDiagnostic> =
                    diagnostics[previous.diagnostics.min(diagnostics.len())..].to_vec();
                let details_changed = details != previous.details;
                // What the commit writes, as Chord diffs the string: an append, a trim plus an append of what follows
                // the shared part, or the whole window when its bounded overlap search finds nothing.
                let mut bytes = 0;
                if snapshot.text != previous.text {
                    let shared = if snapshot.text.starts_with(previous.text.as_str()) {
                        previous.text.len()
                    } else {
                        utf16_to_byte(
                            &snapshot.text,
                            overlap(&previous.text, &snapshot.text, 65_536),
                        )
                    };
                    bytes += snapshot.text.len() - shared;
                }
                if details_changed {
                    bytes += details.as_ref().map_or(4, json_bytes);
                }
                if !added.is_empty() {
                    bytes += serde_json::to_string(&added).map_or(0, |text| text.len());
                }
                (added, details_changed, bytes)
            };
            let runtime = write_runtime.clone();
            let written = Arc::clone(&written);
            let cx = commit_cx.clone();
            async move {
                let conversation_id = runtime.conversation_id();
                let task_id = runtime.task_id().erase();
                let text = snapshot.text.clone();
                let commit_details = details.clone();
                runtime
                    .commit(
                        move |tx, _current| async move {
                            let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                            let Some(slot) = tool_slot(&live, task_id)? else {
                                return Ok(None);
                            };
                            // REMINDER: assign `output` as one string field. Chord then diffs it into an append, or a
                            // trim plus an append for a sliding tail; replacing the slot object would record the whole
                            // window on every commit.
                            let current = match slot.get("output")? {
                                Some(DraftItem::Value(value)) => value.as_str().map(str::to_owned),
                                Some(DraftItem::Draft(_)) | None => None,
                            };
                            if current.as_deref().unwrap_or("") != text {
                                slot.set("output", text.as_str())?;
                            }
                            if snapshot.dropped_bytes > 0 {
                                slot.set("droppedBytes", to_json(&snapshot.dropped_bytes)?)?;
                            }
                            if snapshot.dropped_lines > 0 {
                                slot.set("droppedLines", to_json(&snapshot.dropped_lines)?)?;
                            }
                            // Diff details leaf by leaf and append new diagnostics, so each commit writes only what
                            // changed.
                            if details_changed {
                                if let Some(details) = &commit_details {
                                    assign_json(&slot, "details", details)?;
                                }
                            }
                            if !added.is_empty() {
                                if slot.get("diagnostics")?.is_none() {
                                    slot.set("diagnostics", JsonValue::array())?;
                                }
                                let items =
                                    added.iter().map(to_json).collect::<Result<Vec<_>, _>>()?;
                                slot.child("diagnostics")?.push(items)?;
                            }
                            Ok(None)
                        },
                        &cx,
                    )
                    .await?;
                *written.lock().unwrap_or_else(PoisonError::into_inner) = Written {
                    text: snapshot.text,
                    details,
                    diagnostics: diagnostics.len(),
                };
                Ok(bytes)
            }
            .boxed()
        }),
        Box::new(move |error| {
            // Rejections after an abort mark or close are expected; the committed state stays consistent.
            if !report_runtime.signal().aborted() {
                // After the invocation ended there is nobody left to report to; TS throws into an unobserved promise.
                let _ended = report_runtime.report(error);
            }
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

    fn diagnostic(&self, diagnostic: ToolDiagnostic) -> SessionResult<()> {
        self.reporting.assert_live()?;
        self.reporting.lock().diagnostics.push(diagnostic);
        self.reporting.progress.mark();
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

#[expect(
    clippy::cast_possible_truncation,
    reason = "tool output limits fit in usize"
)]
fn limit(value: Option<u64>, default: u64) -> usize {
    value.unwrap_or(default) as usize
}

/// The output limits of `tool`, the invocation's reporting state, and the
/// output window a shell may skip outside of.
fn reporting_for(
    runtime: &Runtime,
    input: &ToolTaskInput,
    call: &ToolHookCall,
    tool: &ToolRegistration,
    cx: &Context,
) -> (OutputLimits, Arc<Reporting>, Option<ShellOutputWindow>) {
    let configured = tool.output_limits.unwrap_or_default();
    let limits = OutputLimits {
        max_bytes: limit(configured.max_bytes, DEFAULT_MAX_BYTES),
        max_lines: limit(configured.max_lines, DEFAULT_MAX_LINES),
        retain: configured.retain.unwrap_or(OutputRetain::Head),
    };
    let reported = Arc::new(Mutex::new(Reported {
        output: OutputBuffer::new(limits),
        diagnostics: Vec::new(),
        details: None,
    }));
    let streams = match input {
        ToolTaskInput::Model { .. } => true,
        ToolTaskInput::Nested { progress, .. } => *progress != Some(false),
    };
    let reporting = Arc::new(Reporting {
        progress: publish_progress(runtime, &reported, streams, cx),
        reported,
        ended: AtomicBool::new(false),
        call_id: call.id.clone(),
        admissions: Mutex::new(Vec::new()),
        sequence: AtomicU64::new(0),
    });
    let output_window = match limits.retain {
        OutputRetain::Tail => Some(ShellOutputWindow {
            max_bytes: limits.max_bytes as u64,
            max_lines: limits.max_lines as u64,
            min_interval_ms: runtime.settings().progress.output_interval_ms,
            bytes_per_second: PROGRESS_BYTES_PER_SECOND,
        }),
        OutputRetain::Head => None,
    };
    (limits, reporting, output_window)
}

/// Execute with the resolved implementation, then settle its result.
pub(super) async fn run(
    runtime: &Runtime,
    input: &ToolTaskInput,
    call: &ToolHookCall,
    tool: &ToolRegistration,
    args: PiJsonObject,
    cx: &Context,
) -> SessionResult<()> {
    let (limits, reporting, output_window) = reporting_for(runtime, input, call, tool, cx);

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
    // Details still waiting for a progress commit settle with the terminal commit, the final flush.
    let pending = reporting.progress.stop().await;
    let settled = async {
        let settled =
            final_result(runtime, input, call, tool, result, &reporting, limits, cx).await?;
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
    clippy::too_many_arguments,
    reason = "one TS function over the invocation's state"
)]
async fn final_result(
    runtime: &Runtime,
    input: &ToolTaskInput,
    call: &ToolHookCall,
    tool: &ToolRegistration,
    result: ToolExecutionResult,
    reporting: &Reporting,
    limits: OutputLimits,
    cx: &Context,
) -> SessionResult<ToolExecutionResult> {
    let mut harness = Vec::new();
    let (retained, reported_details, reported_diagnostics) = {
        let mut state = reporting.lock();
        let retained = result.output.is_none().then(|| state.output.snapshot());
        (retained, state.details.clone(), state.diagnostics.clone())
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
    let initial = ToolExecutionResult {
        output: Some(output.clone()),
        details: result.details.clone().or(reported_details),
        diagnostics: Some(diagnostics),
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
    // The retained output's truncation applies only while afterTool kept that output.
    if let Some(retained) = &retained {
        if retained.dropped_bytes > 0 && last.output.as_ref() == Some(&output) {
            harness.push(truncated(
                retained.dropped_lines as u64,
                retained.dropped_bytes as u64,
                Some(limits.retain),
            ));
        }
    }
    let bounded = bound_content(last.output.clone().unwrap_or_default(), &limits);
    if bounded.dropped_bytes > 0 {
        harness.push(truncated(
            bounded.dropped_lines as u64,
            bounded.dropped_bytes as u64,
            Some(limits.retain),
        ));
    }
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
        last.structured_output = Some(output_value(&bounded.content)?);
    }
    let mut diagnostics = last.diagnostics.clone().unwrap_or_default();
    diagnostics.extend(harness);
    Ok(ToolExecutionResult {
        output: Some(bounded.content),
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
