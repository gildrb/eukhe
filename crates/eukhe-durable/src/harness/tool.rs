//! The built-in tool task (`harness/tool.ts`, spec §7.3): resolves the called
//! tool among its phase agent's tools, validates, runs `before_tool`, records
//! intent, executes, runs `after_tool`, and settles the result. A
//! model-issued call settles by appending its result entry; a nested call, one
//! a running tool made through `execute_tool()`, by writing its result to its
//! caller's [`NESTED_RESULT_DOC`].

mod invocation;
mod nested;
mod result;
#[cfg(test)]
mod tests;

use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_pi_ai::utils::validation::validate_tool_arguments;
use eukhe_types::pi_ai::{
    AssistantContentBlock, JsonObject as PiJsonObject, JsonValue as PiJsonValue, Message, ToolCall,
};
use serde::de::Error as _;
use serde::ser::SerializeMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use self::invocation::run;
use self::nested::{json_equal, nested_result, summary_of, NestedCalls, NESTED_CALLS_DOC};
pub use self::nested::{NestedResultState, NESTED_RESULT_DOC};
pub use self::result::{append_tool_result, harness_error, ToolResultMeta};
use self::result::{from_slot, ToolEnding};
use super::live::{
    clear_progress, finish_slot, is_nested_slot, remove_nested_slots, tool_slot, SlotProgress,
    LIVE_DOC,
};
use super::types::{
    ToolCallParent, ToolControl, ToolExecutionResult, ToolHookCall, ToolHooks, ToolRegistration,
    ToolReplay,
};
use super::usage::{record_usage, UsageBucket};
use crate::entries::ASSISTANT_ENTRY;
use crate::session::{SessionError, SessionResult};
use crate::tasks::{
    define_task, Migrated, NextTaskState, RunningTask, Task, TaskDefinition, TaskRuntime,
};
use crate::types::{
    DocumentReaderExt, EntryId, TaskAbortReason, TaskId, TaskOutcome, TaskOutcomeError,
};

/// A model-issued call, read from its assistant entry, or a nested call a
/// running tool made through `execute_tool()`, whose call the input carries
/// because no entry holds it.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "camelCase",
    rename_all_fields = "camelCase"
)]
pub enum ToolTaskInput {
    /// `{ kind: "model", assistant, callId }`.
    Model { assistant: EntryId, call_id: String },
    /// `{ kind: "nested", parent, parentCallId, key, call, progress? }`.
    Nested {
        parent: TaskId,
        parent_call_id: String,
        key: String,
        call: ToolCall,
        /// `Some(false)`: commit no running output, details, or diagnostics
        /// to the slot; the result still gets them. TS `progress?: false`.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        progress: Option<bool>,
    },
}

/// Checkpoint of a tool task.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
pub enum ToolTaskCheckpoint {
    Call,
    /// Durable intent: the final arguments and the replay policy recorded
    /// before execution.
    Execute {
        arguments: PiJsonObject,
        replay: ToolReplay,
    },
}

/// Result of a tool task. A model-issued call's result is its transcript
/// entry; a nested call's result is in its caller's [`NESTED_RESULT_DOC`],
/// so the receipt stays small and the result retires with the caller. A
/// version 1 task that was already holding its outcome as `completing` when
/// the Harness upgraded finishes with a version 1 result, `{ entryId,
/// control? }` without `kind`, which reads as a model-issued call's.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ToolTaskResult {
    /// `{ kind: "model", entryId, control? }`.
    Model {
        entry_id: EntryId,
        control: Option<ToolControl>,
    },
    /// `{ kind: "nested" }`.
    Nested,
}

impl Serialize for ToolTaskResult {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut map = serializer.serialize_map(None)?;
        match self {
            Self::Model { entry_id, control } => {
                map.serialize_entry("kind", "model")?;
                map.serialize_entry("entryId", entry_id)?;
                if let Some(control) = control {
                    map.serialize_entry("control", control)?;
                }
            }
            Self::Nested => map.serialize_entry("kind", "nested")?,
        }
        map.end()
    }
}

/// The wire shape of every [`ToolTaskResult`] version.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ToolTaskResultWire {
    #[serde(default)]
    kind: Option<String>,
    #[serde(default)]
    entry_id: Option<EntryId>,
    #[serde(default)]
    control: Option<ToolControl>,
}

impl<'de> Deserialize<'de> for ToolTaskResult {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire = ToolTaskResultWire::deserialize(deserializer)?;
        match wire.kind.as_deref() {
            Some("nested") => Ok(Self::Nested),
            // Version 1 results have no kind; they are model-issued calls'.
            None | Some("model") => Ok(Self::Model {
                entry_id: wire
                    .entry_id
                    .ok_or_else(|| D::Error::missing_field("entryId"))?,
                control: wire.control,
            }),
            Some(other) => Err(D::Error::unknown_variant(other, &["model", "nested"])),
        }
    }
}

/// The version 1 input: a model-issued call.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ToolTaskInputV1 {
    assistant: EntryId,
    call_id: String,
}

/// The tool task's type (TS `typeof ToolTask`).
pub type ToolTask = Task<ToolTaskInput, ToolTaskCheckpoint, ToolTaskResult, ToolHooks>;

type Runtime = TaskRuntime<ToolTaskInput, ToolTaskCheckpoint, ToolTaskResult, ToolHooks>;
type Running = RunningTask<ToolTaskInput, ToolTaskCheckpoint, ToolTaskResult>;

/// Built-in tool task: resolves the called tool among its phase agent's
/// tools, validates, runs `before_tool`, records intent, executes, runs
/// `after_tool`, and settles the result, all in one `call` handler so
/// nothing separates resolution from settlement. `execute` is reached only
/// by recovery and applies the replay rule. A model-issued call settles by
/// appending its result entry; a nested call by writing its result to its
/// caller's `NestedResultDoc`.
pub static TOOL_TASK: LazyLock<ToolTask> = LazyLock::new(|| {
    define_task(
        TaskDefinition::new(
            "pi.tool",
            2,
            |_input: &ToolTaskInput| Ok(ToolTaskCheckpoint::Call),
            abort,
        )
        // Version 1 had only model-issued calls.
        .migrate(|input, checkpoint, _version| {
            let ToolTaskInputV1 { assistant, call_id } = from_json(input)?;
            Ok(Migrated {
                input: ToolTaskInput::Model { assistant, call_id },
                checkpoint: from_json(checkpoint)?,
            })
        })
        .phase("call", call)
        .phase("execute", execute),
    )
});

async fn call(task: Running, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let input = task.input;
    let call = read_call(&runtime, &input, &cx).await?;
    let Some(tool) = resolve_tool(&runtime, &input, &call.name, &cx).await? else {
        let error = harness_error(
            "tool_unavailable",
            &format!("Tool {} is not available", call.name),
        );
        return complete(&runtime, &input, &call, error, &cx).await;
    };
    let checked =
        prepare(&tool, call.arguments.clone()).and_then(|args| validate(&tool, &call, args));
    let args = match checked {
        Ok(args) => args,
        Err(error) => return complete(&runtime, &input, &call, invalid(&error), &cx).await,
    };
    let (args, block) = before_tool(&runtime, &call, args, &cx).await?;
    if let Some(block) = block {
        let blocked = harness_error("blocked", &format!("Tool call blocked: {block}"));
        return complete(&runtime, &input, &call, blocked, &cx).await;
    }
    let args = match validate(&tool, &call, args) {
        Ok(args) => args,
        Err(error) => return complete(&runtime, &input, &call, invalid(&error), &cx).await,
    };
    let conversation_id = runtime.conversation_id();
    let task_id = runtime.task_id().erase();
    let intent = ToolTaskCheckpoint::Execute {
        arguments: args.clone(),
        replay: tool.replay.unwrap_or(ToolReplay::Unsafe),
    };
    // A nested slot shows the arguments the call runs with, which repair,
    // hooks, and coercion may have changed. Compared with the input, which
    // the slot got at admission: reading the draft would track every leaf.
    let changed = match &input {
        ToolTaskInput::Nested { call, .. } => (!json_equal(
            &PiJsonValue::Object(call.arguments.clone()),
            &PiJsonValue::Object(args.clone()),
        ))
        .then(|| to_json(&args))
        .transpose()?,
        ToolTaskInput::Model { .. } => None,
    };
    runtime
        .commit(
            move |tx, _current| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                if let Some(slot) = tool_slot(&live, task_id)? {
                    slot.set("status", "running")?;
                    if let Some(arguments) = changed {
                        if is_nested_slot(&slot)? {
                            slot.set("arguments", arguments)?;
                        }
                    }
                }
                Ok(Some(NextTaskState::Running { checkpoint: intent }))
            },
            &cx,
        )
        .await?;
    run(&runtime, &input, &call, &tool, args, &cx).await
}

/// Recovery after intent: rerun only when the stored and the current policy
/// both say `safe`.
async fn execute(task: Running, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let ToolTaskCheckpoint::Execute { arguments, replay } = task.checkpoint else {
        return Err(SessionError::error(
            "Tool task execute phase without intent",
        ));
    };
    let input = task.input;
    let call = read_call(&runtime, &input, &cx).await?;
    let tool = resolve_tool(&runtime, &input, &call.name, &cx).await?;
    if let Some(tool) =
        tool.filter(|tool| replay == ToolReplay::Safe && tool.replay == Some(ToolReplay::Safe))
    {
        // The rerun reports from scratch; clear what the interrupted attempt published.
        let conversation_id = runtime.conversation_id();
        let task_id = runtime.task_id().erase();
        runtime
            .commit(
                move |tx, _current| async move {
                    let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                    if let Some(slot) = tool_slot(&live, task_id)? {
                        clear_progress(&slot)?;
                    }
                    Ok(None)
                },
                &cx,
            )
            .await?;
        return run(&runtime, &input, &call, &tool, arguments, &cx).await;
    }
    let message = format!(
        "Tool {} was interrupted and may have partially run",
        call.name
    );
    // `failed` records cancellation intent, so the call's owned conversations, left unsupervised, are aborted.
    let ending = ToolEnding::Failed {
        message: message.clone(),
    };
    settle(
        &runtime,
        &input,
        &call,
        ending,
        move |slot| from_slot(slot, "interrupted", &message),
        &cx,
        None,
    )
    .await
}

async fn abort(task: Running, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let call = read_call(&runtime, &task.input, &cx).await?;
    // Abandoned after a restart (`TaskOptions.abandon_on_restart`): say whether the call may have run.
    let (code, message) = if task.abort_reason != Some(TaskAbortReason::Restart) {
        ("aborted", format!("Tool {} was aborted", call.name))
    } else if matches!(task.checkpoint, ToolTaskCheckpoint::Execute { .. }) {
        (
            "interrupted",
            format!(
                "Tool {} was interrupted by a restart and may have partially run",
                call.name
            ),
        )
    } else {
        (
            "abandoned",
            format!(
                "Tool {} was not started: its caller ended with a restart",
                call.name
            ),
        )
    };
    settle(
        &runtime,
        &task.input,
        &call,
        ToolEnding::Aborted,
        move |slot| from_slot(slot, code, &message),
        &cx,
        None,
    )
    .await
}

/// The called tool: among the tools the model is offered for a model-issued
/// call, else among those tools may call.
async fn resolve_tool(
    runtime: &Runtime,
    input: &ToolTaskInput,
    name: &str,
    cx: &Context,
) -> SessionResult<Option<Arc<ToolRegistration>>> {
    let agent = runtime.agent(cx).await?;
    let tools = match input {
        ToolTaskInput::Model { .. } => &agent.tools,
        ToolTaskInput::Nested { .. } => &agent.callable,
    };
    Ok(tools.iter().find(|tool| tool.name == name).cloned())
}

/// The call: from the input for a nested call, which hooks see with its
/// parent, else the tool call `call_id` of the assistant entry.
async fn read_call(
    runtime: &Runtime,
    input: &ToolTaskInput,
    cx: &Context,
) -> SessionResult<ToolHookCall> {
    let (assistant, call_id) = match input {
        ToolTaskInput::Nested {
            parent,
            parent_call_id,
            call,
            ..
        } => {
            return Ok(ToolHookCall {
                call: call.clone(),
                parent: Some(ToolCallParent {
                    task_id: *parent,
                    call_id: parent_call_id.clone(),
                }),
            })
        }
        ToolTaskInput::Model { assistant, call_id } => (*assistant, call_id),
    };
    let entry = runtime.typed_entry(&ASSISTANT_ENTRY, assistant, cx).await?;
    let call = entry.and_then(
        |entry| match entry.into_entry().model?.into_iter().next()? {
            Message::Assistant(message) => {
                message
                    .content
                    .into_iter()
                    .find_map(|content| match content {
                        AssistantContentBlock::ToolCall(call) if call.id == *call_id => Some(call),
                        AssistantContentBlock::ToolCall(_)
                        | AssistantContentBlock::Text(_)
                        | AssistantContentBlock::Thinking(_) => None,
                    })
            }
            Message::System(_) | Message::User(_) | Message::ToolResult(_) => None,
        },
    );
    let call = call.ok_or_else(|| {
        SessionError::error(format!("Entry {assistant} has no tool call {call_id}"))
    })?;
    Ok(ToolHookCall { call, parent: None })
}

/// The call's arguments as repaired by the tool; a failing repair makes them
/// invalid (the error is why).
fn prepare(tool: &ToolRegistration, args: PiJsonObject) -> Result<PiJsonObject, String> {
    let Some(prepare_arguments) = &tool.prepare_arguments else {
        return Ok(args);
    };
    match prepare_arguments(PiJsonValue::Object(args)) {
        Ok(PiJsonValue::Object(args)) => Ok(args),
        // TS casts the repaired value; validation then rejects a non-object.
        Ok(other) => Err(not_an_object(&other)),
        Err(error) => Err(error.to_string()),
    }
}

/// Arguments validated and coerced against the implementation's schema.
fn validate(
    tool: &ToolRegistration,
    call: &ToolCall,
    args: PiJsonObject,
) -> Result<PiJsonObject, String> {
    let mut probe = call.clone();
    probe.arguments = args;
    match validate_tool_arguments(&tool.tool(), &probe) {
        Ok(PiJsonValue::Object(args)) => Ok(args),
        Ok(other) => Err(not_an_object(&other)),
        Err(error) => Err(error.to_string()),
    }
}

/// Repaired or coerced arguments that are not an object.
fn not_an_object(value: &PiJsonValue) -> String {
    format!("Tool arguments must be an object, got {value}")
}

fn invalid(message: &str) -> ToolExecutionResult {
    harness_error("invalid_arguments", message)
}

/// Settle a call that never executed with the Harness's own `result`.
async fn complete(
    runtime: &Runtime,
    input: &ToolTaskInput,
    call: &ToolHookCall,
    result: ToolExecutionResult,
    cx: &Context,
) -> SessionResult<()> {
    settle(
        runtime,
        input,
        call,
        ToolEnding::Completed,
        |_| result,
        cx,
        None,
    )
    .await
}

/// Run every `before_tool` hook: the first `block` wins, otherwise
/// `arguments` replace the call's arguments; a hook error blocks unless the
/// invocation is signalled.
async fn before_tool(
    runtime: &Runtime,
    call: &ToolHookCall,
    args: PiJsonObject,
    cx: &Context,
) -> SessionResult<(PiJsonObject, Option<String>)> {
    let state = Arc::new(Mutex::new((args, None::<String>)));
    let hook_api = runtime.hook_api();
    let signal = runtime.signal();
    runtime
        .hooks()
        .each(
            |hooks: &ToolHooks| hooks.before_tool.clone(),
            |hook| {
                let state = Arc::clone(&state);
                let hook_api = hook_api.clone();
                let signal = signal.clone();
                let mut probe = call.clone();
                let cx = cx.clone();
                async move {
                    {
                        let current = state.lock().unwrap_or_else(PoisonError::into_inner);
                        if current.1.is_some() {
                            return Ok(());
                        }
                        probe.call.arguments = current.0.clone();
                    }
                    let decision = hook(&probe, &hook_api, &cx).await;
                    let mut current = state.lock().unwrap_or_else(PoisonError::into_inner);
                    match decision {
                        Ok(Some(decision)) => {
                            if let Some(block) = decision.block {
                                current.1 = Some(block);
                            } else if let Some(arguments) = decision.arguments {
                                current.0 = arguments;
                            }
                        }
                        Ok(None) => {}
                        Err(error) => {
                            if signal.aborted() {
                                return Err(error);
                            }
                            current.1 = Some(error.to_string());
                        }
                    }
                    Ok(())
                }
            },
        )
        .await?;
    let (args, block) = std::mem::take(&mut *state.lock().unwrap_or_else(PoisonError::into_inner));
    Ok((args, block))
}

/// Commit the tool's terminal state and mark its slot done. A model-issued
/// call appends its result entry and ends with the entry ID; a nested call
/// writes its result to the caller's `NestedResultDoc`, records its usage,
/// and ends with a small receipt. Nested calls this call left running are
/// aborted first, so they report into their slots before the slots below the
/// call leave `pi.live`. `build` receives the slot's published progress so
/// interruption and abort can report the durable partial output.
async fn settle<B>(
    runtime: &Runtime,
    input: &ToolTaskInput,
    call: &ToolHookCall,
    ending: ToolEnding,
    build: B,
    cx: &Context,
    duration_ms: Option<u64>,
) -> SessionResult<()>
where
    B: FnOnce(Option<&SlotProgress>) -> ToolExecutionResult + Send + 'static,
{
    let conversation_id = runtime.conversation_id();
    let task_id = runtime.task_id().erase();
    // A crash in between leaves the call in `execute`: a safe rerun reattaches to the calls, an interruption ends here.
    let index = match runtime.snapshot(&NESTED_CALLS_DOC, task_id, cx).await? {
        Some(index) => from_json::<NestedCalls>(&JsonValue::Object(index))?,
        None => NestedCalls::default(),
    };
    let mut nested_ids: Vec<TaskId> = index.calls.into_values().collect();
    nested_ids.sort_unstable();
    // Mark them all before waiting for any: one may run until a sibling is cancelled.
    futures::future::try_join_all(nested_ids.iter().map(|id| runtime.abort_owned(*id, cx))).await?;
    let input = input.clone();
    let call = call.clone();
    let clock = runtime.clone();
    runtime
        .commit(
            move |tx, _current| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                let slot = tool_slot(&live, task_id)?;
                let progress = match &slot {
                    Some(slot) => Some(from_json::<SlotProgress>(&slot.value()?)?),
                    None => None,
                };
                let result = build(progress.as_ref());
                let settled = match &input {
                    ToolTaskInput::Nested { parent, key, .. } => {
                        let nested = nested_result(task_id, &result, duration_ms);
                        if let Some(usage) = &nested.usage {
                            record_usage(
                                &tx,
                                conversation_id,
                                UsageBucket::Tools,
                                &call.name,
                                usage,
                            )
                            .await?;
                        }
                        // The caller is never terminal before its owned nested calls; a missing entry is a bug, not
                        // a race.
                        let index = tx.doc(&NESTED_CALLS_DOC, *parent).await?;
                        let listed = from_json::<NestedCalls>(&index.value()?)?
                            .calls
                            .get(key)
                            .copied();
                        if listed != Some(task_id) {
                            return Err(SessionError::error(format!(
                                "Nested call {} is not in its caller's index",
                                call.id
                            )));
                        }
                        let stored = NestedResultState {
                            result: nested.clone(),
                        };
                        tx.doc_member(&NESTED_RESULT_DOC, (*parent, &task_id.to_string()), &stored)
                            .await?;
                        if let Some(slot) = &slot {
                            if is_nested_slot(slot)? {
                                finish_slot(slot)?;
                                let output = result.output.as_deref().unwrap_or_default();
                                slot.set("summary", to_json(&summary_of(&nested, output))?)?;
                            }
                        }
                        ToolTaskResult::Nested
                    }
                    ToolTaskInput::Model { .. } => {
                        let meta = ToolResultMeta {
                            timestamp: clock.now()?,
                            duration_ms,
                        };
                        let entry =
                            append_tool_result(&tx, conversation_id, &call, &result, meta).await?;
                        if let Some(slot) = &slot {
                            if !is_nested_slot(slot)? {
                                finish_slot(slot)?;
                                slot.set("entry", to_json(&entry.id)?)?;
                            }
                        }
                        let control = match ending {
                            ToolEnding::Completed => result.control.clone(),
                            ToolEnding::Aborted | ToolEnding::Failed { .. } => None,
                        };
                        ToolTaskResult::Model {
                            entry_id: entry.id,
                            control,
                        }
                    }
                };
                // A call that made no nested calls has no slots below it; skipping the scan keeps many leaves linear.
                if !nested_ids.is_empty() {
                    remove_nested_slots(&live, task_id)?;
                }
                Ok(Some(NextTaskState::Terminal {
                    outcome: outcome_of(ending, settled),
                }))
            },
            cx,
        )
        .await
}

/// The terminal outcome of a call that ended as `ending` with `settled`.
fn outcome_of(ending: ToolEnding, settled: ToolTaskResult) -> TaskOutcome<ToolTaskResult> {
    match ending {
        ToolEnding::Aborted => TaskOutcome::Aborted {
            reason: None,
            result: Some(settled),
        },
        ToolEnding::Failed { message } => TaskOutcome::Failed {
            error: TaskOutcomeError {
                message,
                detail: None,
            },
            result: Some(settled),
        },
        ToolEnding::Completed => TaskOutcome::Completed { result: settled },
    }
}

/// `JSON.stringify` length of a value, in UTF-8 bytes.
fn json_bytes(value: &JsonValue) -> usize {
    value.to_string().len()
}
