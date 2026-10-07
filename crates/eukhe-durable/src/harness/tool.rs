//! The built-in tool task (`harness/tool.ts`, spec §7.3): resolves the called
//! tool among its phase agent's tools, validates, runs `before_tool`, records
//! intent, executes, runs `after_tool`, and appends the result.

mod invocation;
mod result;
#[cfg(test)]
mod tests;

use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_pi_ai::utils::validation::validate_tool_arguments;
use eukhe_types::pi_ai::{
    AssistantContentBlock, JsonObject as PiJsonObject, JsonValue as PiJsonValue, Message, ToolCall,
};
use serde::{Deserialize, Serialize};

use self::invocation::run;
pub use self::result::{append_tool_result, harness_error};
use self::result::{from_slot, ToolEnding};
use super::live::{clear_progress, finish_slot, tool_slot, ToolSlot, LIVE_DOC};
use super::types::{ToolControl, ToolExecutionResult, ToolHooks, ToolRegistration, ToolReplay};
use crate::entries::ASSISTANT_ENTRY;
use crate::session::{SessionError, SessionResult};
use crate::tasks::{define_task, NextTaskState, RunningTask, Task, TaskDefinition, TaskRuntime};
use crate::types::{EntryId, TaskOutcome, TaskOutcomeError};

/// Input of a tool task: the assistant entry and the ID of its tool call.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ToolTaskInput {
    pub assistant: EntryId,
    pub call_id: String,
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

/// Result of a tool task: its result entry and the controls the result
/// requested.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ToolTaskResult {
    pub entry_id: EntryId,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub control: Option<ToolControl>,
}

/// The tool task's type (TS `typeof ToolTask`).
pub type ToolTask = Task<ToolTaskInput, ToolTaskCheckpoint, ToolTaskResult, ToolHooks>;

type Runtime = TaskRuntime<ToolTaskInput, ToolTaskCheckpoint, ToolTaskResult, ToolHooks>;
type Running = RunningTask<ToolTaskInput, ToolTaskCheckpoint, ToolTaskResult>;

/// Built-in tool task: resolves the called tool among its phase agent's
/// tools, validates, runs `before_tool`, records intent, executes, runs
/// `after_tool`, and appends the result, all in one `call` handler so nothing
/// separates resolution from settlement. `execute` is reached only by
/// recovery and applies the replay rule.
pub static TOOL_TASK: LazyLock<ToolTask> = LazyLock::new(|| {
    define_task(
        TaskDefinition::new(
            "pi.tool",
            1,
            |_input: &ToolTaskInput| Ok(ToolTaskCheckpoint::Call),
            abort,
        )
        .phase("call", call)
        .phase("execute", execute),
    )
});

async fn call(task: Running, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let call = read_call(&runtime, &task.input, &cx).await?;
    let Some(tool) = find_tool(&runtime, &call.name, &cx).await? else {
        let error = harness_error(
            "tool_unavailable",
            &format!("Tool {} is not available", call.name),
        );
        return settle(&runtime, &call, ToolEnding::Completed, |_| error, &cx).await;
    };
    let checked =
        prepare(&tool, call.arguments.clone()).and_then(|args| validate(&tool, &call, args));
    let args = match checked {
        Ok(args) => args,
        Err(error) => {
            return settle(
                &runtime,
                &call,
                ToolEnding::Completed,
                move |_| invalid(&error),
                &cx,
            )
            .await
        }
    };
    let (args, block) = before_tool(&runtime, &call, args, &cx).await?;
    if let Some(block) = block {
        let blocked = harness_error("blocked", &format!("Tool call blocked: {block}"));
        return settle(&runtime, &call, ToolEnding::Completed, |_| blocked, &cx).await;
    }
    let args = match validate(&tool, &call, args) {
        Ok(args) => args,
        Err(error) => {
            return settle(
                &runtime,
                &call,
                ToolEnding::Completed,
                move |_| invalid(&error),
                &cx,
            )
            .await
        }
    };
    let conversation_id = runtime.conversation_id();
    let task_id = runtime.task_id().erase();
    let intent = ToolTaskCheckpoint::Execute {
        arguments: args.clone(),
        replay: tool.replay.unwrap_or(ToolReplay::Unsafe),
    };
    runtime
        .commit(
            move |tx, _current| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                if let Some(slot) = tool_slot(&live, task_id)? {
                    slot.set("status", "running")?;
                }
                Ok(Some(NextTaskState::Running { checkpoint: intent }))
            },
            &cx,
        )
        .await?;
    run(&runtime, &call, &tool, args, &cx).await
}

/// Recovery after intent: rerun only when the stored and the current policy
/// both say `safe`.
async fn execute(task: Running, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let ToolTaskCheckpoint::Execute { arguments, replay } = task.checkpoint else {
        return Err(SessionError::error(
            "Tool task execute phase without intent",
        ));
    };
    let call = read_call(&runtime, &task.input, &cx).await?;
    let tool = find_tool(&runtime, &call.name, &cx).await?;
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
        return run(&runtime, &call, &tool, arguments, &cx).await;
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
        &call,
        ending,
        move |slot| from_slot(slot, "interrupted", &message),
        &cx,
    )
    .await
}

async fn abort(task: Running, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let call = read_call(&runtime, &task.input, &cx).await?;
    let message = format!("Tool {} was aborted", call.name);
    settle(
        &runtime,
        &call,
        ToolEnding::Aborted,
        move |slot| from_slot(slot, "aborted", &message),
        &cx,
    )
    .await
}

/// The tool call `call_id` of the assistant entry.
async fn read_call(
    runtime: &Runtime,
    input: &ToolTaskInput,
    cx: &Context,
) -> SessionResult<ToolCall> {
    let entry = runtime
        .typed_entry(&ASSISTANT_ENTRY, input.assistant, cx)
        .await?;
    let call = entry.and_then(
        |entry| match entry.into_entry().model?.into_iter().next()? {
            Message::Assistant(message) => {
                message
                    .content
                    .into_iter()
                    .find_map(|content| match content {
                        AssistantContentBlock::ToolCall(call) if call.id == input.call_id => {
                            Some(call)
                        }
                        AssistantContentBlock::ToolCall(_)
                        | AssistantContentBlock::Text(_)
                        | AssistantContentBlock::Thinking(_) => None,
                    })
            }
            Message::System(_) | Message::User(_) | Message::ToolResult(_) => None,
        },
    );
    call.ok_or_else(|| {
        SessionError::error(format!(
            "Entry {} has no tool call {}",
            input.assistant, input.call_id
        ))
    })
}

/// The called tool among the phase agent's tools.
async fn find_tool(
    runtime: &Runtime,
    name: &str,
    cx: &Context,
) -> SessionResult<Option<Arc<ToolRegistration>>> {
    let agent = runtime.agent(cx).await?;
    Ok(agent.tools.iter().find(|tool| tool.name == name).cloned())
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

/// Run every `before_tool` hook: the first `block` wins, otherwise
/// `arguments` replace the call's arguments; a hook error blocks unless the
/// invocation is signalled.
async fn before_tool(
    runtime: &Runtime,
    call: &ToolCall,
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
                        probe.arguments = current.0.clone();
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

/// Commit the tool's terminal state: append its result entry, mark its slot
/// done, and complete or end with the entry ID. `build` receives the slot so
/// interruption and abort can report the durable partial output.
async fn settle<B>(
    runtime: &Runtime,
    call: &ToolCall,
    ending: ToolEnding,
    build: B,
    cx: &Context,
) -> SessionResult<()>
where
    B: FnOnce(Option<&ToolSlot>) -> ToolExecutionResult + Send + 'static,
{
    let conversation_id = runtime.conversation_id();
    let task_id = runtime.task_id().erase();
    let call = call.clone();
    let clock = runtime.clone();
    runtime
        .commit(
            move |tx, _current| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                let slot = tool_slot(&live, task_id)?;
                let value = match &slot {
                    Some(slot) => Some(from_json::<ToolSlot>(&slot.value()?)?),
                    None => None,
                };
                let result = build(value.as_ref());
                let entry =
                    append_tool_result(&tx, conversation_id, &call, &result, clock.now()?).await?;
                let entry_id = entry.id;
                if let Some(slot) = &slot {
                    finish_slot(slot, Some(entry_id))?;
                }
                let outcome = match ending {
                    ToolEnding::Aborted => TaskOutcome::Aborted {
                        reason: None,
                        result: Some(ToolTaskResult {
                            entry_id,
                            control: None,
                        }),
                    },
                    ToolEnding::Failed { message } => TaskOutcome::Failed {
                        error: TaskOutcomeError {
                            message,
                            detail: None,
                        },
                        result: Some(ToolTaskResult {
                            entry_id,
                            control: None,
                        }),
                    },
                    ToolEnding::Completed => TaskOutcome::Completed {
                        result: ToolTaskResult {
                            entry_id,
                            control: result.control,
                        },
                    },
                };
                Ok(Some(NextTaskState::Terminal { outcome }))
            },
            cx,
        )
        .await
}

/// `JSON.stringify` length of a value, in UTF-8 bytes.
fn json_bytes(value: &JsonValue) -> usize {
    value.to_string().len()
}
