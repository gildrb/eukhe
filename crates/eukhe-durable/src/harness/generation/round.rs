//! Final answers and tool rounds of `pi.generation` (TS `answer`,
//! `startToolRound`, `finishToolRound`, the sequential `tools` phase,
//! `readCalls`, `createToolTask`).

use std::collections::HashSet;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::delta::DraftItem;
use eukhe_chord::json::{from_json, to_json};
use eukhe_pi_ai::utils::transcript::get_current_tools;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Message, ToolCall, UserContent, UserMessage,
};

use super::{GenerationCheckpoint, GenerationResult, Next, Request, Runtime};
use crate::entries::{ASSISTANT_ENTRY, RESET_ENTRY, USER_ENTRY};
use crate::harness::agent::add_tools;
use crate::harness::inbox::{apply_boundary, prepare_boundary, BoundaryAt, QueueModes};
use crate::harness::live::run::{
    append_assistant, create_generation, hand_over, start_run, timestamp,
};
use crate::harness::live::{child_draft, end_run, run_task_id, ToolSlot, ToolSlotStatus, LIVE_DOC};
use crate::harness::tool::{
    append_tool_result, harness_error, ToolResultMeta, ToolTaskInput, ToolTaskResult,
};
use crate::harness::types::{
    ContextOptions, GenerationHooks, ToolControl, ToolExecutionMode, UserInput,
};
use crate::session::{SessionResult, Tx};
use crate::tasks::AnyTask;
use crate::types::{
    DocumentReaderExt, EntryHead, EntryId, JoinPolicy, SubmissionSettlement, TaskId, TaskOptions,
    TaskOutcome, TaskOwnership, TypedEntryDraft,
};

fn queue_modes(runtime: &Runtime) -> QueueModes {
    let settings = runtime.settings();
    QueueModes {
        steering_mode: settings.steering_mode,
        follow_up_mode: settings.follow_up_mode,
    }
}

fn completed(entry_id: EntryId) -> Next {
    Next::Terminal {
        outcome: TaskOutcome::Completed {
            result: GenerationResult { entry_id },
        },
    }
}

/// The calls `call_ids` of the assistant entry, in the given order.
pub(super) async fn read_calls(
    runtime: &Runtime,
    assistant: EntryId,
    call_ids: &[String],
    cx: &Context,
) -> SessionResult<Vec<ToolCall>> {
    let entry = runtime.typed_entry(&ASSISTANT_ENTRY, assistant, cx).await?;
    let message = entry.and_then(|entry| {
        entry
            .model
            .as_ref()
            .and_then(|model| model.first().cloned())
    });
    let calls: Vec<ToolCall> = match message {
        Some(Message::Assistant(message)) => tool_calls(&message),
        Some(Message::System(_) | Message::User(_) | Message::ToolResult(_)) | None => Vec::new(),
    };
    Ok(call_ids
        .iter()
        .filter_map(|id| calls.iter().find(|call| &call.id == id).cloned())
        .collect())
}

fn tool_calls(message: &AssistantMessage) -> Vec<ToolCall> {
    message
        .content
        .iter()
        .filter_map(|content| match content {
            AssistantContentBlock::ToolCall(call) => Some(call.clone()),
            AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
        })
        .collect()
}

/// A tool task for call `call_id`, owned by the generation.
async fn create_tool_task(
    tx: &Tx,
    tool: &AnyTask,
    generation: TaskId,
    assistant: EntryId,
    call_id: String,
) -> SessionResult<TaskId> {
    tx.create_task(
        tool.as_definition_ref(),
        to_json(&ToolTaskInput::Model { assistant, call_id })?,
        TaskOptions {
            ownership: TaskOwnership::Task {
                task_id: generation,
            },
            conversation_id: None,
            background: None,
            abandon_on_restart: None,
        },
    )
    .await
}

/// Sequential round: start the next call and wait for it.
pub(super) async fn start_next_call(
    runtime: &Runtime,
    assistant: EntryId,
    tools: Vec<TaskId>,
    next: String,
    rest: Vec<String>,
    cx: &Context,
) -> SessionResult<()> {
    let conversation_id = runtime.conversation_id();
    let generation = runtime.task_id().erase();
    let tool = runtime.registry().builtins().tool.clone();
    runtime
        .commit(
            move |tx, _current| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                let task_id =
                    create_tool_task(&tx, &tool, generation, assistant, next.clone()).await?;
                if let Some(slots) = child_draft(&live, "tools")? {
                    for index in 0..slots.len()? {
                        let Some(slot) = slots.get(index)?.and_then(DraftItem::into_draft) else {
                            continue;
                        };
                        let call_id = slot.get("callId")?;
                        let same_call = call_id
                            .as_ref()
                            .and_then(|item| item.as_value())
                            .and_then(|value| value.as_str())
                            == Some(next.as_str());
                        let matches = same_call && slot.get("taskId")?.is_none();
                        if matches {
                            slot.set("taskId", to_json(&task_id)?)?;
                            break;
                        }
                    }
                }
                let mut tools = tools;
                tools.push(task_id);
                Ok(Some(Next::Waiting {
                    checkpoint: GenerationCheckpoint::Tools {
                        assistant,
                        tools,
                        pending: rest,
                    },
                    on: vec![task_id],
                    policy: JoinPolicy::AllSettled,
                }))
            },
            cx,
        )
        .await
}

/// A final answer; the final boundary places queued items (spec §6). The
/// first `onYield` continuation appends a user message and hands the run to
/// a successor generation, but only when the boundary selected no user item
/// and no reset. Otherwise the run's inputs settle `done`, and selected user
/// items start the next run.
pub(super) async fn answer(
    runtime: &Runtime,
    message: AssistantMessage,
    cx: &Context,
) -> SessionResult<()> {
    let continuation: Arc<Mutex<Option<UserInput>>> = Arc::default();
    let api = runtime.hook_api();
    runtime
        .hooks()
        .each(
            |hooks: &GenerationHooks| hooks.on_yield.clone(),
            |hook| {
                let pending = continuation
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .is_none()
                    .then(|| hook(&message, &api, cx));
                let continuation = Arc::clone(&continuation);
                async move {
                    if let Some(pending) = pending {
                        let next = pending.await?.map(|yielded| yielded.r#continue);
                        *continuation.lock().unwrap_or_else(PoisonError::into_inner) = next;
                    }
                    Ok(())
                }
            },
        )
        .await?;
    let continuation = continuation
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take();
    let conversation_id = runtime.conversation_id();
    let task_id = runtime.task_id().erase();
    let generation = runtime.registry().builtins().generation.clone();
    let commit_runtime = runtime.clone();
    runtime
        .commit(
            move |tx, _current| async move {
                let runtime = commit_runtime;
                // Queue modes are read on the Session line, when the boundary
                // is decided.
                let mut boundary =
                    prepare_boundary(&tx, conversation_id, queue_modes(&runtime)).await?;
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                let entry = append_assistant(&tx, conversation_id, message).await?;
                let result = completed(entry.id);
                let outcome = apply_boundary(
                    &tx,
                    &mut boundary,
                    BoundaryAt::Final,
                    timestamp(runtime.now()?)?,
                )
                .await?;
                if let Some(content) = continuation {
                    if outcome.users.is_empty() && !outcome.reset {
                        let user = UserMessage {
                            content,
                            timestamp: timestamp(runtime.now()?)?,
                        };
                        tx.append_typed_entry(
                            &USER_ENTRY,
                            conversation_id,
                            TypedEntryDraft {
                                model: Some(vec![Message::User(user)]),
                                ..TypedEntryDraft::default()
                            },
                        )
                        .await?;
                        let next = create_generation(&tx, &generation, conversation_id).await?;
                        hand_over(&live, task_id, next)?;
                        live.delete("generation")?;
                        return Ok(Some(result));
                    }
                }
                end_run(
                    &tx,
                    &live,
                    task_id,
                    &SubmissionSettlement::Done { answer: entry.id },
                )?;
                if !outcome.users.is_empty() {
                    start_run(&tx, &generation, conversation_id, &live, outcome.users).await?;
                }
                Ok(Some(result))
            },
            cx,
        )
        .await
}

/// Append the tool-calling answer and start its tool round in one commit
/// (spec §8.3). A call to a tool the request did not offer gets its
/// `tool_unavailable` result here; every other call gets a tool task owned
/// by the generation, only the first one now when the round is sequential.
/// The generation then waits for them in its `tools` phase, keeping the run.
pub(super) async fn start_tool_round(
    runtime: &Runtime,
    request: Request,
    message: AssistantMessage,
    calls: Vec<ToolCall>,
    cx: &Context,
) -> SessionResult<()> {
    let conversation_id = runtime.conversation_id();
    let messages = match request.messages {
        Some(messages) => messages,
        None => {
            runtime
                .context(
                    conversation_id,
                    cx,
                    ContextOptions {
                        at: Some(request.cutoff),
                    },
                )
                .await?
                .messages
        }
    };
    let offered: HashSet<String> = get_current_tools(&messages)
        .into_iter()
        .map(|tool| tool.name)
        .collect();
    // Read as the round starts; a tool is resolved as its tool task resolves it.
    let tools = runtime.agent(cx).await?.tools.clone();
    let sequential = runtime.settings().tool_execution == ToolExecutionMode::Sequential
        || calls.iter().any(|call| {
            offered.contains(&call.name)
                && tools
                    .iter()
                    .find(|tool| tool.name == call.name)
                    .and_then(|tool| tool.execution_mode)
                    == Some(ToolExecutionMode::Sequential)
        });
    let generation = runtime.task_id().erase();
    let tool = runtime.registry().builtins().tool.clone();
    let commit_runtime = runtime.clone();
    runtime
        .commit(
            move |tx, _current| async move {
                let runtime = commit_runtime;
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                let entry = append_assistant(&tx, conversation_id, message).await?;
                let mut slots: Vec<ToolSlot> = Vec::new();
                let mut tools: Vec<TaskId> = Vec::new();
                let mut pending: Vec<String> = Vec::new();
                for call in &calls {
                    if !offered.contains(&call.name) {
                        let unavailable = harness_error(
                            "tool_unavailable",
                            &format!("Tool {} is not available", call.name),
                        );
                        let meta = ToolResultMeta {
                            timestamp: runtime.now()?,
                            duration_ms: None,
                        };
                        let result =
                            append_tool_result(&tx, conversation_id, call, &unavailable, meta)
                                .await?;
                        slots.push(slot(call, None, ToolSlotStatus::Done, Some(result.id)));
                        continue;
                    }
                    if sequential && !tools.is_empty() {
                        pending.push(call.id.clone());
                        slots.push(slot(call, None, ToolSlotStatus::Pending, None));
                        continue;
                    }
                    let task_id =
                        create_tool_task(&tx, &tool, generation, entry.id, call.id.clone()).await?;
                    tools.push(task_id);
                    slots.push(slot(call, Some(task_id), ToolSlotStatus::Pending, None));
                }
                live.delete("generation")?;
                live.set("tools", to_json(&slots)?)?;
                let on = tools.clone();
                Ok(Some(Next::Waiting {
                    checkpoint: GenerationCheckpoint::Tools {
                        assistant: entry.id,
                        tools,
                        pending,
                    },
                    on,
                    policy: JoinPolicy::AllSettled,
                }))
            },
            cx,
        )
        .await
}

fn slot(
    call: &ToolCall,
    task_id: Option<TaskId>,
    status: ToolSlotStatus,
    entry: Option<EntryId>,
) -> ToolSlot {
    ToolSlot {
        call_id: call.id.clone(),
        name: call.name.clone(),
        task_id,
        status,
        output: None,
        dropped_bytes: None,
        dropped_lines: None,
        details: None,
        diagnostics: None,
        entry,
    }
}

/// The round's tools are terminal: apply their controls and either end the
/// run at the final boundary (`terminate`, `handoff`, or a queued reset) or
/// hand it to the next generation at the `postTools` boundary (spec §8.5).
#[expect(
    clippy::too_many_lines,
    reason = "one TS function, kept whole to read against it"
)]
pub(super) async fn finish_tool_round(
    runtime: &Runtime,
    assistant: EntryId,
    tools: Vec<TaskId>,
    cx: &Context,
) -> SessionResult<()> {
    let conversation_id = runtime.conversation_id();
    let typed: Vec<TaskId<ToolTaskResult>> = tools
        .iter()
        .map(|id| TaskId::from_number(id.get()))
        .collect();
    let outcomes = runtime.outcomes(&typed, cx).await?;
    let mut controls: Vec<(TaskId, Option<ToolControl>)> = Vec::with_capacity(tools.len());
    for (id, outcome) in tools.iter().zip(outcomes) {
        let control = match outcome {
            // Version 1 results have no kind; every result a generation's round reads is a model-issued call's.
            TaskOutcome::Completed {
                result: ToolTaskResult::Model { control, .. },
            } => control,
            TaskOutcome::Completed {
                result: ToolTaskResult::Nested,
            }
            | TaskOutcome::Failed { .. }
            | TaskOutcome::Aborted { .. }
            | TaskOutcome::Orphaned { .. }
            | TaskOutcome::Faulted { .. } => None,
        };
        // A JS `Map.set` of an existing key keeps its position.
        match controls.iter_mut().find(|(other, _)| other == id) {
            Some(existing) => existing.1 = control,
            None => controls.push((*id, control)),
        }
    }
    let live = runtime.snapshot(&LIVE_DOC, conversation_id, cx).await?;
    let slots: Vec<ToolSlot> = match live.as_ref().and_then(|live| live.get("tools")) {
        Some(tools) => from_json(tools)?,
        None => Vec::new(),
    };
    let results: Vec<EntryId> = slots.iter().filter_map(|slot| slot.entry).collect();
    let api = runtime.hook_api();
    runtime
        .hooks()
        .each(
            |hooks: &GenerationHooks| hooks.after_tools.clone(),
            |hook| hook(assistant, &results, &api, cx),
        )
        .await?;
    let control_of = |task_id: TaskId| {
        controls
            .iter()
            .find(|(id, _)| *id == task_id)
            .and_then(|(_, control)| control.as_ref())
    };
    // Every call of the round, including those answered without a task, must
    // ask to terminate.
    let terminate = !slots.is_empty()
        && slots.iter().all(|slot| {
            slot.task_id
                .and_then(control_of)
                .is_some_and(|control| control.terminate)
        });
    let added: Vec<String> = controls
        .iter()
        .filter_map(|(_, control)| control.as_ref())
        .flat_map(|control| control.add_tools.iter().flatten().cloned())
        .collect();
    // The last handoff in call order wins.
    let handoff = controls
        .iter()
        .rev()
        .find_map(|(_, control)| control.as_ref().and_then(|control| control.handoff.clone()));
    let task_id = runtime.task_id().erase();
    let generation = runtime.registry().builtins().generation.clone();
    let commit_runtime = runtime.clone();
    runtime
        .commit(
            move |tx, _current| async move {
                let runtime = commit_runtime;
                let mut boundary =
                    prepare_boundary(&tx, conversation_id, queue_modes(&runtime)).await?;
                if !added.is_empty() {
                    add_tools(&tx, conversation_id, &added).await?;
                }
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                let now = timestamp(runtime.now()?)?;
                if terminate || handoff.is_some() {
                    if let Some(handoff) = handoff {
                        let message = UserMessage {
                            content: UserContent::Text(handoff),
                            timestamp: now,
                        };
                        let entry = tx
                            .append_typed_entry(
                                &RESET_ENTRY,
                                conversation_id,
                                TypedEntryDraft {
                                    model: Some(vec![Message::User(message)]),
                                    head: Some(EntryHead::SelfEntry),
                                    ..TypedEntryDraft::default()
                                },
                            )
                            .await?;
                        boundary.head = Some(entry.id);
                    }
                    let outcome =
                        apply_boundary(&tx, &mut boundary, BoundaryAt::Final, now).await?;
                    end_run(
                        &tx,
                        &live,
                        task_id,
                        &SubmissionSettlement::Done { answer: assistant },
                    )?;
                    if !outcome.users.is_empty() {
                        start_run(&tx, &generation, conversation_id, &live, outcome.users).await?;
                    }
                } else {
                    let outcome =
                        apply_boundary(&tx, &mut boundary, BoundaryAt::PostTools, now).await?;
                    if outcome.reset {
                        // The queued reset cut the run's context before an answer.
                        end_run(
                            &tx,
                            &live,
                            task_id,
                            &SubmissionSettlement::Unanswered {
                                reason: "reset".to_owned(),
                                detail: None,
                            },
                        )?;
                        if !outcome.users.is_empty() {
                            start_run(&tx, &generation, conversation_id, &live, outcome.users)
                                .await?;
                        }
                    } else {
                        live.delete("tools")?;
                        live.delete("nestedTools")?;
                        if run_task_id(&live)? == Some(task_id) {
                            let inputs = live.child("run")?.child("inputs")?;
                            let users = outcome
                                .users
                                .iter()
                                .map(to_json)
                                .collect::<Result<Vec<_>, _>>()?;
                            inputs.push(users)?;
                        }
                        let next = create_generation(&tx, &generation, conversation_id).await?;
                        hand_over(&live, task_id, next)?;
                    }
                }
                Ok(Some(completed(assistant)))
            },
            cx,
        )
        .await
}
