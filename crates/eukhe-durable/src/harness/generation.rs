//! Built-in generation task (`harness/generation.ts`, spec §7.4, §8.2-8.5):
//! prepares the positional system prompt and tool loadout, requests or polls
//! the model, retries, and classifies the response. The run's inputs live in
//! `pi.live.run`.
//!
//! `startRun`, `createGeneration`, `handOver`, `convertPartial`, and
//! `appendAssistant` live in [`crate::harness::live::run`] so admission and
//! conversations do not depend on this module.

mod round;
mod stream;
#[cfg(test)]
mod tests;

use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::json::to_json;
use eukhe_pi_ai::types::{DeferredCancelOptions, DeferredFetchOptions, ProviderRequestOptions};
use eukhe_pi_ai::utils::overflow::is_context_overflow;
use eukhe_pi_ai::utils::retry::{is_retryable_assistant_error, retry_delay_ms, RetryDelay};
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, DeferredHandle, Message, ModelThinkingLevel,
    StopReason, ThinkingLevel, ToolCall,
};
use serde::{Deserialize, Serialize};

use self::round::{answer, finish_tool_round, read_calls, start_next_call, start_tool_round};
use self::stream::stream_response;
use crate::entries::SYSTEM_ENTRY;
use crate::harness::compaction::{estimate_context, select_cut};
use crate::harness::live::run::{
    append_assistant, convert_partial, create_compaction, timestamp, CompactionInput,
};
use crate::harness::live::{end_run, LiveDeferred, LiveGeneration, LiveRetry, LIVE_DOC};
use crate::harness::prompt::{plan_system_entries, render_sections, replay_sections, SystemDraft};
use crate::harness::provider::ensure_provider_session_id;
use crate::harness::tool::append_tool_result;
use crate::harness::tool::harness_error;
use crate::harness::types::{
    CompactionPolicy, CompactionReason, CompactionResult, ContextView, ConversationStreamOptions,
    GenerationHooks, ModelRef, PromptInput, RequestMessages,
};
use crate::session::{SessionError, SessionResult};
use crate::tasks::{define_task, NextTaskState, RunningTask, Task, TaskDefinition, TaskRuntime};
use crate::types::{
    EntryId, EntryQuery, JoinPolicy, SubmissionSettlement, TaskId, TaskOutcome, TaskOutcomeError,
};

/// Input of `pi.generation` (TS `Record<string, never>`): always `{}`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenerationInput {}

/// Checkpoint of `pi.generation`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
pub enum GenerationCheckpoint {
    #[serde(rename_all = "camelCase")]
    Prepare {
        attempt: u64,
        /// The blocking compaction this generation waited for; it starts no
        /// other compaction (spec §8.3).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        compacted: Option<TaskId<CompactionResult>>,
        /// Error text of the overflow that started `compacted`; checked once
        /// when `prepare` resumes.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        overflow: Option<String>,
    },
    #[serde(rename_all = "camelCase")]
    Request {
        attempt: u64,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        compacted: Option<TaskId<CompactionResult>>,
        model: ModelRef,
        thinking_level: ModelThinkingLevel,
        /// The settings' request options when preparation committed; a
        /// resend after recovery uses them unchanged.
        stream_options: ConversationStreamOptions,
        /// Newest entry included in the request.
        cutoff: EntryId,
    },
    #[serde(rename_all = "camelCase")]
    Retry {
        attempt: u64,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        compacted: Option<TaskId<CompactionResult>>,
        until: f64,
    },
    #[serde(rename_all = "camelCase")]
    Poll {
        attempt: u64,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        compacted: Option<TaskId<CompactionResult>>,
        model: ModelRef,
        cutoff: EntryId,
        handle: DeferredHandle,
        poll_at: f64,
    },
    /// Waiting on the round's tool tasks, which the generation owns (spec
    /// §8.5).
    #[serde(rename_all = "camelCase")]
    Tools {
        /// The tool-calling answer.
        assistant: EntryId,
        /// Tool tasks created so far, in call order; grows by one per started
        /// call of a sequential round.
        tools: Vec<TaskId>,
        /// Calls of a sequential round not started yet, in call order.
        pending: Vec<String>,
    },
}

/// Result of `pi.generation`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GenerationResult {
    pub entry_id: EntryId,
}

/// The typed `pi.generation` task.
pub type GenerationTask =
    Task<GenerationInput, GenerationCheckpoint, GenerationResult, GenerationHooks>;

pub(crate) type Runtime =
    TaskRuntime<GenerationInput, GenerationCheckpoint, GenerationResult, GenerationHooks>;
type Current = RunningTask<GenerationInput, GenerationCheckpoint, GenerationResult>;
pub(crate) type Next = NextTaskState<GenerationCheckpoint, GenerationResult>;

/// What classification needs from the request that produced a message.
pub(crate) struct Request {
    attempt: u64,
    compacted: Option<TaskId<CompactionResult>>,
    model: ModelRef,
    cutoff: EntryId,
    /// Committed model context through `cutoff`, when the phase already
    /// derived it.
    pub(crate) messages: Option<Vec<Message>>,
    /// Set when the message came from polling, so a still deferred result
    /// polls strictly later.
    poll_at: Option<f64>,
}

const DEFAULT_POLL_AFTER_MS: f64 = 5000.0;

/// Built-in generation task: prepares the positional system prompt and tool
/// loadout, requests or polls the model, retries, and classifies the
/// response. The run's inputs live in `pi.live.run`.
pub static GENERATION_TASK: LazyLock<GenerationTask> = LazyLock::new(|| {
    define_task(
        TaskDefinition::new(
            "pi.generation",
            1,
            |_input: &GenerationInput| {
                Ok(GenerationCheckpoint::Prepare {
                    attempt: 1,
                    compacted: None,
                    overflow: None,
                })
            },
            abort,
        )
        .phase("prepare", prepare)
        .phase("request", request)
        .phase("retry", retry)
        .phase("poll", poll)
        .phase("tools", tools),
    )
});

/// The checkpoint a phase handler was dispatched for; the scheduler
/// dispatches by `phase`, so another variant is a corrupt record.
fn phase_mismatch(expected: &str) -> SessionError {
    SessionError::type_error(format!(
        "pi.generation checkpoint is not in phase {expected}"
    ))
}

/// pi-ai `reasoning` of a pinned thinking level; `off` sends none.
fn reasoning(level: ModelThinkingLevel) -> Option<ThinkingLevel> {
    match level {
        ModelThinkingLevel::Off => None,
        ModelThinkingLevel::Minimal => Some(ThinkingLevel::Minimal),
        ModelThinkingLevel::Low => Some(ThinkingLevel::Low),
        ModelThinkingLevel::Medium => Some(ThinkingLevel::Medium),
        ModelThinkingLevel::High => Some(ThinkingLevel::High),
        ModelThinkingLevel::Xhigh => Some(ThinkingLevel::Xhigh),
        ModelThinkingLevel::Max => Some(ThinkingLevel::Max),
    }
}

fn live_generation(attempt: u64) -> LiveGeneration {
    LiveGeneration {
        attempt,
        message: None,
        retry: None,
        deferred: None,
    }
}

/// Render the system prompt and tool loadout and append the positional
/// `pi.system` entries they need, then move to `request`. The agent and
/// settings resolved here are fixed for this request. Only the Harness
/// writes to a busy conversation, so the transcript read here is still the
/// tail at the commit.
#[expect(
    clippy::too_many_lines,
    reason = "one TS phase, kept whole to read against it"
)]
async fn prepare(task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let GenerationCheckpoint::Prepare {
        attempt,
        compacted,
        overflow,
    } = task.checkpoint
    else {
        return Err(phase_mismatch("prepare"));
    };
    let conversation_id = runtime.conversation_id();
    let agent = runtime.agent(&cx).await?;
    let settings = runtime.settings();
    let reference = agent.model.clone();
    let resolved = reference.as_ref().and_then(|reference| {
        runtime
            .models()
            .get_model(&reference.provider, &reference.model_id)
    });
    let (Some(model), Some(resolved)) = (reference.clone(), resolved) else {
        return fail_no_model(&runtime, reference.as_ref(), &cx).await;
    };
    let thinking_level = agent.thinking_level;
    if let (Some(compacted), Some(overflow)) = (compacted, &overflow) {
        let outcomes = runtime
            .outcomes::<CompactionResult>(&[compacted], &cx)
            .await?;
        let compacted_entry = matches!(
            outcomes.first(),
            Some(TaskOutcome::Completed { result }) if result.entry_id.is_some()
        );
        if !compacted_entry {
            return fail_model_error(&runtime, overflow.clone(), &cx).await;
        }
    }
    let view = runtime.context(conversation_id, &cx, None).await?;
    let shown = replay_sections(&view.messages);
    let report_runtime = runtime.clone();
    let report = move |error: SessionError| report_runtime.report(error);
    let env = match runtime.env(&cx).await {
        Ok(env) => env,
        Err(error) => {
            if cx.aborted() {
                return Err(error);
            }
            report(error)?;
            None
        }
    };
    let input = PromptInput {
        conversation_id,
        agent: Arc::clone(&agent),
        env,
        shown: shown.clone(),
        read: Arc::new(runtime.clone()),
    };
    let desired = render_sections(&agent.sections, &input, &shown, &report, &cx).await?;
    let tools: Vec<_> = agent.tools.iter().map(|tool| tool.tool()).collect();
    let entries = plan_system_entries(&view, &desired, &tools, timestamp(runtime.now()?)?);
    let threshold = if compacted.is_none() {
        threshold_compaction(
            &view,
            &entries,
            resolved.context_window,
            &settings.compaction,
        )
    } else {
        None
    };
    let compaction = runtime.registry().builtins().compaction.clone();
    let task_id = runtime.task_id().erase();
    if threshold == Some(Threshold::Blocking) {
        // Compact first and prepare again; the transcript is unchanged until
        // the compaction appends.
        return runtime
            .commit(
                move |tx, _current| async move {
                    let child = create_compaction(
                        &tx,
                        &compaction,
                        conversation_id,
                        CompactionInput {
                            reason: CompactionReason::Threshold,
                            instructions: None,
                        },
                        Some(task_id),
                    )
                    .await?;
                    let checkpoint = GenerationCheckpoint::Prepare {
                        attempt,
                        compacted: Some(child),
                        overflow: None,
                    };
                    Ok(Some(Next::Waiting {
                        checkpoint,
                        on: vec![child.erase()],
                        policy: JoinPolicy::AllSettled,
                    }))
                },
                &cx,
            )
            .await;
    }
    let stream_options = settings.stream;
    runtime
        .commit(
            move |tx, _current| async move {
                let mut cutoff = tx
                    .scan_entries(EntryQuery::new(conversation_id), 1, None)
                    .await?
                    .items
                    .first()
                    .map(|entry| entry.id);
                for entry in entries {
                    cutoff = Some(
                        tx.append_typed_entry(&SYSTEM_ENTRY, conversation_id, entry)
                            .await?
                            .id,
                    );
                }
                let Some(cutoff) = cutoff else {
                    return Err(SessionError::error(format!(
                        "Conversation {conversation_id} has no entries to send"
                    )));
                };
                // Checked in this commit, so a compaction admitted during
                // preparation counts.
                if threshold == Some(Threshold::Background)
                    && tx
                        .doc(&LIVE_DOC, conversation_id)
                        .await?
                        .get("compactions")?
                        .is_none()
                {
                    create_compaction(
                        &tx,
                        &compaction,
                        conversation_id,
                        CompactionInput {
                            reason: CompactionReason::Threshold,
                            instructions: None,
                        },
                        None,
                    )
                    .await?;
                }
                Ok(Some(Next::Running {
                    checkpoint: GenerationCheckpoint::Request {
                        attempt,
                        compacted,
                        model,
                        thinking_level,
                        stream_options,
                        cutoff,
                    },
                }))
            },
            &cx,
        )
        .await
}

async fn request(task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let GenerationCheckpoint::Request {
        attempt,
        compacted,
        model: reference,
        thinking_level,
        stream_options,
        cutoff,
    } = task.checkpoint
    else {
        return Err(phase_mismatch("request"));
    };
    let conversation_id = runtime.conversation_id();
    runtime
        .commit(
            move |tx, _current| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                convert_partial(&tx, &live, conversation_id).await?;
                live.set("generation", to_json(&live_generation(attempt))?)?;
                Ok(None)
            },
            &cx,
        )
        .await?;
    let Some(model) = runtime
        .models()
        .get_model(&reference.provider, &reference.model_id)
    else {
        return fail_no_model(&runtime, Some(&reference), &cx).await;
    };
    let view = runtime.context(conversation_id, &cx, Some(cutoff)).await?;
    let messages = Mutex::new(view.messages.clone());
    let api = runtime.hook_api();
    runtime
        .hooks()
        .each(
            |hooks: &GenerationHooks| hooks.before_request.clone(),
            |hook| {
                let current = RequestMessages {
                    messages: messages
                        .lock()
                        .unwrap_or_else(PoisonError::into_inner)
                        .clone(),
                };
                let pending = hook(&current, &api, &cx);
                let messages = &messages;
                async move {
                    if let Some(replaced) = pending.await? {
                        *messages.lock().unwrap_or_else(PoisonError::into_inner) =
                            replaced.messages;
                    }
                    Ok(())
                }
            },
        )
        .await?;
    let messages = messages
        .into_inner()
        .unwrap_or_else(PoisonError::into_inner);
    let mut options = stream_options.simple_stream_options();
    options.stream.request.signal = Some(runtime.signal());
    options.stream.session_id = Some(ensure_provider_session_id(&runtime, &cx).await?);
    options.reasoning = reasoning(thinking_level);
    let message = stream_response(&runtime, &model, messages, options, attempt, &cx).await?;
    let request = Request {
        attempt,
        compacted,
        model: reference,
        cutoff,
        messages: Some(view.messages),
        poll_at: None,
    };
    classify(&runtime, request, message, &cx).await
}

async fn retry(task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let GenerationCheckpoint::Retry {
        attempt,
        compacted,
        until,
    } = task.checkpoint
    else {
        return Err(phase_mismatch("retry"));
    };
    runtime.sleep(until, &cx).await?;
    let conversation_id = runtime.conversation_id();
    runtime
        .commit(
            move |tx, _current| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                live.set("generation", to_json(&live_generation(attempt + 1))?)?;
                Ok(Some(Next::Running {
                    checkpoint: GenerationCheckpoint::Prepare {
                        attempt: attempt + 1,
                        compacted,
                        overflow: None,
                    },
                }))
            },
            &cx,
        )
        .await
}

async fn poll(task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let GenerationCheckpoint::Poll {
        attempt,
        compacted,
        model: reference,
        cutoff,
        handle,
        poll_at,
    } = task.checkpoint
    else {
        return Err(phase_mismatch("poll"));
    };
    let Some(model) = runtime
        .models()
        .get_model(&reference.provider, &reference.model_id)
    else {
        return fail_no_model(&runtime, Some(&reference), &cx).await;
    };
    runtime.sleep(poll_at, &cx).await?;
    let options = DeferredFetchOptions {
        request: ProviderRequestOptions {
            signal: Some(runtime.signal()),
            ..ProviderRequestOptions::default()
        },
        ..DeferredFetchOptions::default()
    };
    let message = runtime
        .models()
        .fetch_deferred(&model, &handle, options.into())
        .await;
    let request = Request {
        attempt,
        compacted,
        model: reference,
        cutoff,
        messages: None,
        poll_at: Some(poll_at),
    };
    classify(&runtime, request, message, &cx).await
}

async fn tools(task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let GenerationCheckpoint::Tools {
        assistant,
        tools,
        pending,
    } = task.checkpoint
    else {
        return Err(phase_mismatch("tools"));
    };
    let mut pending = pending.into_iter();
    let Some(next) = pending.next() else {
        return finish_tool_round(&runtime, assistant, tools, &cx).await;
    };
    // Sequential round: start the next call and wait for it.
    start_next_call(&runtime, assistant, tools, next, pending.collect(), &cx).await
}

async fn abort(task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let checkpoint = task.checkpoint;
    if let GenerationCheckpoint::Poll { model, handle, .. } = &checkpoint {
        if let Some(model) = runtime.models().get_model(&model.provider, &model.model_id) {
            let options = DeferredCancelOptions {
                signal: Some(runtime.signal()),
                ..DeferredCancelOptions::default()
            };
            if let Err(error) = runtime
                .models()
                .cancel_deferred(&model, handle, options.into())
                .await
            {
                runtime.report(SessionError::other(error))?;
            }
        }
    }
    let conversation_id = runtime.conversation_id();
    // Runs after the round's tool tasks are terminal; calls never started get
    // `aborted` results (spec §8.5).
    let unstarted = match &checkpoint {
        GenerationCheckpoint::Tools {
            assistant, pending, ..
        } => read_calls(&runtime, *assistant, pending, &cx).await?,
        GenerationCheckpoint::Prepare { .. }
        | GenerationCheckpoint::Request { .. }
        | GenerationCheckpoint::Retry { .. }
        | GenerationCheckpoint::Poll { .. } => Vec::new(),
    };
    let commit_runtime = runtime.clone();
    runtime
        .commit(
            move |tx, _current| async move {
                let runtime = commit_runtime;
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                convert_partial(&tx, &live, conversation_id).await?;
                for call in &unstarted {
                    let result =
                        harness_error("aborted", &format!("Tool {} was aborted", call.name));
                    append_tool_result(&tx, conversation_id, call, &result, runtime.now()?).await?;
                }
                end_run(
                    &tx,
                    &live,
                    runtime.task_id().erase(),
                    &SubmissionSettlement::Unanswered {
                        reason: "aborted".to_owned(),
                        detail: None,
                    },
                )?;
                Ok(Some(Next::Terminal {
                    outcome: TaskOutcome::Aborted {
                        reason: None,
                        result: None,
                    },
                }))
            },
            &cx,
        )
        .await
}

/// Which threshold compaction preparation starts before its request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Threshold {
    Blocking,
    Background,
}

/// Which threshold compaction preparation starts before its request (spec
/// §8.3): `blocking` above `contextWindow - reserveTokens`, `background`
/// above the background threshold, and only when range selection finds a
/// cut. The caller starts a background one only while no compaction is
/// listed.
#[expect(
    clippy::cast_precision_loss,
    reason = "TS compares token counts as doubles; blocking may be negative"
)]
fn threshold_compaction(
    view: &ContextView,
    planned: &[SystemDraft],
    context_window: u64,
    policy: &CompactionPolicy,
) -> Option<Threshold> {
    if !policy.enabled || context_window == 0 {
        return None;
    }
    let extra: Vec<Message> = planned
        .iter()
        .flat_map(|entry| entry.model.iter().flatten().cloned())
        .collect();
    let tokens = estimate_context(view, &extra) as f64;
    let blocking = context_window as f64 - policy.reserve_tokens;
    let background = blocking - policy.background_tokens;
    let over = if tokens > blocking {
        Some(Threshold::Blocking)
    } else if policy.background_tokens > 0.0 && tokens > background {
        Some(Threshold::Background)
    } else {
        None
    };
    over.filter(|_| select_cut(view, policy.keep_recent_tokens).is_some())
}

/// `{ reason }` failure detail.
#[derive(Serialize)]
struct FailureDetail<'a> {
    reason: &'a str,
}

fn failed(message: String, reason: &str) -> SessionResult<Next> {
    Ok(Next::Terminal {
        outcome: TaskOutcome::Failed {
            error: TaskOutcomeError {
                message,
                detail: Some(to_json(&FailureDetail { reason })?),
            },
            result: None,
        },
    })
}

/// Settle the run's inputs `unanswered` with `model_error` and fail with
/// `text`.
async fn fail_model_error(runtime: &Runtime, text: String, cx: &Context) -> SessionResult<()> {
    let conversation_id = runtime.conversation_id();
    let task_id = runtime.task_id().erase();
    runtime
        .commit(
            move |tx, _current| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                end_run(
                    &tx,
                    &live,
                    task_id,
                    &SubmissionSettlement::Unanswered {
                        reason: "model_error".to_owned(),
                        detail: Some(to_json(&text)?),
                    },
                )?;
                failed(text, "model_error").map(Some)
            },
            cx,
        )
        .await
}

/// Settle the run's inputs `unanswered` with `no_model` and fail.
async fn fail_no_model(
    runtime: &Runtime,
    reference: Option<&ModelRef>,
    cx: &Context,
) -> SessionResult<()> {
    let message = match reference {
        None => "No model is configured".to_owned(),
        Some(reference) => format!(
            "Model {}/{} is not available",
            reference.provider, reference.model_id
        ),
    };
    let conversation_id = runtime.conversation_id();
    let task_id = runtime.task_id().erase();
    runtime
        .commit(
            move |tx, _current| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                end_run(
                    &tx,
                    &live,
                    task_id,
                    &SubmissionSettlement::Unanswered {
                        reason: "no_model".to_owned(),
                        detail: None,
                    },
                )?;
                failed(message, "no_model").map(Some)
            },
            cx,
        )
        .await
}

/// Classify a terminal provider message in one commit that also clears the
/// partial.
#[expect(
    clippy::too_many_lines,
    reason = "one TS function, kept whole to read against it"
)]
async fn classify(
    runtime: &Runtime,
    request: Request,
    message: AssistantMessage,
    cx: &Context,
) -> SessionResult<()> {
    // An abort mark or close: the abort invocation or the reopened run
    // handles the committed state.
    runtime
        .signal()
        .throw_if_aborted()
        .map_err(SessionError::Aborted)?;
    let conversation_id = runtime.conversation_id();
    let task_id = runtime.task_id().erase();
    let attempt = request.attempt;
    let compacted = request.compacted;
    if message.stop_reason == StopReason::Deferred {
        if let Some(handle) = message.deferred.clone() {
            let after = runtime.now()? + handle.poll_after_ms.unwrap_or(DEFAULT_POLL_AFTER_MS);
            let poll_at = after.max(request.poll_at.map_or(f64::NEG_INFINITY, |at| at + 1.0));
            let model = request.model;
            let cutoff = request.cutoff;
            return runtime
                .commit(
                    move |tx, _current| async move {
                        let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                        let generation = LiveGeneration {
                            deferred: Some(LiveDeferred { poll_at }),
                            ..live_generation(attempt)
                        };
                        live.set("generation", to_json(&generation)?)?;
                        Ok(Some(Next::Running {
                            checkpoint: GenerationCheckpoint::Poll {
                                attempt,
                                compacted,
                                model,
                                cutoff,
                                handle,
                                poll_at,
                            },
                        }))
                    },
                    cx,
                )
                .await;
        }
    }
    let api = runtime.hook_api();
    runtime
        .hooks()
        .each(
            |hooks: &GenerationHooks| hooks.after_response.clone(),
            |hook| hook(&message, &api, cx),
        )
        .await?;
    let calls: Vec<ToolCall> = message
        .content
        .iter()
        .filter_map(|content| match content {
            AssistantContentBlock::ToolCall(call) => Some(call.clone()),
            AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
        })
        .collect();
    if message.stop_reason == StopReason::ToolUse && !calls.is_empty() {
        return start_tool_round(runtime, request, message, calls, cx).await;
    }
    if matches!(
        message.stop_reason,
        StopReason::Stop | StopReason::Length | StopReason::ToolUse
    ) {
        return answer(runtime, message, cx).await;
    }
    // The retry and compaction policies govern the next attempt, so they are
    // read now rather than pinned at preparation.
    let settings = runtime.settings();
    let overflow = message.stop_reason == StopReason::Error && is_context_overflow(&message, None);
    if overflow && compacted.is_none() && settings.compaction.enabled {
        let policy = settings.compaction;
        let view = runtime
            .context(conversation_id, cx, Some(request.cutoff))
            .await?;
        if select_cut(&view, policy.keep_recent_tokens).is_some() {
            let text = message
                .error_message
                .clone()
                .unwrap_or_else(|| "Context overflow".to_owned());
            let compaction = runtime.registry().builtins().compaction.clone();
            return runtime
                .commit(
                    move |tx, _current| async move {
                        let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                        append_assistant(&tx, conversation_id, message).await?;
                        live.delete("generation")?;
                        let child = create_compaction(
                            &tx,
                            &compaction,
                            conversation_id,
                            CompactionInput {
                                reason: CompactionReason::Overflow,
                                instructions: None,
                            },
                            Some(task_id),
                        )
                        .await?;
                        Ok(Some(Next::Waiting {
                            checkpoint: GenerationCheckpoint::Prepare {
                                attempt,
                                compacted: Some(child),
                                overflow: Some(text),
                            },
                            on: vec![child.erase()],
                            policy: JoinPolicy::AllSettled,
                        }))
                    },
                    cx,
                )
                .await;
        }
    }
    let policy = settings.retry;
    // An overflow is never retried: only a compaction can make the next
    // request fit.
    let retry = message.stop_reason == StopReason::Error
        && !overflow
        && is_retryable_assistant_error(&message)
        && policy.enabled
        && attempt <= u64::from(policy.max_retries);
    let until = if retry {
        let delay = RetryDelay {
            base_delay_ms: policy.base_delay_ms,
            max_agent_delay_ms: policy.max_agent_delay_ms,
        };
        runtime.now()? + retry_delay_ms(delay, u32::try_from(attempt).unwrap_or(u32::MAX))
    } else {
        0.0
    };
    runtime
        .commit(
            move |tx, _current| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                let error = message.error_message.clone();
                let stop_reason = message.stop_reason;
                append_assistant(&tx, conversation_id, message).await?;
                if retry {
                    let generation = LiveGeneration {
                        retry: Some(LiveRetry {
                            at: until,
                            error: error.unwrap_or_default(),
                        }),
                        ..live_generation(attempt)
                    };
                    live.set("generation", to_json(&generation)?)?;
                    return Ok(Some(Next::Running {
                        checkpoint: GenerationCheckpoint::Retry {
                            attempt,
                            compacted,
                            until,
                        },
                    }));
                }
                let text = error.unwrap_or_else(|| {
                    format!(
                        "Model response ended with stop reason {}",
                        stop_reason.as_str()
                    )
                });
                end_run(
                    &tx,
                    &live,
                    task_id,
                    &SubmissionSettlement::Unanswered {
                        reason: "model_error".to_owned(),
                        detail: Some(to_json(&text)?),
                    },
                )?;
                failed(text, "model_error").map(Some)
            },
            cx,
        )
        .await
}
