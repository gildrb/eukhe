//! Built-in generation task (`harness/generation.ts`, spec §7.4, §8.2-8.5):
//! prepares the positional system prompt and tool loadout, requests or polls
//! the model, retries, and classifies the response. The run's inputs live in
//! `pi.live.run`.
//!
//! `startRun`, `createGeneration`, `handOver`, `convertPartial`, and
//! `appendAssistant` live in [`crate::harness::live::run`] so admission and
//! conversations do not depend on this module.

mod decide;
mod deferred;
mod entry;
mod force;
mod leak;
mod note;
mod repeat;
mod round;
mod stream;
#[cfg(test)]
mod tests;

use std::collections::HashSet;
use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use eukhe_ai::capabilities::CapabilityOptions;
use eukhe_ai::models::ModelsCapabilityOptions;
use eukhe_ai::types::{
    DeferredCancelOptions, DeferredFetchOptions, DeferredRequest, DeferredWindow,
    ProviderRequestOptions,
};
use eukhe_ai::utils::overflow::is_context_overflow;
use eukhe_ai::utils::retry::{
    is_retryable_assistant_error, repeated_lines, retry_wait, stalled_idle_ms, RetryDelay,
    RetryWait,
};
use eukhe_ai::utils::stream_failure::RepeatedLines;
use eukhe_ai::utils::transcript::get_current_tools;
use eukhe_bend::rules::infer_force::{self, Offer, Reply as ForceReply, Step as ForceStep};
use eukhe_chord::context::Context;
use eukhe_chord::json::to_json;
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, DeferredHandle, Message, Model, ModelThinkingLevel,
    StopReason, ThinkingLevel, ToolCall, ToolChoice, UserContent, UserMessage,
};
use serde::{Deserialize, Serialize};

use self::decide::{
    after_compaction, after_reply, before_request, recover, retry_note, threshold_for, Act,
    Compacted, Compaction, Counts, Ended, Failure, Limits, Prepared, Reply, Rounds, Step, Stuck,
    Threshold, CAPS, LENGTH_NOTES, MAX_NOTES, REDIRECT_NOTES,
};
use self::deferred::{idle_after_stall, FailedPoll, PollFailure};
use self::force::{soft_prompt, Forcing};
use self::leak::{scan, Leak};
use self::note::{NoteCause, RepeatedCall, RetryNote, ARGUMENTS_SHOWN};
use self::repeat::{canonical_arguments, rounds_in_a_row};
use self::round::{answer, finish_tool_round, read_calls, start_next_call, start_tool_round};
use self::stream::{request_context, stream_response};
use crate::entries::SYSTEM_ENTRY;
use crate::harness::compaction::{estimate_context, select_cut};
use crate::harness::inbox::{has_queued_summary, INBOX_DOC};
use crate::harness::live::run::{
    append_assistant, convert_partial, create_compaction, timestamp, CompactionInput,
};
use crate::harness::live::{end_run, LiveDeferred, LiveGeneration, LiveRetry, LIVE_DOC};
use crate::harness::prompt::{plan_system_entries, render_sections, replay_sections, SystemDraft};
use crate::harness::provider::ensure_provider_session_id;
use crate::harness::tool::{append_tool_result, harness_error, ToolResultMeta};
use crate::harness::types::{
    CompactionPolicy, CompactionReason, CompactionResult, ContextOptions, ContextView,
    ConversationStreamOptions, GenerationHooks, ModelRef, PromptInput, RequestMessages, Settings,
    ThresholdTokens,
};
use crate::session::{SessionError, SessionResult};
use crate::tasks::{define_task, NextTaskState, RunningTask, Task, TaskDefinition, TaskRuntime};
use crate::types::{
    EntryId, EntryQuery, JoinPolicy, SubmissionSettlement, TaskId, TaskOutcome, TaskOutcomeError,
};

pub use self::force::ForcedToolError;

/// Input of `pi.generation` (TS `Record<string, never>`): `{}` for a run's
/// first generation; the next ones carry the run's finished rounds.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenerationInput {
    #[serde(default, skip_serializing_if = "Rounds::is_first")]
    pub(crate) rounds: Rounds,
}

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
        /// Set when `compacted` is a blocking threshold compaction; checked
        /// once when `prepare` resumes.
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        threshold: bool,
        /// Requests of the forced tool call before this one that went
        /// without the call ([`ConversationStreamOptions::force_tool`]).
        #[serde(default, skip_serializing_if = "is_zero")]
        forced: u32,
        /// The note the request ends with (H4.7), after a noted reply.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        note: Option<RetryNote>,
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
        #[serde(default, skip_serializing_if = "is_zero")]
        forced: u32,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        note: Option<RetryNote>,
    },
    #[serde(rename_all = "camelCase")]
    Retry {
        attempt: u64,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        compacted: Option<TaskId<CompactionResult>>,
        until: f64,
        #[serde(default, skip_serializing_if = "is_zero")]
        forced: u32,
        /// The note the retry's request ends with ([`retry_note`]).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        note: Option<RetryNote>,
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
        /// When the request this polls for went out (the harness clock,
        /// ms).
        sent_at: f64,
        /// When the request's deferred job's time ends (H4.4): its
        /// provider's expiry, else the end of its window.
        deadline: f64,
        /// The fetches of the job that failed in a row (H4.4); a reply
        /// that is still deferred sets it to 0.
        #[serde(default, skip_serializing_if = "is_zero")]
        failures: u32,
        #[serde(default, skip_serializing_if = "is_zero")]
        forced: u32,
        /// The forced tool call of the request this polls for and its
        /// escalation, pinned with it.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        force: Option<Forcing>,
        /// The note of the request this polls for, pinned with it.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        note: Option<RetryNote>,
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

/// Serde `skip_serializing_if` of the `forced` counters: a generation that
/// forces no tool keeps its records unchanged.
#[expect(
    clippy::trivially_copy_pass_by_ref,
    reason = "serde `skip_serializing_if` passes the field by reference"
)]
fn is_zero(count: &u32) -> bool {
    *count == 0
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
    /// When the request went out (the harness clock, ms).
    sent_at: f64,
    /// When the request's deferred job's time ends (H4.4): the end of the
    /// requested window, until the job's handle gives the provider's
    /// expiry.
    deadline: f64,
    /// The poll that gave the message; none for the request itself.
    poll: Option<Polled>,
    /// Earlier requests of the forced call that went without it.
    forced: u32,
    /// The request's forced tool call, when it forces one.
    force: Option<Forcing>,
    /// The note the request ended with.
    note: Option<RetryNote>,
}

/// The poll of a deferred job that gave a message.
struct Polled {
    /// When it was due, so a job that is still deferred polls strictly
    /// later.
    at: f64,
    /// The job's handle.
    handle: DeferredHandle,
    /// The fetches of the job that failed in a row before this one.
    failures: u32,
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
                    threshold: false,
                    forced: 0,
                    note: None,
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
        threshold: blocked,
        forced,
        note,
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
    // The compaction this preparation waited for, if it resumes after one.
    let waited = match (compacted, &overflow) {
        (Some(child), Some(_)) => Some((child, Compaction::Overflow)),
        (Some(child), None) if blocked => Some((child, Compaction::Threshold)),
        _ => None,
    };
    if let Some((child, compaction)) = waited {
        let outcomes = runtime.outcomes::<CompactionResult>(&[child], &cx).await?;
        let (ended, failure) = compaction_end(outcomes.first());
        if after_compaction(compaction, ended).is_err() {
            let text = match (overflow, failure) {
                (Some(overflow), _) => overflow,
                (None, Some(failure)) => failure,
                (None, None) => "Compaction found nothing to compact".to_owned(),
            };
            return fail_model_error(&runtime, text, &cx).await;
        }
    }
    let view = runtime
        .context(conversation_id, &cx, ContextOptions::default())
        .await?;
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
    let at = Counts {
        attempt,
        notes: note.as_ref().map_or(0, |note| note.spent),
        waited: 0,
        compacted: compacted.is_some(),
    };
    let policy = &settings.compaction;
    // A generation that compacted reads no threshold (law
    // `run_prepare_compacted_reads_no_threshold`), so its context is not
    // measured. The provider's count costs one request, so it runs only
    // when the threshold check runs.
    let checks = !at.compacted && policy.enabled && resolved.context_window != 0;
    let counted = match policy.token_count {
        ThresholdTokens::Provider if checks => {
            Some(provider_tokens(&runtime, &resolved, &settings.stream, &view, &entries).await)
        }
        ThresholdTokens::Provider | ThresholdTokens::Estimate => None,
    };
    let threshold = if at.compacted {
        None
    } else {
        threshold_compaction(&view, resolved.context_window, policy, || {
            counted.unwrap_or_else(|| estimate_context(&view, &planned_messages(&entries)))
        })
    };
    let prepared = before_request(at, threshold);
    let compaction = runtime.registry().builtins().compaction.clone();
    let task_id = runtime.task_id().erase();
    if prepared == Prepared::Compact {
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
                        threshold: true,
                        forced,
                        note,
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
                // preparation counts. A queued summary is a compaction not yet
                // placed: another would summarize the history it replaces.
                if prepared == (Prepared::Request { background: true })
                    && tx
                        .doc(&LIVE_DOC, conversation_id)
                        .await?
                        .get("compactions")?
                        .is_none()
                    && !has_queued_summary(
                        tx.doc(&INBOX_DOC, conversation_id)
                            .await?
                            .child("items")?
                            .value()?
                            .as_array()
                            .unwrap_or_default(),
                    )
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
                        forced,
                        note,
                    },
                }))
            },
            &cx,
        )
        .await
}

#[expect(
    clippy::too_many_lines,
    reason = "one TS phase, kept whole to read against it"
)]
async fn request(task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let GenerationCheckpoint::Request {
        attempt,
        compacted,
        model: reference,
        thinking_level,
        stream_options,
        cutoff,
        forced,
        note,
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
    let view = runtime
        .context(conversation_id, &cx, ContextOptions { at: Some(cutoff) })
        .await?;
    // The hooks see and may replace the messages and the forced tool; the
    // settings' forced tool is the first value.
    let shaped = Mutex::new(RequestMessages {
        messages: view.messages.clone(),
        force_tool: stream_options.force_tool.clone(),
    });
    let api = runtime.hook_api();
    // A failed hook ends the run: the request it would have shaped never
    // goes out in another form.
    let hooked = runtime
        .hooks()
        .each_required(
            |hooks: &GenerationHooks| hooks.before_request.clone(),
            |hook| {
                let current = shaped
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .clone();
                let pending = hook(&current, &api, &cx);
                let shaped = &shaped;
                async move {
                    if let Some(replaced) = pending.await? {
                        *shaped.lock().unwrap_or_else(PoisonError::into_inner) = replaced;
                    }
                    Ok(())
                }
            },
        )
        .await;
    match hooked {
        Ok(()) => {}
        Err(error) if cx.aborted() => return Err(error),
        Err(error) => {
            return fail_model_error(&runtime, format!("A request hook failed: {error}"), &cx).await
        }
    }
    let RequestMessages {
        mut messages,
        force_tool,
    } = shaped.into_inner().unwrap_or_else(PoisonError::into_inner);
    let mut options = stream_options.simple_stream_options();
    options.stream.request.signal = Some(runtime.signal());
    options.stream.session_id = Some(ensure_provider_session_id(&runtime, &cx).await?);
    options.reasoning = reasoning(thinking_level);
    // The note of a retry after a noted reply (H4.7), then a forced call's
    // soft prompt, end the request; the native flag follows the
    // escalation. None of them is committed to the transcript.
    let force = force_tool.map(|option| Forcing::of(option, &model, options.reasoning));
    let ends = note.iter().map(RetryNote::text);
    for text in ends.chain(force.iter().map(|force| soft_prompt(&force.forced.tool))) {
        messages.push(Message::User(UserMessage {
            content: UserContent::Text(text),
            timestamp: timestamp(runtime.now()?)?,
        }));
    }
    // The native flag of this request: the compiled core decides
    // (`infer_force::flag`, law `infer_force_steps`).
    if let Some(force) = force.as_ref().filter(|force| {
        infer_force::flag(
            forced,
            Offer {
                native: force.escalation.native,
                free: force.escalation.free,
            },
        )
    }) {
        options.tool_choice = Some(ToolChoice::Tool(force.forced.tool.clone()));
    }
    // The retry after a stall (M3) has twice the idle deadline it stalled
    // under: the same deadline would stall the same request again.
    if let Some(RetryNote {
        cause: NoteCause::Stalled { idle_ms },
        ..
    }) = &note
    {
        options.stream.request.stream_idle_timeout_ms = Some(ms_f64(idle_after_stall(*idle_ms)));
    }
    // The time a deferred job of the request may run (H4.4), until its
    // handle gives the provider's expiry: the requested window, else the
    // longest window of the API.
    let window = match stream_options.deferred {
        Some(DeferredRequest::Window(Some(window))) => window,
        Some(DeferredRequest::Window(None) | DeferredRequest::Flag(_)) | None => {
            DeferredWindow::Hours24
        }
    };
    let window_ms = match window {
        DeferredWindow::Minutes15 => 15.0 * 60_000.0,
        DeferredWindow::Hours1 => 60.0 * 60_000.0,
        DeferredWindow::Hours24 => 24.0 * 60.0 * 60_000.0,
    };
    let sent_at = runtime.now()?;
    // A remote provider sees pseudonyms, not the memory's text: the
    // provider runtime scrubs every stream request (`privacy.anonymizeRemote`).
    let message = stream_response(&runtime, &model, messages, options, attempt, &cx).await?;
    let request = Request {
        attempt,
        compacted,
        model: reference,
        cutoff,
        messages: Some(view.messages),
        sent_at,
        deadline: sent_at + window_ms,
        poll: None,
        forced,
        force,
        note,
    };
    classify(&runtime, request, message, &cx).await
}

async fn retry(task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let GenerationCheckpoint::Retry {
        attempt,
        compacted,
        until,
        forced,
        note,
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
                        threshold: false,
                        forced,
                        note,
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
        sent_at,
        deadline,
        failures,
        forced,
        force,
        note,
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
            stream_idle_timeout_ms: runtime.settings().stream.stream_idle_timeout_ms,
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
        sent_at,
        deadline,
        poll: Some(Polled {
            at: poll_at,
            handle,
            failures,
        }),
        forced,
        force,
        note,
    };
    classify(&runtime, request, message, &cx).await
}

/// Cancel the deferred job of `handle` at its provider. A failed
/// cancellation is reported, not raised: the run ends either way.
async fn cancel_job(
    runtime: &Runtime,
    reference: &ModelRef,
    handle: &DeferredHandle,
) -> SessionResult<()> {
    let Some(model) = runtime
        .models()
        .get_model(&reference.provider, &reference.model_id)
    else {
        return Ok(());
    };
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
    Ok(())
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
        return finish_tool_round(&runtime, assistant, tools, task.input.rounds, &cx).await;
    };
    // Sequential round: start the next call and wait for it.
    start_next_call(&runtime, assistant, tools, next, pending.collect(), &cx).await
}

async fn abort(task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let checkpoint = task.checkpoint;
    if let GenerationCheckpoint::Poll { model, handle, .. } = &checkpoint {
        cancel_job(&runtime, model, handle).await?;
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
                    let meta = ToolResultMeta {
                        timestamp: runtime.now()?,
                        duration_ms: None,
                    };
                    append_tool_result(&tx, conversation_id, call, &result, meta).await?;
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

/// How the compaction a preparation waited for ended, with the failure
/// text of one that did not complete.
fn compaction_end(outcome: Option<&TaskOutcome<CompactionResult>>) -> (Compacted, Option<String>) {
    match outcome {
        Some(TaskOutcome::Completed { result }) if result.entry_id.is_some() => {
            (Compacted::Entry, None)
        }
        None | Some(TaskOutcome::Completed { .. }) => (Compacted::Nothing, None),
        Some(TaskOutcome::Failed { error, .. } | TaskOutcome::Faulted { error }) => (
            Compacted::Failed,
            Some(format!("Compaction failed: {}", error.message)),
        ),
        Some(TaskOutcome::Orphaned { reason }) => (
            Compacted::Failed,
            Some(format!("Compaction failed: {reason}")),
        ),
        Some(TaskOutcome::Aborted { .. }) => {
            (Compacted::Failed, Some("Compaction was aborted".to_owned()))
        }
    }
}

/// Which threshold compaction preparation starts before its request (spec
/// §8.3): [`threshold_for`] the request's input `tokens`, and only when
/// range selection finds a cut. `tokens` runs only when the policy and the
/// window let the check run (else no context is over a threshold, law
/// `infer_threshold_over_exact`). The caller starts a background one only
/// while no compaction is listed.
fn threshold_compaction(
    view: &ContextView,
    context_window: u64,
    policy: &CompactionPolicy,
    tokens: impl FnOnce() -> u64,
) -> Option<Threshold> {
    if !policy.enabled || context_window == 0 {
        return None;
    }
    threshold_for(tokens(), context_window, policy)
        .filter(|_| select_cut(view, policy.keep_window(context_window)).is_some())
}

/// The model messages of the system entries preparation plans to append.
fn planned_messages(planned: &[SystemDraft]) -> Vec<Message> {
    planned
        .iter()
        .flat_map(|entry| entry.model.iter().flatten().cloned())
        .collect()
}

/// The input tokens of the request being prepared, by the provider's own
/// counter ([`ThresholdTokens::Provider`]): the transcript and the planned
/// system entries, in the context the request sends. The count request
/// takes the request options of the stream (`stream`: timeout, retries,
/// headers), so it obeys the same limits and sends the same headers. When
/// the provider has no counter or the count fails, this logs a warning and
/// returns the local estimate: the caller asked for that choice, so it is
/// never silent.
#[tracing::instrument(skip_all, fields(provider = %model.provider, model = %model.id))]
async fn provider_tokens(
    runtime: &Runtime,
    model: &Model,
    stream: &ConversationStreamOptions,
    view: &ContextView,
    planned: &[SystemDraft],
) -> u64 {
    let extra = planned_messages(planned);
    let messages = view.messages.iter().chain(&extra).cloned().collect();
    // The count request reaches the provider: it reads pseudonyms too.
    let messages = if runtime.settings().privacy_anonymize_remote
        && !eukhe_ai::privacy::is_local(&model.base_url)
    {
        eukhe_ai::privacy::Scrubber::new(&runtime.settings().privacy_terms).scrub_messages(messages)
    } else {
        messages
    };
    let mut request = stream.simple_stream_options().stream.request;
    request.signal = Some(runtime.signal());
    let options = ModelsCapabilityOptions::from(CapabilityOptions { request });
    match runtime
        .models()
        .count_tokens(model, request_context(messages), options)
        .await
    {
        Ok(count) => count.input_tokens,
        Err(error) => {
            tracing::warn!(
                provider = %model.provider,
                model = %model.id,
                %error,
                "provider token count failed; the compaction threshold uses the local estimate"
            );
            estimate_context(view, &extra)
        }
    }
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

/// The limits of the run's decisions, read when they are decided:
/// `max_wait` is the ms the request's deferred job may run.
fn limits(settings: &Settings, max_wait: u64) -> Limits {
    Limits {
        max_rounds: settings.max_tool_rounds,
        max_wait,
        max_retries: settings.retry.max_retries,
        max_notes: MAX_NOTES,
    }
}

/// A span of the harness clock as whole ms; a negative span is 0.
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_sign_loss,
    reason = "the cast saturates: a negative span is 0, a span past u64::MAX is u64::MAX"
)]
fn ms_u64(span: f64) -> u64 {
    span as u64
}

/// Whole ms as a time or span of the harness clock.
#[expect(
    clippy::cast_precision_loss,
    reason = "a time or deadline in ms, far below 2^53, where the cast is exact"
)]
fn ms_f64(ms: u64) -> f64 {
    ms as f64
}

/// Classify a terminal provider message and commit the step it leads to
/// ([`after_reply`], LAWS.bend H4), clearing the partial.
#[expect(
    clippy::too_many_lines,
    reason = "one TS function, kept whole to read against it"
)]
async fn classify(
    runtime: &Runtime,
    mut request: Request,
    mut message: AssistantMessage,
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
    let deferred = if message.stop_reason == StopReason::Deferred {
        message.deferred.take()
    } else {
        None
    };
    if deferred.is_none() {
        let api = runtime.hook_api();
        runtime
            .hooks()
            .each(
                |hooks: &GenerationHooks| hooks.after_response.clone(),
                |hook| hook(&message, &api, cx),
            )
            .await?;
    }
    let mut calls: Vec<ToolCall> = message
        .content
        .iter()
        .filter_map(|content| match content {
            AssistantContentBlock::ToolCall(call) => Some(call.clone()),
            AssistantContentBlock::Text(_) | AssistantContentBlock::Thinking(_) => None,
        })
        .collect();
    // The retry and compaction policies govern the next attempt, so they are
    // read now rather than pinned at preparation.
    let settings = runtime.settings();
    let polled = request.poll.take();
    // A failed fetch of a deferred job (H10): the job can still run, so a
    // new request would pay for the work two times. A retryable failure
    // below `retry.maxRetries` failures in a row polls the same job again,
    // after the retry policy's wait (never before the server's wait); any
    // other failure cancels the job, then fails the run.
    let mut repoll_wait = None;
    let mut cancelled = false;
    let deferred = match polled
        .as_ref()
        .filter(|_| message.stop_reason == StopReason::Error)
    {
        None => deferred,
        Some(poll) => {
            let failure = PollFailure {
                retryable: settings.retry.enabled && is_retryable_assistant_error(&message),
                failures: poll.failures,
            };
            let delay = RetryDelay {
                base_delay_ms: settings.retry.base_delay_ms,
                max_agent_delay_ms: settings.retry.max_agent_delay_ms,
            };
            repoll_wait = match failure.next(settings.retry.max_retries) {
                FailedPoll::Repoll => match retry_wait(delay, poll.failures + 1, &message) {
                    RetryWait::After(wait) => Some(wait),
                    RetryWait::Refused { server_ms, cap_ms } => {
                        let error = message.error_message.as_deref().unwrap_or_default();
                        message.error_message = Some(RetryWait::refusal(server_ms, cap_ms, error));
                        None
                    }
                },
                FailedPoll::Cancel => None,
            };
            if repoll_wait.is_none() {
                cancel_job(runtime, &request.model, &poll.handle).await?;
                cancelled = true;
            }
            repoll_wait.map(|_| poll.handle.clone())
        }
    };
    let (reply, cause) = if let Some(handle) = &deferred {
        (Reply::Deferred(handle), None)
    } else if cancelled {
        (
            Reply::Error {
                retryable: false,
                noted: false,
            },
            None,
        )
    } else if matches!(
        message.stop_reason,
        StopReason::Stop | StopReason::Length | StopReason::ToolUse
    ) {
        // Tool calls leaked as text (H4.8): a reply with no tool call has
        // each text block scanned for tool-call markup.
        let mut leaked = Vec::new();
        let mut broken = None;
        if calls.is_empty() {
            for (index, content) in message.content.iter().enumerate() {
                match content {
                    AssistantContentBlock::Text(text) => match scan(&text.text) {
                        Leak::None => {}
                        Leak::Calls {
                            markup,
                            calls,
                            text,
                        } => leaked.push((index, markup, calls, text)),
                        Leak::Broken { markup, reason } => {
                            broken = broken.or(Some((markup, reason)));
                        }
                    },
                    AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => {}
                }
            }
        }
        // The leak and the calls read the request's context: the tools it
        // offered, the rounds before.
        if (!calls.is_empty() || !leaked.is_empty()) && request.messages.is_none() {
            let context = ContextOptions {
                at: Some(request.cutoff),
            };
            request.messages = Some(
                runtime
                    .context(conversation_id, cx, context)
                    .await?
                    .messages,
            );
        }
        let context = request.messages.as_deref().unwrap_or_default();
        if broken.is_none() && !leaked.is_empty() {
            let offered: HashSet<String> = get_current_tools(context)
                .into_iter()
                .map(|tool| tool.name)
                .collect();
            let unknown = leaked.iter().find_map(|(_, markup, calls, _)| {
                calls
                    .iter()
                    .find(|call| !offered.contains(&call.name))
                    .map(|call| (*markup, format!("it names no offered tool {:?}", call.name)))
            });
            if unknown.is_some() {
                broken = unknown;
            } else {
                // Every leaked call parsed and names an offered tool: the
                // calls are rebuilt, and the markup leaves the text.
                for (index, _, leaked_calls, text) in leaked {
                    if let Some(AssistantContentBlock::Text(block)) = message.content.get_mut(index)
                    {
                        block.text = text;
                    }
                    for call in leaked_calls {
                        calls.push(ToolCall {
                            id: format!("leak_{}_{attempt}_{}", request.cutoff, calls.len()),
                            name: call.name,
                            arguments: call.arguments,
                            thought_signature: None,
                            namespace: None,
                        });
                    }
                }
                message.content.retain(|content| match content {
                    AssistantContentBlock::Text(text) => !text.text.trim().is_empty(),
                    AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => true,
                });
                message
                    .content
                    .extend(calls.iter().cloned().map(AssistantContentBlock::ToolCall));
                message.stop_reason = StopReason::ToolUse;
            }
        }
        let reply = Ended {
            text: message.content.iter().any(|content| match content {
                AssistantContentBlock::Text(text) => !text.text.trim().is_empty(),
                AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => false,
            }),
            calls: !calls.is_empty(),
        }
        .reply();
        // A stuck reply gets its recovery (H4.8): the note of the request
        // counts the notes of each recovery in a row.
        let stuck = match reply {
            Reply::Calls => Some(Stuck::Calls {
                rounds: rounds_in_a_row(context, &calls),
            }),
            Reply::Error { .. } if message.stop_reason == StopReason::Length => Some(Stuck::Length),
            Reply::Text => broken.is_some().then_some(Stuck::Leak),
            Reply::Error { .. } | Reply::Deferred(_) | Reply::Overflow { .. } => None,
        };
        let thinking: usize = message
            .content
            .iter()
            .map(|content| match content {
                AssistantContentBlock::Thinking(thinking) => thinking.thinking.chars().count(),
                AssistantContentBlock::Text(_) | AssistantContentBlock::ToolCall(_) => 0,
            })
            .sum();
        let only = if thinking > 0 {
            format!(", only {thinking} characters of thinking")
        } else {
            String::new()
        };
        let no_answer = format!(
            "The model gave no answer: its reply (stop reason {}) has no text and no tool call{only}",
            message.stop_reason.as_str()
        );
        // A failed reply fails before it is appended: the user sees why,
        // and a retry leaves it out of the next request's context and ends
        // that request with a note (H4.7).
        let (reply, cause, error) = match stuck {
            None => match reply {
                Reply::Error { .. } => (reply, Some(NoteCause::NoAnswer), Some(no_answer)),
                Reply::Text | Reply::Calls | Reply::Deferred(_) | Reply::Overflow { .. } => {
                    (reply, None, None)
                }
            },
            Some(stuck) => {
                let note = request.note.as_ref().and_then(|note| note.cause.recovery());
                let redo = Reply::Error {
                    retryable: false,
                    noted: true,
                };
                let quit = Reply::Error {
                    retryable: false,
                    noted: false,
                };
                let names = calls
                    .iter()
                    .map(|call| call.name.as_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                match (stuck, recover(stuck, note, &CAPS)) {
                    (Stuck::Calls { .. }, Act::Run) => (Reply::Calls, None, None),
                    (Stuck::Calls { rounds }, Act::Redo { row }) => {
                        let repeated = calls
                            .iter()
                            .map(|call| {
                                let mut arguments = canonical_arguments(&call.arguments);
                                if let Some((cut, _)) =
                                    arguments.char_indices().nth(ARGUMENTS_SHOWN)
                                {
                                    arguments.truncate(cut);
                                    arguments.push('…');
                                }
                                RepeatedCall {
                                    tool: call.name.clone(),
                                    arguments,
                                }
                            })
                            .collect();
                        let error = format!(
                            "The model made the same tool calls ({names}) with the same results \
                             {rounds} times in a row; the harness did not run them again"
                        );
                        let cause = NoteCause::Redirect {
                            calls: repeated,
                            rounds: rounds.get(),
                            row,
                        };
                        (redo, Some(cause), Some(error))
                    }
                    (Stuck::Calls { rounds }, Act::Quit) => {
                        let error = format!(
                            "The model made the same tool calls ({names}) with the same results \
                             {rounds} times in a row, after {REDIRECT_NOTES} redirect notes; the \
                             harness did not run them again"
                        );
                        (quit, None, Some(error))
                    }
                    (Stuck::Length, Act::Redo { row }) => {
                        let cause = NoteCause::Length {
                            tokens: message.usage.output,
                            row,
                        };
                        (redo, Some(cause), Some(no_answer))
                    }
                    (Stuck::Length, Act::Quit) => {
                        let error = format!(
                            "{no_answer}. The model hit the output limit while it was still \
                             reasoning after {LENGTH_NOTES} length notes in a row: use a \
                             different model or raise the model's max output tokens"
                        );
                        (quit, None, Some(error))
                    }
                    (Stuck::Leak, Act::Redo { row }) => match broken {
                        Some((markup, reason)) => {
                            let error = format!(
                                "The model wrote a tool call as {} markup in its text, and the \
                                 harness could not read it ({reason})",
                                markup.as_str()
                            );
                            let cause = NoteCause::Leaked {
                                markup: markup.as_str().to_owned(),
                                reason,
                                row,
                            };
                            (redo, Some(cause), Some(error))
                        }
                        None => (reply, None, None),
                    },
                    // At its cap, a leak answers as text.
                    (Stuck::Leak, Act::Stand | Act::Quit) => (Reply::Text, None, None),
                    (Stuck::Length | Stuck::Leak, Act::Run)
                    | (Stuck::Length | Stuck::Calls { .. }, Act::Stand) => (reply, None, None),
                }
            }
        };
        if let Some(error) = error {
            message.error_message = Some(error);
            message.stop_reason = StopReason::Error;
        }
        (reply, cause)
    } else if message.stop_reason == StopReason::Error && is_context_overflow(&message, None) {
        // An overflow is never retried: only a compaction can make the next
        // request fit.
        let cut = compacted.is_none()
            && settings.compaction.enabled
            && select_cut(
                &runtime
                    .context(
                        conversation_id,
                        cx,
                        ContextOptions {
                            at: Some(request.cutoff),
                        },
                    )
                    .await?,
                settings.compaction.keep_window(
                    runtime
                        .models()
                        .get_model(&request.model.provider, &request.model.model_id)
                        .map_or(0, |model| model.context_window),
                ),
            )
            .is_some();
        (Reply::Overflow { cut }, None)
    } else {
        // A stream the repetition guard cut is noted (H4.7): its retry
        // names the repeated line in its note. So is a stream that stalled
        // (M3): its retry, sent at once, has a note and twice the idle
        // deadline.
        let cause = repeated_lines(&message)
            .map(|RepeatedLines { period, line }| NoteCause::Repeated { period, line })
            .or_else(|| stalled_idle_ms(&message).map(|idle_ms| NoteCause::Stalled { idle_ms }));
        let reply = Reply::Error {
            retryable: message.stop_reason == StopReason::Error
                && is_retryable_assistant_error(&message)
                && settings.retry.enabled,
            noted: cause.is_some(),
        };
        (reply, cause)
    };
    // A provider that gives the job's expiry with its handle sets the
    // job's deadline (H4.4).
    let deadline = deferred
        .as_ref()
        .and_then(|handle| handle.expires_at)
        .map_or(request.deadline, ms_f64);
    let sent_at = request.sent_at;
    let at = Counts {
        attempt,
        notes: request.note.as_ref().map_or(0, |note| note.spent),
        waited: ms_u64(runtime.now()? - sent_at),
        compacted: compacted.is_some(),
    };
    // A forced call judges each answer: one without the call is kept in the
    // transcript, any other calls it made get `not_run` results, and it is
    // asked again while retries remain, else it fails the run. Deferred,
    // failed, and overflowing replies go on as usual, and so does a reply
    // with no text and no tool call (H4.7): it is a failed reply.
    let forced = request.forced;
    if let Some(force) = request
        .force
        .as_ref()
        .filter(|_| matches!(reply, Reply::Text | Reply::Calls))
    {
        let tries = forced + 1;
        let reply = if calls.iter().any(|call| call.name == force.forced.tool) {
            ForceReply::Called
        } else {
            ForceReply::Missed
        };
        match infer_force::after(forced, force.escalation.retries, reply) {
            ForceStep::Called => {}
            step @ (ForceStep::Retry | ForceStep::Failed) => {
                let tool = &force.forced.tool;
                let skipped: Vec<_> = calls
                    .iter()
                    .map(|call| {
                        let text = format!(
                            "Tool {} was not run: this turn had to call {tool}",
                            call.name
                        );
                        (call.clone(), harness_error("not_run", &text))
                    })
                    .collect();
                let meta = ToolResultMeta {
                    timestamp: runtime.now()?,
                    duration_ms: None,
                };
                let error = (step == ForceStep::Failed).then(|| ForcedToolError::NotCalled {
                    tool: tool.clone(),
                    attempts: tries,
                });
                return runtime
                    .commit(
                        move |tx, _current| async move {
                            let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                            append_assistant(&tx, conversation_id, message).await?;
                            for (call, result) in &skipped {
                                append_tool_result(&tx, conversation_id, call, result, meta)
                                    .await?;
                            }
                            let Some(error) = error else {
                                live.delete("generation")?;
                                return Ok(Some(Next::Running {
                                    checkpoint: GenerationCheckpoint::Prepare {
                                        attempt,
                                        compacted,
                                        overflow: None,
                                        threshold: false,
                                        forced: tries,
                                        // The kept answer grows the context:
                                        // the next request is a new one.
                                        note: None,
                                    },
                                }));
                            };
                            end_run(
                                &tx,
                                &live,
                                task_id,
                                &SubmissionSettlement::Unanswered {
                                    reason: "forced_tool".to_owned(),
                                    detail: Some(to_json(&error)?),
                                },
                            )?;
                            failed(error.to_string(), "forced_tool").map(Some)
                        },
                        cx,
                    )
                    .await;
            }
        }
    }
    match after_reply(at, reply, &limits(&settings, ms_u64(deadline - sent_at))) {
        Step::Poll(handle) => {
            let handle = handle.clone();
            let wait = repoll_wait
                .unwrap_or_else(|| handle.poll_after_ms.unwrap_or(DEFAULT_POLL_AFTER_MS));
            let after = runtime.now()? + wait;
            let poll_at = after.max(
                polled
                    .as_ref()
                    .map_or(f64::NEG_INFINITY, |poll| poll.at + 1.0),
            );
            // A retried fetch counts one more failure in a row; a reply
            // that is still deferred sets the count to 0.
            let failures = repoll_wait
                .and(polled.as_ref())
                .map_or(0, |poll| poll.failures + 1);
            let model = request.model;
            let cutoff = request.cutoff;
            let force = request.force;
            let note = request.note;
            runtime
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
                                sent_at,
                                deadline,
                                failures,
                                forced,
                                force,
                                note,
                            },
                        }))
                    },
                    cx,
                )
                .await
        }
        Step::Fail(Failure::Polls) => {
            // The job may still run: cancel it before the run fails.
            if let Some(handle) = &deferred {
                cancel_job(runtime, &request.model, handle).await?;
            }
            let text = format!(
                "The model's deferred response was not ready by its deadline, {} s after the \
                 request",
                ms_u64(deadline - sent_at) / 1000
            );
            fail_model_error(runtime, text, cx).await
        }
        Step::Tools => start_tool_round(runtime, request, message, calls, cx).await,
        Step::Answer => answer(runtime, message, cx).await,
        Step::Compact => {
            let text = message
                .error_message
                .clone()
                .unwrap_or_else(|| "Context overflow".to_owned());
            let compaction = runtime.registry().builtins().compaction.clone();
            let note = request.note;
            runtime
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
                                threshold: false,
                                forced,
                                note,
                            },
                            on: vec![child.erase()],
                            policy: JoinPolicy::AllSettled,
                        }))
                    },
                    cx,
                )
                .await
        }
        step @ (Step::Retry | Step::Note | Step::Fail(Failure::Model)) => {
            let policy = settings.retry;
            let note = retry_note(at, cause, request.note);
            // A noted retry is a new request, due at once (R2): nothing is
            // overloaded. A transient retry's wait is drawn once and
            // committed with the retry checkpoint, so a replay resumes at
            // the same instant: full jitter under the policy's step, never
            // before the server's Retry-After. A server wait above the cap
            // (H5) sends no retry: a retry before the server's time cannot
            // succeed, so the run fails at once with the server's time.
            let (retry, until) = match step {
                Step::Retry => {
                    let delay = RetryDelay {
                        base_delay_ms: policy.base_delay_ms,
                        max_agent_delay_ms: policy.max_agent_delay_ms,
                    };
                    let retries = attempt.saturating_sub(u64::from(at.notes));
                    let retries = u32::try_from(retries).unwrap_or(u32::MAX);
                    match retry_wait(delay, retries, &message) {
                        RetryWait::After(wait) => (true, runtime.now()? + wait),
                        RetryWait::Refused { server_ms, cap_ms } => {
                            let error = message.error_message.as_deref().unwrap_or_default();
                            message.error_message =
                                Some(RetryWait::refusal(server_ms, cap_ms, error));
                            (false, 0.0)
                        }
                    }
                }
                Step::Note => (true, runtime.now()?),
                Step::Answer | Step::Tools | Step::Poll(..) | Step::Compact | Step::Fail(_) => {
                    (false, 0.0)
                }
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
                                    forced,
                                    note,
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
    }
}
