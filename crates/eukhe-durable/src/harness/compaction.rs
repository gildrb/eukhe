//! Built-in compaction task (`harness/compaction.ts`, spec §8.7): select an
//! old prefix of the model context, summarize it, and place a summary entry
//! whose `head` is the first kept entry. A compaction the generation owns
//! blocks it and appends directly; a conversation-owned one places its
//! summary through a write submission.
//!
//! `createCompaction` lives in [`crate::harness::live::run`] with the other
//! run helpers, so admission and conversations do not depend on this module.

mod prompt;
mod range;
#[cfg(test)]
mod tests;

use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::delta::Draft;
use eukhe_chord::json::to_json;
use eukhe_pi_ai::utils::retry::{is_retryable_assistant_error, retry_delay_ms, RetryDelay};
use eukhe_types::pi_ai::{
    AssistantMessage, CacheRetention, Context as PiContext, Message, ModelThinkingLevel,
    StopReason, SystemContent, SystemMessage, TextContent, ThinkingLevel, UserContent,
    UserContentBlock, UserMessage,
};
use serde::{Deserialize, Serialize};

pub use self::prompt::serialize_conversation;
use self::prompt::{
    summary_failure, summary_prompt, summary_text, SUMMARIZATION_SYSTEM_PROMPT, SUMMARY_PREFIX,
    SUMMARY_SUFFIX,
};
pub use self::range::{estimate_context, select_cut, summarized_messages};
use crate::entries::{CompactionData, COMPACTION_ENTRY};
use crate::harness::inbox::QueueModes;
use crate::harness::live::run::{timestamp, CompactionInput};
use crate::harness::live::{compaction_status, remove_compaction_status, LiveRetry, LIVE_DOC};
use crate::harness::provider::ensure_provider_session_id;
use crate::harness::submissions::admit_submission;
use crate::harness::types::CompactionSnapshot;
use crate::harness::types::{
    CompactionDecision, CompactionHooks, CompactionRequest, CompactionResult, ContextOptions,
    ConversationStreamOptions, ModelRef, SubmissionDraft, WriteSubmissionDraft,
};
use crate::harness::usage::{record_usage, UsageBucket};
use crate::session::{SessionError, SessionResult, Tx};
use crate::tasks::{define_task, NextTaskState, RunningTask, Task, TaskDefinition, TaskRuntime};
use crate::types::{EntryDraft, EntryHead, EntryId, TaskOutcome, TaskOutcomeError};

/// The pinned summarization request.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SummaryRequest {
    pub attempt: u64,
    pub model: ModelRef,
    pub thinking_level: ModelThinkingLevel,
    pub stream_options: ConversationStreamOptions,
    pub max_tokens: f64,
    /// Newest entry of the context the range was selected from.
    pub tail: EntryId,
    /// First entry kept verbatim; the summary's `head`.
    pub first_kept: EntryId,
}

/// The pinned request of a durable backoff and when it ends.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RetryRequest {
    #[serde(flatten)]
    pub request: SummaryRequest,
    pub until: f64,
}

/// Checkpoint of `pi.compaction`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "phase", rename_all = "camelCase")]
pub enum CompactionCheckpoint {
    /// `{ phase: "select" }`.
    Select,
    /// `{ phase: "summarize", ...request }`.
    Summarize(SummaryRequest),
    /// `{ phase: "retry", ...request, until }`.
    Retry(RetryRequest),
}

/// The typed `pi.compaction` task.
pub type CompactionTask =
    Task<CompactionInput, CompactionCheckpoint, CompactionResult, CompactionHooks>;

type Runtime =
    TaskRuntime<CompactionInput, CompactionCheckpoint, CompactionResult, CompactionHooks>;
type Current = RunningTask<CompactionInput, CompactionCheckpoint, CompactionResult>;
type Next = NextTaskState<CompactionCheckpoint, CompactionResult>;

/// Built-in compaction task (spec §8.7): select an old prefix of the model
/// context, summarize it, and place a summary entry whose `head` is the
/// first kept entry.
pub static COMPACTION_TASK: LazyLock<CompactionTask> = LazyLock::new(|| {
    define_task(
        TaskDefinition::new(
            "pi.compaction",
            1,
            |_input: &CompactionInput| Ok(CompactionCheckpoint::Select),
            abort,
        )
        .phase("select", select)
        .phase("summarize", summarize)
        .phase("retry", retry),
    )
});

async fn select(task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let conversation_id = runtime.conversation_id();
    let agent = runtime.agent(&cx).await?;
    let settings = runtime.settings();
    let reference = agent.model.clone();
    let model = reference.as_ref().and_then(|reference| {
        runtime
            .models()
            .get_model(&reference.provider, &reference.model_id)
    });
    let (Some(reference), Some(model)) = (reference.clone(), model) else {
        return fail_no_model(&runtime, reference.as_ref(), &cx).await;
    };
    let policy = settings.compaction;
    let view = runtime
        .context(conversation_id, &cx, ContextOptions::default())
        .await?;
    let Some(cut) = select_cut(&view, policy.keep_recent_tokens) else {
        return complete(&runtime, &cx).await;
    };
    let first_kept = view.entries[cut].id;
    let CompactionInput {
        reason,
        instructions,
    } = task.input;
    let compaction = CompactionRequest {
        reason,
        entries: view.entries[..cut].to_vec(),
        messages: summarized_messages(&view, cut),
        first_kept,
        instructions,
    };
    let decision: Arc<Mutex<Option<CompactionDecision>>> = Arc::default();
    let api = runtime.hook_api();
    runtime
        .hooks()
        .each(
            |hooks: &CompactionHooks| hooks.before_compact.clone(),
            |hook| {
                // Later hooks are not asked once one decided.
                let pending = decision
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .is_none()
                    .then(|| hook(&compaction, &api, &cx));
                let decision = Arc::clone(&decision);
                async move {
                    if let Some(pending) = pending {
                        let decided = pending.await?;
                        let mut slot = decision.lock().unwrap_or_else(PoisonError::into_inner);
                        if slot.is_none() {
                            *slot = decided;
                        }
                    }
                    Ok(())
                }
            },
        )
        .await?;
    let decision = decision
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take();
    match decision {
        Some(CompactionDecision::Decline) => return complete(&runtime, &cx).await,
        Some(CompactionDecision::Summary(summary)) => {
            return place(&runtime, first_kept, summary, None, &cx).await;
        }
        Some(CompactionDecision::SummaryWithData(summary, data)) => {
            return place(&runtime, first_kept, summary, Some(data), &cx).await;
        }
        None => {}
    }
    let tail = view
        .entries
        .iter()
        .map(|entry| entry.id)
        .fold(first_kept, std::cmp::Ord::max);
    let request = SummaryRequest {
        attempt: 1,
        model: reference,
        thinking_level: agent.thinking_level,
        stream_options: settings.stream,
        max_tokens: max_tokens(policy.reserve_tokens, model.max_tokens),
        tail,
        first_kept,
    };
    runtime
        .commit(
            move |_tx, _current| async move {
                Ok(Some(NextTaskState::Running {
                    checkpoint: CompactionCheckpoint::Summarize(request),
                }))
            },
            &cx,
        )
        .await
}

/// `min(floor(0.8 * reserveTokens), model.maxTokens)`, the model's value
/// only when positive.
fn max_tokens(reserve_tokens: f64, model_max_tokens: u64) -> f64 {
    let budget = (0.8 * reserve_tokens).floor();
    if model_max_tokens > 0 {
        budget.min(range::js_number(model_max_tokens))
    } else {
        budget
    }
}

/// The pinned `maxTokens` as pi-ai's integer option. TS forwards any number;
/// pi-ai's Rust options hold only non-negative integers, so a negative pin
/// (from a negative `reserveTokens`) is rejected instead of coerced.
fn request_max_tokens(max_tokens: f64) -> SessionResult<u64> {
    if max_tokens.fract() != 0.0
        || !(0.0..=eukhe_chord::json::MAX_SAFE_INTEGER).contains(&max_tokens)
    {
        return Err(SessionError::type_error(format!(
            "maxTokens {max_tokens} is not a non-negative integer"
        )));
    }
    #[expect(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "checked above: a non-negative integer within 2^53"
    )]
    Ok(max_tokens as u64)
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

/// The checkpoint a phase handler was dispatched for; the scheduler
/// dispatches by `phase`, so another variant is a corrupt record.
fn phase_mismatch(expected: &str) -> SessionError {
    SessionError::type_error(format!(
        "pi.compaction checkpoint is not in phase {expected}"
    ))
}

async fn summarize(task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let CompactionCheckpoint::Summarize(request) = task.checkpoint else {
        return Err(phase_mismatch("summarize"));
    };
    let Some(model) = runtime
        .models()
        .get_model(&request.model.provider, &request.model.model_id)
    else {
        return fail_no_model(&runtime, Some(&request.model), &cx).await;
    };
    let conversation_id = runtime.conversation_id();
    // The context at `tail` is immutable, so this is the range `select` chose.
    let view = runtime
        .context(
            conversation_id,
            &cx,
            ContextOptions {
                at: Some(request.tail),
            },
        )
        .await?;
    // TS `findIndex` yields -1 when absent, and `slice(0, -1)` drops the last
    // contribution.
    let cut = view
        .entries
        .iter()
        .position(|entry| entry.id == request.first_kept)
        .unwrap_or_else(|| view.contributions.len().saturating_sub(1));
    let now = timestamp(runtime.now()?)?;
    let messages = vec![
        Message::System(SystemMessage {
            content: SystemContent::Text(SUMMARIZATION_SYSTEM_PROMPT.to_owned()),
            sections: None,
            tools_added: None,
            tools_removed: None,
            timestamp: now,
        }),
        Message::User(UserMessage {
            content: UserContent::Blocks(vec![UserContentBlock::Text(TextContent::new(
                summary_prompt(
                    &summarized_messages(&view, cut),
                    task.input.instructions.as_deref(),
                ),
            ))]),
            timestamp: now,
        }),
    ];
    let mut options = ConversationStreamOptions {
        deferred: None,
        ..request.stream_options.clone()
    }
    .simple_stream_options();
    options.stream.cache_retention = Some(CacheRetention::None);
    options.stream.max_tokens = Some(request_max_tokens(request.max_tokens)?);
    options.stream.request.signal = Some(runtime.signal());
    options.stream.session_id = Some(ensure_provider_session_id(&runtime, &cx).await?);
    options.reasoning = reasoning(request.thinking_level);
    let message = runtime
        .models()
        .complete_simple(
            &model,
            PiContext {
                system_prompt: None,
                messages,
                tools: None,
            },
            options.into(),
        )
        .await;
    // An abort mark or close: the abort invocation or the reopened task
    // handles the committed state.
    runtime
        .signal()
        .throw_if_aborted()
        .map_err(SessionError::Aborted)?;
    classify(runtime, request, message, &cx).await
}

/// Classify a summarization response in one commit that adds its usage to
/// `pi.usage`: place a summary, back off for a retryable error the retry
/// policy allows, or fail with `model_error`.
async fn classify(
    runtime: Runtime,
    request: SummaryRequest,
    message: AssistantMessage,
    cx: &Context,
) -> SessionResult<()> {
    let conversation_id = runtime.conversation_id();
    let summary = summary_text(&message);
    let policy = runtime.settings().retry;
    let retry = message.stop_reason == StopReason::Error
        && is_retryable_assistant_error(&message)
        && policy.enabled
        && request.attempt <= u64::from(policy.max_retries);
    let until = if retry {
        let attempt = u32::try_from(request.attempt).unwrap_or(u32::MAX);
        runtime.now()?
            + retry_delay_ms(
                RetryDelay {
                    base_delay_ms: policy.base_delay_ms,
                    max_agent_delay_ms: policy.max_agent_delay_ms,
                },
                attempt,
            )
    } else {
        0.0
    };
    let commit_runtime = runtime.clone();
    runtime
        .commit(
            move |tx, current| async move {
                let runtime = commit_runtime;
                let key = format!("{}/{}", message.provider, message.model);
                record_usage(
                    &tx,
                    conversation_id,
                    UsageBucket::Models,
                    &key,
                    &message.usage,
                )
                .await?;
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                if let Some(summary) = summary {
                    return place_summary(
                        &tx,
                        &runtime,
                        &current,
                        &live,
                        request.first_kept,
                        &summary,
                        None,
                    )
                    .await
                    .map(Some);
                }
                if retry {
                    if let Some(status) = compaction_status(&live, runtime.task_id().erase())? {
                        let retry = LiveRetry {
                            at: until,
                            error: message.error_message.clone().unwrap_or_default(),
                        };
                        status.set("retry", to_json(&retry)?)?;
                    }
                    return Ok(Some(NextTaskState::Running {
                        checkpoint: CompactionCheckpoint::Retry(RetryRequest { request, until }),
                    }));
                }
                remove_compaction_status(&live, runtime.task_id().erase())?;
                Ok(Some(failed(summary_failure(&message), "model_error")?))
            },
            cx,
        )
        .await
}

async fn retry(task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let CompactionCheckpoint::Retry(RetryRequest { request, until }) = task.checkpoint else {
        return Err(phase_mismatch("retry"));
    };
    runtime.sleep(until, &cx).await?;
    let attempt = request.attempt + 1;
    let conversation_id = runtime.conversation_id();
    let task_id = runtime.task_id().erase();
    runtime
        .commit(
            move |tx, _current| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                if let Some(status) = compaction_status(&live, task_id)? {
                    status.set("attempt", to_json(&attempt)?)?;
                    status.delete("retry")?;
                }
                Ok(Some(NextTaskState::Running {
                    checkpoint: CompactionCheckpoint::Summarize(SummaryRequest {
                        attempt,
                        ..request
                    }),
                }))
            },
            &cx,
        )
        .await
}

async fn abort(_task: Current, runtime: Runtime, cx: Context) -> SessionResult<()> {
    let conversation_id = runtime.conversation_id();
    let task_id = runtime.task_id().erase();
    runtime
        .commit(
            move |tx, _current| async move {
                remove_compaction_status(&tx.doc(&LIVE_DOC, conversation_id).await?, task_id)?;
                Ok(Some(NextTaskState::Terminal {
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

/// Place a summary supplied by a hook in its own commit. `extra` carries
/// additional `pi.compaction` data fields (eukhe addition: the harness
/// digest snapshot).
async fn place(
    runtime: &Runtime,
    first_kept: EntryId,
    summary: String,
    extra: Option<CompactionSnapshot>,
    cx: &Context,
) -> SessionResult<()> {
    let commit_runtime = runtime.clone();
    runtime
        .commit(
            move |tx, current| async move {
                let runtime = commit_runtime;
                let live = tx.doc(&LIVE_DOC, runtime.conversation_id()).await?;
                place_summary(&tx, &runtime, &current, &live, first_kept, &summary, extra)
                    .await
                    .map(Some)
            },
            cx,
        )
        .await
}

/// Place the summary entry and complete (spec §8.7). A blocking compaction,
/// owned by its generation, appends it: the generation holds the run and
/// waits. A conversation-owned one admits it as a write submission, placed
/// at once when idle, otherwise at the next boundary, or settled `stale`.
///
/// REMINDER: nothing else may append to a busy conversation, so every
/// non-blocking summary goes through admission.
async fn place_summary(
    tx: &Tx,
    runtime: &Runtime,
    current: &Current,
    live: &Draft,
    first_kept: EntryId,
    summary: &str,
    extra: Option<CompactionSnapshot>,
) -> SessionResult<Next> {
    let task_id = runtime.task_id().erase();
    let conversation_id = runtime.conversation_id();
    remove_compaction_status(live, task_id)?;
    let text = format!("{SUMMARY_PREFIX}{summary}{SUMMARY_SUFFIX}");
    let snapshot = extra.as_ref().map_or((None, None), |snapshot| {
        (
            Some(snapshot.harness_digest.clone()),
            Some(snapshot.harness_state_fingerprint.clone()),
        )
    });
    let entry = EntryDraft {
        kind: COMPACTION_ENTRY.kind().to_owned(),
        model: Some(vec![Message::User(UserMessage {
            content: UserContent::Blocks(vec![UserContentBlock::Text(TextContent::new(text))]),
            timestamp: timestamp(runtime.now()?)?,
        })]),
        data: Some(to_json(&CompactionData {
            reason: current.input.reason,
            harness_digest: snapshot.0,
            harness_state_fingerprint: snapshot.1,
        })?),
        head: Some(EntryHead::Entry(first_kept)),
        edits: None,
    };
    let result = if current.owner.is_none() {
        let settings = runtime.settings();
        let submission_id = admit_submission(
            tx,
            conversation_id,
            SubmissionDraft::Write(WriteSubmissionDraft {
                request_id: Some(format!("compaction:{task_id}")),
                entry,
            }),
            runtime.now()?,
            QueueModes {
                steering_mode: settings.steering_mode,
                follow_up_mode: settings.follow_up_mode,
            },
            &runtime.registry().builtins().generation,
        )
        .await?;
        CompactionResult {
            entry_id: None,
            submission_id: Some(submission_id),
        }
    } else {
        let appended = tx.append_entry(conversation_id, entry).await?;
        CompactionResult {
            entry_id: Some(appended.id),
            submission_id: None,
        }
    };
    Ok(NextTaskState::Terminal {
        outcome: TaskOutcome::Completed { result },
    })
}

/// Remove the status and complete without a summary.
async fn complete(runtime: &Runtime, cx: &Context) -> SessionResult<()> {
    let conversation_id = runtime.conversation_id();
    let task_id = runtime.task_id().erase();
    runtime
        .commit(
            move |tx, _current| async move {
                remove_compaction_status(&tx.doc(&LIVE_DOC, conversation_id).await?, task_id)?;
                Ok(Some(NextTaskState::Terminal {
                    outcome: TaskOutcome::Completed {
                        result: CompactionResult::default(),
                    },
                }))
            },
            cx,
        )
        .await
}

async fn fail_no_model(
    runtime: &Runtime,
    reference: Option<&ModelRef>,
    cx: &Context,
) -> SessionResult<()> {
    let message = reference.map_or_else(
        || "No model is configured".to_owned(),
        |reference| {
            format!(
                "Model {}/{} is not available",
                reference.provider, reference.model_id
            )
        },
    );
    let conversation_id = runtime.conversation_id();
    let task_id = runtime.task_id().erase();
    runtime
        .commit(
            move |tx, _current| async move {
                remove_compaction_status(&tx.doc(&LIVE_DOC, conversation_id).await?, task_id)?;
                Ok(Some(failed(message, "no_model")?))
            },
            cx,
        )
        .await
}

/// `{ reason }` failure detail.
#[derive(Serialize)]
struct FailureDetail<'a> {
    reason: &'a str,
}

fn failed(message: String, reason: &str) -> SessionResult<Next> {
    Ok(NextTaskState::Terminal {
        outcome: TaskOutcome::Failed {
            error: TaskOutcomeError {
                message,
                detail: Some(to_json(&FailureDetail { reason })?),
            },
            result: None,
        },
    })
}
