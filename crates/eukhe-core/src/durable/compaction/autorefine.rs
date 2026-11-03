//! The compact-trigger auto-refine on the durable session (the old
//! engine's `auto_refine_trigger`): a successful compaction arms a
//! review; the next quiescent boundary runs the shared sequence — the
//! gates (the refine surface, `autoRefine.enabled`, `autoRefine.compact`),
//! the review cooldown, then the review, and only an approving review
//! runs the refinement through [`crate::durable::rlm::refine::refine`].
//! Every review attempt — decline, success, or failure — stamps the
//! cooldown, so a persistent failure cannot retry a full review on every
//! boundary. The cooldown and pending flag are session-memory, like TS
//! `_lastAutoRefineReviewAt` / `_compactAutoRefinePending`.

use std::sync::{Mutex, PoisonError, Weak};

use eukhe_ai::models::ModelsSimpleStreamOptions;
use eukhe_chord::context::Context;
use eukhe_durable::harness::{Continuation, Conversation};
use eukhe_types::pi_ai::{
    AssistantContentBlock, CacheBreakpoint, Message, TextContent, UserContent, UserContentBlock,
    UserMessage,
};
use futures::FutureExt;

use crate::autonomous::now_millis;
use crate::durable::rlm::refine::{
    auto_refine_instructions, completed, AutoRefineGates, RefinementSource,
    AUTO_REFINE_COMPACT_REASON,
};
use crate::durable::HostDeps;
use crate::refinement::executor::{review_auto_refine, AutoRefineReviewContext, ReviewFn};
use crate::refinement::{
    load_global_refinement_history, load_harness_state, merge_harness_states,
    merge_refinement_history, HarnessScope,
};

use super::CompactionRuntime;

/// The compact-trigger state one session carries.
#[derive(Default)]
pub(crate) struct AutoRefineState {
    inner: Mutex<Inner>,
}

#[derive(Default)]
struct Inner {
    /// A successful compaction armed the trigger.
    pending: bool,
    /// The last review attempt's timestamp (millis): every attempt stamps
    /// the cooldown window.
    last_review_at: Option<u64>,
    /// Settled non-error assistant turns since the last review (the
    /// review prompt's trigger line).
    settled_turns_since_review: u32,
    /// A round is in flight: a second consumption re-arms instead of
    /// overlapping.
    in_flight: bool,
}

impl AutoRefineState {
    /// One settled non-error assistant turn appended (the old
    /// `_assistantTurnsSinceAutoRefine` increment).
    pub(crate) fn note_settled_turn(&self) {
        let mut inner = self.inner.lock().unwrap_or_else(PoisonError::into_inner);
        inner.settled_turns_since_review = inner.settled_turns_since_review.saturating_add(1);
    }

    /// A successful compaction armed the trigger.
    pub(crate) fn arm(&self) {
        let mut inner = self.inner.lock().unwrap_or_else(PoisonError::into_inner);
        inner.pending = true;
    }
}

fn lock(state: &AutoRefineState) -> std::sync::MutexGuard<'_, Inner> {
    state.inner.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Whether the session may run auto-refinement (the old
/// `_autoRefineAllowedForSession`): a top-level session with a local
/// harness state directory.
fn allowed(deps: &HostDeps) -> bool {
    deps.role.is_root()
        && crate::refinement::get_local_harness_state_dir(deps.storage_dir.as_deref()).is_some()
}

fn gates(deps: &HostDeps) -> AutoRefineGates {
    AutoRefineGates::from_settings(Some(&deps.settings.manager().get_auto_refine()))
}

/// What consuming the trigger at one boundary came to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Consumed {
    /// Nothing more for this boundary: no trigger, a gate, the cooldown,
    /// or a finished round.
    Settled,
    /// A run started before the review's request went out: the trigger
    /// waits for the conversation's next idle, where the review continues
    /// that run's cached request instead of racing it.
    Busy,
}

/// Consume an armed trigger at one quiescent boundary: the gates, the
/// cooldown, the review, and the approving review's refinement run.
pub(crate) async fn consume(
    runtime: &std::sync::Arc<CompactionRuntime>,
    conversation: &Conversation,
    cx: &Context,
) -> anyhow::Result<Consumed> {
    let deps = &runtime.deps;
    let gates = gates(deps);
    let settled_turns = {
        let mut inner = lock(&runtime.autorefine);
        if !inner.pending {
            return Ok(Consumed::Settled);
        }
        if !allowed(deps) || !gates.enabled || !gates.compact {
            inner.pending = false;
            return Ok(Consumed::Settled);
        }
        if inner
            .last_review_at
            .is_some_and(|last| now_millis().saturating_sub(last) < gates.cooldown_ms)
        {
            // The cooldown holds the trigger for a later boundary.
            return Ok(Consumed::Settled);
        }
        if inner.in_flight {
            return Ok(Consumed::Settled);
        }
        inner.in_flight = true;
        inner.settled_turns_since_review
    };
    // A round starts under the session's closing gate: a close that begins
    // meanwhile waits for its requests instead of abandoning them, and a
    // closing session starts none.
    let Some(outcome) = deps
        .closing
        .admit(|| run_round(deps, conversation, settled_turns, cx))
        .await
    else {
        lock(&runtime.autorefine).in_flight = false;
        return Ok(Consumed::Settled);
    };
    let mut inner = lock(&runtime.autorefine);
    inner.in_flight = false;
    if let Ok(Verdict::Busy) = outcome {
        // No attempt went out: the trigger stays armed, the cooldown
        // unstamped.
        return Ok(Consumed::Busy);
    }
    // Every fresh attempt stamps the cooldown and resets the counter
    // (decline, success, and failure alike).
    inner.last_review_at = Some(now_millis());
    inner.settled_turns_since_review = 0;
    if outcome.is_ok() {
        inner.pending = false;
    }
    drop(inner);
    outcome.map(|_| Consumed::Settled)
}

/// What a review came to.
enum Verdict {
    /// The conversation was busy when the request was to go out; none went.
    Busy,
    Declined,
    Approved(crate::refinement::executor::AutoRefineReview),
}

/// One review round: the review, then the approving review's refinement
/// run with its rows committed.
async fn run_round(
    deps: &HostDeps,
    conversation: &Conversation,
    settled_turns: u32,
    cx: &Context,
) -> anyhow::Result<Verdict> {
    let review = match review(deps, conversation, settled_turns, cx).await? {
        Verdict::Approved(review) => review,
        verdict @ (Verdict::Busy | Verdict::Declined) => return Ok(verdict),
    };
    let request = super::super::rlm::refine::RefineRequest {
        instructions: Some(auto_refine_instructions(
            AUTO_REFINE_COMPACT_REASON,
            &review,
        )),
        global: false,
        rollback_id: None,
    };
    let result = super::super::rlm::refine::refine(deps, conversation, request, cx).await?;
    let drafts = super::super::rlm::refine::outcome_drafts(&result, RefinementSource::Auto)
        .map_err(|error| anyhow::anyhow!("{error}"))?;
    let conversation_id = conversation.id();
    conversation
        .commit(
            move |tx| async move {
                for draft in drafts {
                    tx.append_entry(conversation_id, draft).await?;
                }
                Ok(())
            },
            cx,
        )
        .await
        .map_err(|error| anyhow::anyhow!("{error}"))?;
    Ok(Verdict::Approved(review))
}

/// Whether a run of `conversation` is live: the idle the review's task
/// waits for has not come (the same test, so a busy review always waits).
fn busy(conversation: &Conversation, cx: &Context) -> bool {
    conversation.wait_for_idle(cx).now_or_never().is_none()
}

/// The compact-trigger review: an LLM call over the conversation, the
/// merged harness state, and the refinement history. It continues the
/// conversation's next turn: the request is the one that turn starts with
/// (the session's system prompt, tools, model, and messages, shaped as the
/// turn's), with the review prompt as its last message. The provider reads
/// the prefix the session's requests cached, and the prefix the review
/// writes is the one the next turn reads; after a compaction the prefix is
/// written once, not once for the review and again for the turn. While a
/// run is live the review sends nothing ([`Verdict::Busy`]): its request
/// would race the run's and write the same prefix again.
async fn review(
    deps: &HostDeps,
    conversation: &Conversation,
    settled_turns: u32,
    cx: &Context,
) -> anyhow::Result<Verdict> {
    let local_dir = crate::refinement::get_local_harness_state_dir(deps.storage_dir.as_deref());
    let global_dir = crate::refinement::get_global_harness_state_dir(&deps.agent_dir);
    let local_state = local_dir.map_or_else(crate::refinement::empty_harness_state, |dir| {
        load_harness_state(&dir, HarnessScope::Local)
    });
    let global_state = load_harness_state(&global_dir, HarnessScope::Global);
    let merged = merge_harness_states(&global_state, Some(&local_state));
    let global_history = load_global_refinement_history(&global_dir);
    let session_history =
        super::super::rlm::refine::session_refinement_history(conversation, cx).await?;
    let history = merge_refinement_history(&global_history, &session_history);
    let Some(Continuation {
        model,
        messages,
        options,
    }) = conversation.continuation(cx).await?
    else {
        return Ok(Verdict::Declined);
    };
    let mut messages = match deps.optchat.get().and_then(Weak::upgrade) {
        Some(chat) => chat.side_request(conversation.id(), messages, cx).await?,
        None => messages,
    };
    mark_prefix_end(&mut messages);
    if busy(conversation, cx) {
        return Ok(Verdict::Busy);
    }
    let models = deps.models.clone();
    let call: ReviewFn = Box::new(move |prompt| {
        Box::pin(async move {
            messages.push(Message::User(UserMessage {
                content: UserContent::Text(prompt),
                timestamp: now_millis(),
            }));
            let context = eukhe_types::pi_ai::Context {
                system_prompt: None,
                messages,
                tools: None,
            };
            // No output cap and no tool choice of its own: either would
            // change the request's thinking budget or tool choice, which
            // invalidates the cached messages.
            let reply = completed(
                models
                    .complete_simple(&model, context, ModelsSimpleStreamOptions::from(options))
                    .await,
            )?;
            Ok(reply
                .content
                .iter()
                .filter_map(|block| match block {
                    AssistantContentBlock::Text(text) => Some(text.text.as_str()),
                    AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
                })
                .collect::<Vec<_>>()
                .join("\n"))
        })
    });
    let review = review_auto_refine(
        &merged,
        &history,
        &AutoRefineReviewContext {
            reason: AUTO_REFINE_COMPACT_REASON.to_owned(),
            turns_since_last_review: settled_turns,
        },
        call,
    )
    .await?;
    Ok(if review.should_refine {
        Verdict::Approved(review)
    } else {
        Verdict::Declined
    })
}

/// Mark the end of the continued conversation (the last text block of its
/// last message) as a cache breakpoint: the review writes the prefix it
/// shares with the next turn there, a few blocks before that turn's own
/// end, where the turn's request finds it.
fn mark_prefix_end(messages: &mut [Message]) {
    let block = match messages.last_mut() {
        Some(Message::Assistant(assistant)) => {
            assistant
                .content
                .iter_mut()
                .rev()
                .find_map(|block| match block {
                    AssistantContentBlock::Text(text) => Some(text),
                    AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
                })
        }
        Some(Message::User(user)) => {
            if let UserContent::Text(text) = &mut user.content {
                user.content = UserContent::Blocks(vec![UserContentBlock::Text(TextContent::new(
                    std::mem::take(text),
                ))]);
            }
            match &mut user.content {
                UserContent::Blocks(blocks) => {
                    blocks.iter_mut().rev().find_map(|block| match block {
                        UserContentBlock::Text(text) => Some(text),
                        UserContentBlock::Image(_) => None,
                    })
                }
                UserContent::Text(_) => None,
            }
        }
        Some(Message::ToolResult(_) | Message::System(_)) | None => None,
    };
    if let Some(block) = block {
        block.cache_breakpoint = Some(CacheBreakpoint::Ephemeral);
    }
}
