//! The compact-trigger auto-refine on the durable session (the old
//! engine's `auto_refine_trigger`): a successful compaction arms a
//! review; the next quiescent boundary runs the shared sequence — the
//! gates (the refine surface, `autoRefine.enabled`, `autoRefine.compact`),
//! the review cooldown, then the review, and only an approving review
//! runs the refinement through [`crate::durable::rlm::refine::refine`].
//! Every review attempt — decline, success, or failure — stamps the
//! cooldown, so a persistent failure cannot retry a full review on every
//! boundary. The cooldown and pending flag are session-memory, exactly
//! like the old engine's `_lastAutoRefineReviewAt` /
//! `_compactAutoRefinePending`.

use std::sync::{Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_durable::harness::Conversation;
use eukhe_types::session::AgentMessage;

use crate::durable::HostDeps;
use crate::refinement::executor::{review_auto_refine, AutoRefineReviewContext};
use crate::refinement::{
    load_global_refinement_history, load_harness_state, merge_harness_states,
    merge_refinement_history, HarnessScope,
};
use crate::session_engine::refine::{
    auto_refine_instructions, now_millis, AutoRefineGates, AUTO_REFINE_COMPACT_REASON,
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
    let auto_refine = deps.settings.manager().settings().auto_refine.clone();
    AutoRefineGates::from_settings(auto_refine.as_ref())
}

/// Consume an armed trigger at one quiescent boundary: the gates, the
/// cooldown, the review, and the approving review's refinement run.
#[allow(clippy::too_many_lines)]
pub(crate) async fn consume(
    runtime: &std::sync::Arc<CompactionRuntime>,
    conversation: &Conversation,
    cx: &Context,
) -> anyhow::Result<()> {
    let deps = &runtime.deps;
    let gates = gates(deps);
    let settled_turns = {
        let mut inner = lock(&runtime.autorefine);
        if !inner.pending {
            return Ok(());
        }
        if !allowed(deps) || !gates.enabled || !gates.compact {
            inner.pending = false;
            return Ok(());
        }
        if inner
            .last_review_at
            .is_some_and(|last| now_millis().saturating_sub(last) < gates.cooldown_ms)
        {
            // The cooldown holds the trigger for a later boundary.
            return Ok(());
        }
        if inner.in_flight {
            return Ok(());
        }
        inner.in_flight = true;
        inner.settled_turns_since_review
    };
    let outcome = run_round(deps, conversation, settled_turns, cx).await;
    {
        let mut inner = lock(&runtime.autorefine);
        inner.in_flight = false;
        // Every fresh attempt stamps the cooldown and resets the counter
        // (decline, success, and failure alike).
        inner.last_review_at = Some(now_millis());
        inner.settled_turns_since_review = 0;
        if outcome.is_ok() {
            inner.pending = false;
        }
    }
    outcome.map(drop)
}

/// One review round: the review, then the approving review's refinement
/// run with its rows committed.
async fn run_round(
    deps: &HostDeps,
    conversation: &Conversation,
    settled_turns: u32,
    cx: &Context,
) -> anyhow::Result<()> {
    let review = review(deps, conversation, settled_turns, cx).await?;
    let Some(review) = review else {
        return Ok(());
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
    let drafts = super::super::rlm::refine::outcome_drafts(
        &result,
        crate::session_engine::refine::RefinementSource::Auto,
    )
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
    Ok(())
}

/// The compact-trigger review (the old `review_compact_auto_refine`): an
/// LLM call over the conversation, the merged harness state, and the
/// refinement history; `Ok(None)` is the decline.
async fn review(
    deps: &HostDeps,
    conversation: &Conversation,
    settled_turns: u32,
    cx: &Context,
) -> anyhow::Result<Option<crate::refinement::executor::AutoRefineReview>> {
    let view = conversation.context(cx).await?;
    let messages: Vec<AgentMessage> = super::super::rlm::refine::transcript(&view.messages)?;
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
    // The review runs on the conversation's model, over the session's
    // [`Models`] (the same seam the refinement planner uses).
    let agent = conversation.agent(cx).await?;
    let Some(reference) = agent.model.clone() else {
        return Ok(None);
    };
    let Some(model) = deps
        .models
        .get_model(&reference.provider, &reference.model_id)
    else {
        return Ok(None);
    };
    let legacy = super::super::rlm::refine::legacy_model(&model);
    let refiner = super::super::rlm::refine::refiner(deps, model, reference);
    let review = review_auto_refine(
        &messages,
        &merged,
        &history,
        &legacy,
        &AutoRefineReviewContext {
            reason: AUTO_REFINE_COMPACT_REASON.to_owned(),
            turns_since_last_review: settled_turns,
        },
        refiner,
    )
    .await?;
    Ok(review.should_refine.then_some(review))
}
