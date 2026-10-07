//! Model-requested refinement at the run boundary (kernel `refine.run`):
//! the generation's `after_tools` hook runs a refinement the finished tool
//! round requested, before the next model request, so the model resumes
//! with the refinement notice in context (the old daemon's
//! `consume_pending_refinement` after a settled turn).
//!
//! The pending request lives in the conversation's
//! [`BOUNDARY_DOC`](super::BOUNDARY_DOC); the commit that records the
//! outcome also clears it, and a failed run clears it too (taken regardless
//! of outcome, so a failure is not silently re-run). A crash during the
//! run leaves the request pending and the hook reruns it on resume.
//!
//! Port of `session_engine::refine::execute_refinement_with_rows` over the
//! durable conversation: the audit row is a `eukhe.custom-state` entry
//! (`eukhe.refinement`), the outcome and notice rows are `eukhe.custom`
//! entries. [`refine_now`] is the user `/refine` path over the same run.

use std::sync::{Arc, Weak};

use eukhe_chord::context::Context;
use eukhe_durable::harness::define::hook;
use eukhe_durable::harness::types::{GenerationHooks, HookApi, HookRegistration, ModelRef};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, GENERATION_TASK};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, EntryDraft};
use eukhe_pi_ai::models::ModelsSimpleStreamOptions;
use eukhe_types::pi_ai::{
    AssistantContentBlock, Message, Modality, StopReason, UserContent, UserMessage,
};
use futures::FutureExt;

use super::super::entries::{CustomStateData, CUSTOM_STATE_ENTRY};
use super::super::HostDeps;
use super::boundary::{boundary_state, PendingRefine, BOUNDARY_DOC};
use super::CustomNotice;
use super::RlmRuntime;
use crate::refinement::executor::{
    apply_refinement_plan, plan_refinement, RefineOptions as CoreRefineOptions, RefinementPlan,
    RefinerFn,
};
use crate::refinement::{
    append_global_refinement, get_global_harness_state_dir, get_local_harness_state_dir,
    infer_refinement_result_scope, load_global_refinement_history, load_harness_state,
    merge_harness_states, merge_refinement_history, save_harness_state, HarnessMemory,
    HarnessScope, RefinementResult,
};
use crate::session_engine::refine::{
    create_refinement_notice_message, create_refinement_outcome_message, RefinementSource,
    REFINEMENT_AUDIT_CUSTOM_TYPE,
};

/// A user-requested refinement (`/refine [--global] [instructions]`,
/// `/refine rollback <id>`).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RefineRequest {
    pub instructions: Option<String>,
    pub global: bool,
    pub rollback_id: Option<String>,
}

/// `/refine`: run a user-requested refinement of `conversation` now and
/// commit its audit, outcome, and (when an edit applied) notice rows.
///
/// # Errors
///
/// The refinement fails (no session directory for a local refinement, no
/// model, planner or store failures), or the rows fail to commit.
pub async fn refine_now(
    deps: &HostDeps,
    conversation: &Conversation,
    request: RefineRequest,
    cx: &Context,
) -> anyhow::Result<RefinementResult> {
    let result = refine(deps, conversation, request, cx).await?;
    let drafts = outcome_drafts(&result, RefinementSource::User)?;
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
        .await?;
    Ok(result)
}

/// Entries read per page when collecting the in-session refinement history.
const HISTORY_PAGE: usize = 256;

/// The `after_tools` hook that runs a pending refinement.
pub(super) fn refine_hook(runtime: &Arc<RlmRuntime>) -> HookRegistration {
    let weak: Weak<RlmRuntime> = Arc::downgrade(runtime);
    hook(
        &*GENERATION_TASK,
        GenerationHooks {
            after_tools: Some(Arc::new(move |_, _, api: &HookApi, cx: &Context| {
                let (weak, api, cx) = (weak.clone(), api.clone(), cx.clone());
                async move {
                    let Some(runtime) = weak.upgrade() else {
                        return Ok(());
                    };
                    let conversation_id = api.conversation_id();
                    let Some(pending) = boundary_state(&api, conversation_id, &cx).await?.refine
                    else {
                        return Ok(());
                    };
                    run_pending(&runtime, conversation_id, pending, &cx).await
                }
                .boxed()
            })),
            ..GenerationHooks::default()
        },
    )
}

/// Run the pending refinement and record its outcome; the request is
/// cleared either way. A failure is returned for the hook runner to report.
async fn run_pending(
    runtime: &RlmRuntime,
    conversation_id: ConversationId,
    pending: PendingRefine,
    cx: &Context,
) -> SessionResult<()> {
    let harness = runtime.deps.harness.require()?;
    let conversation = harness
        .conversation(conversation_id, cx)
        .await?
        .ok_or_else(|| {
            SessionError::error(format!("conversation {conversation_id} does not exist"))
        })?;
    let request = RefineRequest {
        instructions: pending.instructions,
        global: pending.global,
        rollback_id: None,
    };
    let refined = refine(&runtime.deps, &conversation, request, cx).await;
    if cx.aborted() {
        // The run is being aborted: the request stays for the next boundary.
        return match cx.abort_signal().and_then(|signal| signal.reason()) {
            Some(reason) => Err(SessionError::Aborted(reason)),
            None => Ok(()),
        };
    }
    let drafts = match &refined {
        Ok(result) => outcome_drafts(result, RefinementSource::SelfRefine)?,
        Err(_) => Vec::new(),
    };
    conversation
        .commit(
            move |tx| async move {
                tx.doc(&BOUNDARY_DOC, conversation_id)
                    .await?
                    .delete("refine")?;
                for draft in drafts {
                    tx.append_entry(conversation_id, draft).await?;
                }
                Ok(())
            },
            cx,
        )
        .await?;
    refined
        .map(|_| ())
        .map_err(|error| SessionError::error(format!("requested refinement failed: {error:#}")))
}

/// The audit row, the outcome row, and (when an edit applied) the
/// model-facing notice row of `source`, in the old write order.
fn outcome_drafts(
    result: &RefinementResult,
    source: RefinementSource,
) -> SessionResult<Vec<EntryDraft>> {
    let audit = CUSTOM_STATE_ENTRY.draft(&eukhe_durable::types::TypedEntryDraft {
        model: None,
        data: CustomStateData {
            custom_type: REFINEMENT_AUDIT_CUSTOM_TYPE.to_string(),
            data: Some(serde_json::to_value(result).map_err(SessionError::other)?),
        },
        head: None,
        edits: None,
    })?;
    let mut drafts = vec![
        audit,
        notice(create_refinement_outcome_message(result)).draft()?,
    ];
    if result.applied_edits.iter().any(|edit| edit.applied) {
        let message = create_refinement_notice_message(result, source);
        drafts.push(notice(message).draft()?);
    }
    Ok(drafts)
}

fn notice(message: eukhe_types::session::CustomMessage) -> CustomNotice {
    let text = match message.content {
        eukhe_types::ai::UserContent::Text(text) => text,
        eukhe_types::ai::UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(|block| match block {
                eukhe_types::ai::UserContentBlock::Text(text) => Some(text.text.as_str()),
                eukhe_types::ai::UserContentBlock::Image(_)
                | eukhe_types::ai::UserContentBlock::Raw(_) => None,
            })
            .collect::<Vec<_>>()
            .join("\n"),
    };
    CustomNotice {
        custom_type: message.custom_type,
        text,
        display: message.display,
        details: message.details,
        timestamp: message.timestamp,
    }
}

/// Plan, re-read, apply, and persist one refinement of the session's
/// harness state (`execute_refinement_with_rows` without the session rows).
async fn refine(
    deps: &HostDeps,
    conversation: &Conversation,
    request: RefineRequest,
    cx: &Context,
) -> anyhow::Result<RefinementResult> {
    let local_harness_dir = get_local_harness_state_dir(deps.storage_dir.as_deref());
    let global_harness_dir = get_global_harness_state_dir(&deps.agent_dir);
    let memory = if deps.memory.is_some() {
        HarnessMemory::Chat
    } else {
        HarnessMemory::Harness
    };
    let requested_scope = if request.global {
        HarnessScope::Global
    } else {
        HarnessScope::Local
    };
    // A local refinement needs the session's own directory: its harness
    // state and artifact paths live there. A rollback resolves its scope
    // from the target refinement.
    if request.rollback_id.is_none()
        && requested_scope == HarnessScope::Local
        && local_harness_dir.is_none()
    {
        anyhow::bail!(LOCAL_REFINEMENT_NEEDS_DIR);
    }
    let options = CoreRefineOptions {
        global: request.global,
        instructions: request.instructions,
        rollback_id: request.rollback_id,
        memory,
    };
    let scope_dir = |scope: HarnessScope| match scope {
        HarnessScope::Global => Ok(global_harness_dir.clone()),
        HarnessScope::Local => local_harness_dir
            .clone()
            .ok_or_else(|| anyhow::anyhow!(LOCAL_REFINEMENT_NEEDS_DIR)),
    };
    let global_state = load_harness_state(&global_harness_dir, HarnessScope::Global);
    let planning_state = match (requested_scope, &local_harness_dir) {
        (HarnessScope::Local, Some(local_harness_dir)) => {
            let local_state = load_harness_state(local_harness_dir, HarnessScope::Local);
            merge_harness_states(&global_state, Some(&local_state))
        }
        (HarnessScope::Global, _) | (HarnessScope::Local, None) => global_state.clone(),
    };
    let history = merge_refinement_history(
        &load_global_refinement_history(&global_harness_dir),
        &session_refinement_history(conversation, cx).await?,
    );
    // Baseline captured before the (slow) model pass, so concurrent kernel
    // writes are rejected instead of clobbered. A rollback's baseline is
    // its target's scope.
    let baseline_scope = options
        .rollback_id
        .as_ref()
        .and_then(|id| history.iter().find(|item| &item.id == id))
        .and_then(infer_refinement_result_scope)
        .unwrap_or(requested_scope);
    let baseline_state = load_harness_state(&scope_dir(baseline_scope)?, baseline_scope);

    let agent = conversation.agent(cx).await?;
    let model_ref = agent
        .model
        .ok_or_else(|| anyhow::anyhow!("the conversation has no model to refine with"))?;
    let model = deps
        .models
        .get_model(&model_ref.provider, &model_ref.model_id)
        .ok_or_else(|| {
            anyhow::anyhow!(
                "model {}/{} is not available",
                model_ref.provider,
                model_ref.model_id
            )
        })?;
    let messages = transcript(&conversation.context(cx).await?.messages)?;
    let plan = plan_refinement(
        &messages,
        &planning_state,
        &history,
        &legacy_model(&model),
        &options,
        refiner(deps, model, model_ref),
    )
    .await?;
    let plan = strip_display_prefixes(plan);

    let target_scope = plan.rollback_scope.unwrap_or(requested_scope);
    let target_dir = scope_dir(target_scope)?;
    let mut state = load_harness_state(&target_dir, target_scope);
    // The factory opt-in resolves immediately before the apply, after the
    // planning request: a setting changed during the request decides.
    let agent_dir = deps.agent_dir.clone();
    let factory_enabled =
        tokio::task::spawn_blocking(move || crate::refinement::factory_enabled(&agent_dir)).await?;
    let mut result = apply_refinement_plan(
        &mut state,
        plan,
        &options,
        Some(baseline_state),
        factory_enabled,
    );
    result.harness_state_path = save_harness_state(&target_dir, &state)?
        .to_string_lossy()
        .to_string();
    if target_scope == HarnessScope::Global {
        append_global_refinement(&global_harness_dir, &result)?;
    }
    Ok(result)
}

/// The local-refinement failure without a session directory.
const LOCAL_REFINEMENT_NEEDS_DIR: &str =
    "Local harness refinement requires a session directory; use global refinement instead.";

/// The refinements recorded in this conversation (its audit rows), oldest
/// first.
async fn session_refinement_history(
    conversation: &Conversation,
    cx: &Context,
) -> anyhow::Result<Vec<RefinementResult>> {
    let mut history = Vec::new();
    let mut cursor = None;
    loop {
        let page = conversation
            .entries(ConversationEntryQuery::default(), HISTORY_PAGE, cursor, cx)
            .await?;
        for entry in page.items {
            let Some(audit) = CUSTOM_STATE_ENTRY.narrow(entry)? else {
                continue;
            };
            let data = audit.data();
            if data.custom_type != REFINEMENT_AUDIT_CUSTOM_TYPE {
                continue;
            }
            if let Some(value) = &data.data {
                history.push(serde_json::from_value::<RefinementResult>(value.clone())?);
            }
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => break,
        }
    }
    // Pages are newest first.
    history.reverse();
    Ok(history)
}

/// The conversation's model context in the session message shape the
/// refinement planner serializes (system markers carry no content).
fn transcript(messages: &[Message]) -> anyhow::Result<Vec<eukhe_types::session::AgentMessage>> {
    messages
        .iter()
        .filter(|message| !matches!(message, Message::System(_)))
        .map(|message| {
            let value = serde_json::to_value(message)?;
            Ok(serde_json::from_value(value)?)
        })
        .collect()
}

/// The planner's model description: it reads the context window and output
/// budget; the request itself goes through the session's [`Models`].
fn legacy_model(model: &eukhe_types::pi_ai::Model) -> eukhe_types::ai::Model {
    let cost = eukhe_types::ai::ModelCost {
        input: model.cost.input.into(),
        output: model.cost.output.into(),
        cache_read: model.cost.cache_read.into(),
        cache_write: model.cost.cache_write.into(),
    };
    eukhe_types::ai::Model {
        id: model.id.clone(),
        name: model.name.clone(),
        api: model.api.clone(),
        provider: model.provider.clone(),
        base_url: model.base_url.clone(),
        reasoning: model.reasoning,
        thinking_level_map: None,
        input: model
            .input
            .iter()
            .map(|modality| match modality {
                Modality::Text => eukhe_types::ai::ModelInput::Text,
                Modality::Image => eukhe_types::ai::ModelInput::Image,
            })
            .collect(),
        cost,
        context_window: model.context_window,
        max_tokens: model.max_tokens,
        featured: None,
        headers: None,
        compat: None,
    }
}

/// The planner's model call over the session's models: the request model
/// with the planner's output budget, one user prompt, and the reply's text.
fn refiner(deps: &HostDeps, model: eukhe_types::pi_ai::Model, model_ref: ModelRef) -> RefinerFn {
    let models = deps.models.clone();
    Box::new(move |request, system_prompt, prompt| {
        Box::pin(async move {
            let mut model = model;
            model.max_tokens = request.max_tokens;
            let context = eukhe_types::pi_ai::Context {
                system_prompt: Some(system_prompt.to_string()),
                messages: vec![Message::User(UserMessage {
                    content: UserContent::Text(prompt),
                    timestamp: 0,
                })],
                tools: None,
            };
            let reply = models
                .complete_simple(&model, context, ModelsSimpleStreamOptions::default())
                .await;
            match reply.stop_reason {
                StopReason::Error | StopReason::Aborted => anyhow::bail!(
                    "{}",
                    reply
                        .error_message
                        .unwrap_or_else(|| "refinement request failed".to_string())
                ),
                StopReason::Pending | StopReason::Deferred => {
                    anyhow::bail!("refinement request did not complete")
                }
                StopReason::Stop | StopReason::Length | StopReason::ToolUse => {}
            }
            let text: Vec<eukhe_types::ai::AssistantContentBlock> = reply
                .content
                .iter()
                .filter_map(|block| match block {
                    AssistantContentBlock::Text(text) => {
                        Some(eukhe_types::ai::AssistantContentBlock::Text(
                            eukhe_types::ai::TextContent {
                                text: text.text.clone(),
                                text_signature: None,
                                rest: serde_json::Map::default(),
                                cache_breakpoint: None,
                            },
                        ))
                    }
                    AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
                })
                .collect();
            Ok(eukhe_types::ai::AssistantMessage {
                content: text,
                api: model.api.clone(),
                provider: model_ref.provider,
                model: model_ref.model_id,
                response_model: None,
                response_id: None,
                diagnostics: None,
                usage: eukhe_types::ai::Usage::default(),
                stop_reason: eukhe_types::ai::StopReason::Stop,
                stop_reason_raw: None,
                error_message: None,
                timestamp: reply.timestamp,
                rest: serde_json::Map::default(),
            })
        })
    })
}

/// Strip display-only `local:`/`global:` prefixes from proposal edit ids.
fn strip_display_prefixes(mut plan: RefinementPlan) -> RefinementPlan {
    for edit in &mut plan.proposal.edits {
        if let Some(id) = &edit.id {
            if let Some(stripped) = id
                .strip_prefix("local:")
                .or_else(|| id.strip_prefix("global:"))
            {
                edit.id = Some(stripped.to_string());
            }
        }
    }
    plan
}
