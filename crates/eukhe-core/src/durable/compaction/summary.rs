//! `before_compact`: eukhe's own summary of a durable compaction (the old
//! engine's `compact_session::execute_compaction` over the Harness's
//! `CompactionRequest`): the old summarizer prompts and serializer
//! (`compaction_utils`), the auxiliary-model routing (`auxiliaryModel`,
//! TS #2411), the previous summary's update mode, the recent-state anchor
//! (TS #2385), the harness-digest block that leads the summary, and the
//! `[compaction-summary]` wrapper — the same texts the old engine wrote.
//! The summary text deltas stream to the session's
//! [`SummaryDeltaSink`](super::HostDeps) while the summarizer answers.
//!
//! Chat-memory roots decline: their next turn starts fresh from the
//! settled view, so the context a summary would replace is dropped anyway
//! (the old engine's `next_turn_is_fresh` threshold skip).

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_durable::harness::types::{
    BeforeCompactHook, CompactionDecision, CompactionRequest, CompactionSnapshot, HookApi,
};
use eukhe_durable::harness::Conversation;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::EntryRecord;
use eukhe_pi_ai::models::ModelsSimpleStreamOptions;
use eukhe_pi_ai::types::SimpleStreamOptions;
use eukhe_types::pi_ai::{
    AssistantMessageEvent, CacheRetention, Context as PiContext, Message, StopReason,
};
use futures::{FutureExt, StreamExt};
use serde_json::json;

use crate::durable::observe::compaction_trace::trace;

use super::head;
use crate::session_engine::auxiliary_model::{resolve_auxiliary_model, AuxiliaryModelContext};
use crate::session_engine::compact_session::history_summary_completion_budget;
use crate::session_engine::compaction::DEFAULT_RESERVE_TOKENS;
use crate::session_engine::compaction_exec::build_summarization_request;
use crate::session_engine::compaction_utils::{
    compute_file_lists, extract_file_ops_from_message, format_file_operations, FileOperations,
    SUMMARIZATION_SYSTEM_PROMPT,
};
use crate::session_engine::messages::create_compaction_outcome_message;

use super::{CompactionRuntime, COMPACTION_ENTRY_KIND};

/// The `before_compact` hook of `eukhe.compaction`.
pub(super) fn before_compact_hook(runtime: &Arc<CompactionRuntime>) -> BeforeCompactHook {
    let runtime = Arc::clone(runtime);
    Arc::new(
        move |request: &CompactionRequest, api: &HookApi, cx: &Context| {
            let (runtime, request, api, cx) =
                (runtime.clone(), request.clone(), api.clone(), cx.clone());
            async move { decide(&runtime, &request, &api, &cx).await }.boxed()
        },
    )
}

/// One hook invocation: decline, or summarize and answer the summary.
async fn decide(
    runtime: &Arc<CompactionRuntime>,
    request: &CompactionRequest,
    api: &HookApi,
    cx: &Context,
) -> SessionResult<Option<CompactionDecision>> {
    let deps = &runtime.deps;
    trace(
        "compact.enter",
        &json!({ "customInstructions": request.instructions.is_some() }),
    );
    // A chat-memory root's next turn starts fresh from the settled view;
    // the history lives in the chat, so the compaction is declined (the
    // old engine's `next_turn_is_fresh` arm).
    if chat_memory_root(deps, api.conversation_id(), cx).await? {
        return Ok(Some(CompactionDecision::Decline));
    }
    let harness = deps.harness.require()?;
    let Some(conversation) = harness.conversation(api.conversation_id(), cx).await? else {
        return Ok(Some(CompactionDecision::Decline));
    };
    // The compaction head (a previous summary) leads the summarized
    // entries; everything after it is this compaction's history.
    let head_wrapped = request
        .entries
        .first()
        .filter(|entry| entry.kind == COMPACTION_ENTRY_KIND)
        .and_then(|entry| head::user_text(entry.model.as_deref().unwrap_or(&[])));
    let previous = head_previous(head_wrapped);
    let history_records: Vec<&EntryRecord> = if head_wrapped.is_some() {
        request.entries.iter().skip(1).collect()
    } else {
        request.entries.iter().collect()
    };
    let history_models = head::flattened_models(&history_records);
    let history = head::agent_messages(&history_models)
        .map_err(|error| SessionError::error(format!("{error:#}")))?;
    if history.is_empty() && previous.is_none() {
        // Nothing new and nothing to update (the old engine's
        // `CompactSkip::TooShort`): the compaction ends without a summary.
        return Ok(Some(CompactionDecision::Decline));
    }
    // The recent-state anchor: the newest assistant text of the kept tail.
    let anchor = kept_tail_anchor(&conversation, request, cx).await?;
    // File operations: the previous summary's carried lists plus the
    // history's operations, merged and re-formatted (TS #2385).
    let mut file_ops = FileOperations::default();
    if let Some(previous) = previous.as_deref() {
        let (read, modified) = head::file_lists(previous);
        file_ops.read.extend(read);
        file_ops.edited.extend(modified);
    }
    for message in &history {
        extract_file_ops_from_message(message, &mut file_ops);
    }
    let (read_files, modified_files) = compute_file_lists(&file_ops);
    let file_block = format_file_operations(&read_files, &modified_files);

    // The model: the conversation's agent model, routed through
    // `auxiliaryModel` when that is set and usable (TS #2411).
    let agent = conversation.agent(cx).await?;
    let model_ref = agent.model.clone();
    let session_model = model_ref.as_ref().and_then(|reference| {
        deps.models
            .get_model(&reference.provider, &reference.model_id)
    });
    let (Some(_), Some(model)) = (model_ref, session_model) else {
        // No model resolves: the built-in summarizer path fails the same
        // way (fail_no_model), so decline and let it answer.
        return Ok(None);
    };
    let reserve = compaction_reserve_tokens(deps);
    let (mut model, options_extra) = route_auxiliary(
        deps,
        &model,
        &history,
        previous.as_deref(),
        anchor.as_deref(),
        request.instructions.as_deref(),
        reserve,
    );
    // The completion budget (TS `generateSummary`: floor(0.8 * reserve)),
    // clamped by the model's own limit like the harness's pin.
    let mut max_tokens = history_summary_completion_budget(reserve);
    if model.max_tokens > 0 {
        max_tokens = max_tokens.min(model.max_tokens);
    }
    model.max_tokens = max_tokens;

    // The request (the old engine's `build_summarization_request`).
    let request_messages = build_summarization_request(
        &history,
        request.instructions.as_deref(),
        previous.as_deref(),
        anchor.as_deref(),
        reserve,
    );
    let mut messages: Vec<Message> = Vec::with_capacity(request_messages.len());
    for message in &request_messages {
        let value = serde_json::to_value(message)
            .map_err(|error| SessionError::error(error.to_string()))?;
        messages.push(
            serde_json::from_value(value)
                .map_err(|error| SessionError::error(error.to_string()))?,
        );
    }
    let context = PiContext {
        system_prompt: Some(SUMMARIZATION_SYSTEM_PROMPT.to_owned()),
        messages,
        tools: None,
    };
    let mut options: ModelsSimpleStreamOptions = SimpleStreamOptions {
        stream: eukhe_pi_ai::types::StreamOptions {
            max_tokens: Some(max_tokens),
            cache_retention: Some(CacheRetention::None),
            ..eukhe_pi_ai::types::StreamOptions::default()
        },
        ..SimpleStreamOptions::default()
    }
    .into();
    if let Some(api_key) = options_extra.api_key {
        options.options.stream.request.api_key = Some(api_key);
    }
    if let Some(headers) = options_extra.headers {
        options.options.stream.request.headers = Some(headers);
    }
    trace(
        "compact.summarizer_request",
        &json!({ "maxTokens": max_tokens }),
    );
    // Stream the summarizer, forwarding every text delta to the live
    // summary sink (the old engine's `complete_summary_call` on_delta).
    let sink = deps.summary_delta.clone();
    let forward_sink = sink.clone();
    let stream = deps.models.stream_simple(&model, context, options);
    let events = stream.events();
    let drain = tokio::spawn(async move {
        let mut events = events;
        while let Some(event) = events.next().await {
            if let AssistantMessageEvent::TextDelta { delta, .. } = &event {
                if let Some(sink) = forward_sink.as_ref() {
                    sink(delta);
                }
            }
        }
    });
    let reply = stream.result().await;
    let _ = drain.await;
    // The old engine's failure label ("Summarization failed"): an error
    // stop bubbles out of the hook and fails the compaction task.
    if reply.stop_reason == StopReason::Error {
        let message = reply.error_message.unwrap_or_default();
        return Err(SessionError::error(format!(
            "Summarization failed: {message}"
        )));
    }
    let summary_text: String = reply
        .content
        .iter()
        .filter_map(|block| match block {
            eukhe_types::pi_ai::AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("\n");
    let mut body = summary_text;
    body.push_str(&file_block);
    // The parts the live stream never carried (the file-operations block
    // never flows through the summarizer) flush through the sink so a
    // client accumulating deltas holds the committed text.
    if !file_block.is_empty() {
        if let Some(sink) = sink_for(deps) {
            sink(&file_block);
        }
    }
    // The harness digest: a fresh render leads the summary (the old
    // engine's `harness_digest` block, TS #2394) and rides the entry data
    // with its state fingerprint, so a later staleness check compares
    // state instead of query-dependent renderings.
    let digest = super::digest_render_of(deps, &conversation, cx).await?;
    let text = match &digest {
        Some(render) => format!(
            "{}{}",
            head::digest_block(&render.digest),
            head::wrapped_summary(&body)
        ),
        None => head::wrapped_summary(&body),
    };
    Ok(Some(match digest {
        Some(render) => CompactionDecision::SummaryWithData(
            text,
            CompactionSnapshot {
                harness_digest: render.digest,
                harness_state_fingerprint: render.state_fingerprint,
            },
        ),
        None => CompactionDecision::Summary(text),
    }))
}

/// The previous summary of a compaction head's wrapped text, when the head
/// carries one that leaves anything to update from.
fn head_previous(wrapped: Option<&str>) -> Option<String> {
    wrapped.and_then(head::previous_summary)
}

/// Whether the compaction's conversation is a chat-memory root (a session
/// with chat memory, root role, whose conversation no task owns).
async fn chat_memory_root(
    deps: &super::HostDeps,
    conversation: eukhe_durable::types::ConversationId,
    cx: &Context,
) -> SessionResult<bool> {
    if deps.memory.is_none() || deps.role.memory_role() != crate::memory::MemoryRole::Root {
        return Ok(false);
    }
    let harness = deps.harness.require()?;
    let root =
        crate::durable::optchat::request::is_root_conversation(&harness, conversation, cx).await;
    root.map_err(SessionError::other)
}

/// Whether `conversation` is a chat-memory root (the observer's skip
/// message reads the same decline the hook applies).
pub(super) async fn chat_memory_root_of(
    deps: &super::HostDeps,
    conversation: eukhe_durable::types::ConversationId,
    cx: &Context,
) -> SessionResult<bool> {
    chat_memory_root(deps, conversation, cx).await
}

/// The recent-state anchor over the kept tail: the newest assistant text
/// of the entries from `first_kept` on (the committed context, so a busy
/// conversation reads its placed state).
async fn kept_tail_anchor(
    conversation: &Conversation,
    request: &CompactionRequest,
    cx: &Context,
) -> SessionResult<Option<String>> {
    let view = harness_read_context(conversation, cx).await?;
    let kept: Vec<&EntryRecord> = view
        .entries
        .iter()
        .skip_while(|entry| entry.id != request.first_kept)
        .collect();
    Ok(head::recent_state_anchor(&head::flattened_models(&kept)))
}

/// The conversation's committed context view (read outside the task's own
/// commit, like any host read).
async fn harness_read_context(
    conversation: &Conversation,
    cx: &Context,
) -> SessionResult<eukhe_durable::harness::types::ContextView> {
    conversation.context(cx).await
}

/// The session's compaction reserve tokens (the settings file's
/// `compaction.reserveTokens`, the old engine's default).
fn compaction_reserve_tokens(deps: &super::HostDeps) -> u64 {
    deps.settings
        .manager()
        .settings()
        .compaction
        .as_ref()
        .and_then(|compaction| compaction.reserve_tokens)
        .unwrap_or(DEFAULT_RESERVE_TOKENS)
}

/// Extra request options the auxiliary-model routing resolved.
struct RoutedExtras {
    api_key: Option<String>,
    headers: Option<eukhe_types::pi_ai::ProviderHeaders>,
}

/// Route the summarizer through `auxiliaryModel` when it is set, usable,
/// and its known window fits the exact request this compaction issues (TS
/// #2411 `_resolveAuxiliaryModel`); otherwise the session model with no
/// extras (the session's [`Models`] already carry its auth).
fn route_auxiliary(
    deps: &super::HostDeps,
    session_model: &eukhe_types::pi_ai::Model,
    history: &[eukhe_types::session::AgentMessage],
    previous: Option<&str>,
    anchor: Option<&str>,
    custom_instructions: Option<&str>,
    reserve: u64,
) -> (eukhe_types::pi_ai::Model, RoutedExtras) {
    let context = AuxiliaryModelContext {
        cwd: deps.cwd.clone(),
        agent_dir: deps.agent_dir.clone(),
    };
    let legacy = crate::durable::rlm::refine::legacy_model(session_model);
    let required = crate::session_engine::compact_session::estimate_summary_request_tokens(
        history,
        &[],
        false,
        previous,
        anchor,
        custom_instructions,
        reserve,
    );
    let routed = resolve_auxiliary_model(
        &context,
        "compaction summary",
        &legacy,
        None,
        Some(required),
    );
    let extras = RoutedExtras {
        api_key: routed.api_key,
        headers: routed.headers.map(|headers| {
            headers
                .into_iter()
                .map(|(name, value)| (name, Some(value)))
                .collect()
        }),
    };
    // The routed model rides the session's collection when it is known
    // there (the collection owns provider overrides); an unknown model
    // keeps the session model rather than calling blind.
    let model = deps
        .models
        .get_model(&routed.model.provider, &routed.model.id)
        .unwrap_or_else(|| session_model.clone());
    (model, extras)
}

/// The session's summary delta sink (a fresh clone for a 'static call).
fn sink_for(deps: &super::HostDeps) -> Option<crate::durable::SummaryDeltaSink> {
    deps.summary_delta.clone()
}

/// The custom message row of an unsuccessful compaction (the old engine's
/// `create_compaction_outcome_message`): kept for the observer's rows.
#[must_use]
pub(crate) fn outcome_message(
    content: &str,
    reason: crate::session_engine::messages::CompactionOutcomeReason,
    outcome: crate::session_engine::messages::CompactionOutcomeKind,
) -> eukhe_types::session::CustomMessage {
    create_compaction_outcome_message(content, reason, outcome)
}
