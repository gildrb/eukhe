//! The abandoned-branch summary of a tree move (TS `generateBranchSummary`
//! over `collectEntriesForBranchSummary`): the summarizer call runs on the
//! session's models with the `auxiliaryModel` setting's model (TS #2411),
//! falling back to the main conversation's model, and the summary lands in
//! the moved-to conversation as an `eukhe.branch-summary` entry written
//! through a write submission, with the call's spend added to that
//! conversation's `pi.usage` under the serving model.

use eukhe_chord::context::{AbortSignal, Context};
use eukhe_core::durable::{BranchSummaryData, HostDeps, BRANCH_SUMMARY_ENTRY};
use eukhe_core::session_engine::branch_summarization::{
    build_branch_summary_request, estimate_branch_summary_request_tokens, finalize_branch_summary,
    BranchSummaryDetails, DEFAULT_BRANCH_RESERVE_TOKENS,
};
use eukhe_core::session_engine::compaction_utils::SUMMARIZATION_SYSTEM_PROMPT;
use eukhe_core::session_engine::messages::{BRANCH_SUMMARY_PREFIX, BRANCH_SUMMARY_SUFFIX};
use eukhe_durable::harness::types::WriteSubmissionDraft;
use eukhe_durable::harness::usage::{record_usage, UsageBucket};
use eukhe_durable::harness::Conversation;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{EntryId, TypedEntryDraft};
use eukhe_pi_ai::auth::AuthOperationOptions;
use eukhe_pi_ai::models::ModelsSimpleStreamOptions;
use eukhe_pi_ai::types::{ProviderRequestOptions, SimpleStreamOptions, StreamOptions};
use eukhe_types::pi_ai::{
    AssistantContentBlock, Context as PiContext, Message, Model, StopReason, TextContent, Usage,
    UserContent, UserContentBlock, UserMessage,
};
use eukhe_types::session::FileEntry;
use serde_json::Value;

/// The summarizer call cap (TS `maxTokens: 2048`).
const BRANCH_SUMMARY_MAX_TOKENS: u64 = 2048;
/// The window assumed for a model that reports none.
const DEFAULT_CONTEXT_WINDOW: u64 = 128_000;

/// A finished summary, ready to persist.
pub(crate) struct BranchSummary {
    pub(crate) summary: String,
    /// `{ readFiles, modifiedFiles }`.
    pub(crate) details: Value,
    /// The call's spend under its `provider/modelId` key; `None` when no
    /// request was needed.
    pub(crate) usage: Option<(String, Usage)>,
}

/// How a summary run ended.
pub(crate) enum SummaryOutcome {
    Complete(Box<BranchSummary>),
    /// `abort_branch_summary` cancelled it.
    Aborted,
    Failed(String),
}

/// What to summarize and how.
pub(crate) struct SummaryRequest<'a> {
    /// The abandoned branch, oldest first.
    pub(crate) entries: &'a [FileEntry],
    pub(crate) custom_instructions: Option<&'a str>,
    /// Replace the default prompt instead of appending the custom focus.
    pub(crate) replace_instructions: bool,
}

/// Summarize the abandoned branch with the auxiliary model, or `main`'s.
pub(crate) async fn generate(
    deps: &HostDeps,
    main: &Conversation,
    request: SummaryRequest<'_>,
    signal: AbortSignal,
    cx: &Context,
) -> SummaryOutcome {
    let model_ref = match main.agent(cx).await {
        Ok(agent) => agent.model,
        Err(error) => return SummaryOutcome::Failed(error.to_string()),
    };
    let Some(model_ref) = model_ref else {
        return SummaryOutcome::Failed("No model selected for the branch summary".to_owned());
    };
    let Some(session_model) = deps
        .models
        .get_model(&model_ref.provider, &model_ref.model_id)
    else {
        return SummaryOutcome::Failed(format!(
            "Model {}/{} not found",
            model_ref.provider, model_ref.model_id
        ));
    };
    let settings = deps.settings.manager();
    let reserve = settings
        .settings()
        .branch_summary
        .as_ref()
        .and_then(|settings| settings.reserve_tokens)
        .unwrap_or(DEFAULT_BRANCH_RESERVE_TOKENS);
    // The fit check estimates the request the SESSION model would issue
    // (its window sizes the slice); the routed model re-slices with its own
    // window, exactly like TS.
    let required = estimate_branch_summary_request_tokens(
        request.entries,
        session_model.context_window,
        reserve,
        request.custom_instructions,
        request.replace_instructions,
    );
    let model = resolve_auxiliary_model(
        deps,
        settings.get_auxiliary_model(),
        settings.get_allowed_models().as_deref(),
        session_model,
        required,
    )
    .await;
    let window = if model.context_window > 0 {
        model.context_window
    } else {
        DEFAULT_CONTEXT_WINDOW
    };
    let (messages, preparation) = build_branch_summary_request(
        request.entries,
        window.saturating_sub(reserve),
        request.custom_instructions,
        request.replace_instructions,
    );
    let prompt = messages.iter().find_map(|message| match message {
        eukhe_types::session::AgentMessage::User(user) => match &user.content {
            eukhe_types::ai::UserContent::Text(text) => Some(text.clone()),
            eukhe_types::ai::UserContent::Blocks(_) => None,
        },
        _ => None,
    });
    // Nothing model-visible remains after filtering (TS answers the fixed
    // text without a request).
    let Some(prompt) = prompt else {
        let finalized = finalize_branch_summary("", &preparation);
        return SummaryOutcome::Complete(Box::new(BranchSummary {
            summary: "No content to summarize".to_owned(),
            details: details_value(finalized.read_files, finalized.modified_files),
            usage: None,
        }));
    };
    let options = SimpleStreamOptions {
        stream: StreamOptions {
            request: ProviderRequestOptions {
                signal: Some(signal.clone()),
                ..ProviderRequestOptions::default()
            },
            max_tokens: Some(BRANCH_SUMMARY_MAX_TOKENS),
            ..StreamOptions::default()
        },
        ..SimpleStreamOptions::default()
    };
    let context = PiContext {
        system_prompt: Some(SUMMARIZATION_SYSTEM_PROMPT.to_owned()),
        messages: vec![Message::User(UserMessage {
            content: UserContent::Text(prompt),
            timestamp: crate::util::now_ms(),
        })],
        tools: None,
    };
    let reply = deps
        .models
        .complete_simple(&model, context, ModelsSimpleStreamOptions::from(options))
        .await;
    if signal.aborted() || reply.stop_reason == StopReason::Aborted {
        return SummaryOutcome::Aborted;
    }
    match reply.stop_reason {
        StopReason::Error => {
            return SummaryOutcome::Failed(
                reply
                    .error_message
                    .unwrap_or_else(|| "Branch summary failed".to_owned()),
            )
        }
        StopReason::Pending | StopReason::Deferred => {
            return SummaryOutcome::Failed("Branch summary did not complete".to_owned())
        }
        StopReason::Stop | StopReason::Length | StopReason::ToolUse | StopReason::Aborted => {}
    }
    let text: String = reply
        .content
        .iter()
        .filter_map(|block| match block {
            AssistantContentBlock::Text(text) => Some(text.text.as_str()),
            AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => None,
        })
        .collect();
    let finalized = finalize_branch_summary(&text, &preparation);
    SummaryOutcome::Complete(Box::new(BranchSummary {
        summary: finalized
            .summary
            .unwrap_or_else(|| "No summary generated".to_owned()),
        details: details_value(finalized.read_files, finalized.modified_files),
        usage: Some((format!("{}/{}", reply.provider, reply.model), reply.usage)),
    }))
}

/// TS #2411's `_resolveAuxiliaryModel` over the session's model
/// collection (the durable twin of
/// `eukhe_core::session_engine::auxiliary_model::resolve_auxiliary_model`):
/// an unset, blank, or session-equal selector keeps the session model; a
/// selector outside `allowedModels`, missing from the authenticated
/// catalog, or whose known window is smaller than the request falls back
/// to the session model with the warning.
async fn resolve_auxiliary_model(
    deps: &HostDeps,
    selector: Option<&str>,
    allowlist: Option<&[String]>,
    session_model: Model,
    required_context_tokens: u64,
) -> Model {
    let Some(selector) = selector
        .map(|selector| selector.trim().to_lowercase())
        .filter(|selector| !selector.is_empty())
    else {
        return session_model;
    };
    if format!("{}/{}", session_model.provider, session_model.id).to_lowercase() == selector {
        return session_model;
    }
    let fallback = |model: Model| {
        // The selector is logged, never auth details (TS `CodeQL`
        // `js/clear-text-logging`).
        eprintln!(
            "Warning: auxiliaryModel \"{selector}\" unusable for branch summary; using the session model."
        );
        model
    };
    if allowlist.is_some_and(|allowlist| !eukhe_core::models::model_allowed(&selector, allowlist)) {
        return fallback(session_model);
    }
    let available = deps
        .models
        .get_available(None, AuthOperationOptions::default())
        .await
        .unwrap_or_default();
    let Some(model) = available
        .into_iter()
        .find(|model| format!("{}/{}", model.provider, model.id).to_lowercase() == selector)
    else {
        return fallback(session_model);
    };
    if model.context_window > 0 && model.context_window < required_context_tokens {
        return fallback(session_model);
    }
    model
}

fn details_value(read_files: Vec<String>, modified_files: Vec<String>) -> Value {
    serde_json::to_value(BranchSummaryDetails {
        read_files,
        modified_files,
    })
    .unwrap_or(Value::Null)
}

/// Write `summary` into `conversation` (TS `branchWithSummary`): the entry
/// goes through a write submission keyed by the conversation, so a repeat
/// never duplicates it, and the call's spend joins the conversation's
/// `pi.usage`. Returns the summary entry.
///
/// # Errors
///
/// The draft, the submission, or the usage commit fails, or the write was
/// not placed.
pub(crate) async fn write_summary(
    conversation: &Conversation,
    from_id: String,
    summary: BranchSummary,
    cx: &Context,
) -> SessionResult<EntryId> {
    let timestamp = crate::util::now_ms();
    let model = (!summary.summary.is_empty()).then(|| {
        vec![Message::User(UserMessage {
            content: UserContent::Blocks(vec![UserContentBlock::Text(TextContent::new(format!(
                "{BRANCH_SUMMARY_PREFIX}{}{BRANCH_SUMMARY_SUFFIX}",
                summary.summary
            )))]),
            timestamp,
        })]
    });
    let entry = BRANCH_SUMMARY_ENTRY
        .draft(&TypedEntryDraft {
            model,
            data: BranchSummaryData {
                summary: summary.summary,
                from_id,
                details: Some(summary.details),
                from_hook: None,
                timestamp,
            },
            head: None,
            edits: None,
        })
        .map_err(SessionError::other)?;
    let handle = conversation
        .submit(
            WriteSubmissionDraft {
                request_id: Some(format!("branch-summary:{}", conversation.id())),
                entry,
            },
            cx,
        )
        .await?;
    let settled = handle.wait(cx).await?;
    let state = &settled.record().state;
    let entry = state.entry().ok_or_else(|| {
        SessionError::error(format!(
            "The branch summary was not written: {}",
            state.reason().unwrap_or("unanswered")
        ))
    })?;
    if let Some((key, usage)) = summary.usage {
        let id = conversation.id();
        conversation
            .commit(
                move |tx| async move {
                    record_usage(&tx, id, UsageBucket::Models, &key, &usage).await
                },
                cx,
            )
            .await?;
    }
    Ok(entry)
}
