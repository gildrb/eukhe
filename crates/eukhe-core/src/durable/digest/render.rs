//! The digest composition half of `session_engine::harness_digest`: render
//! the continual-harness state (merged global + local) into the
//! model-facing digest body plus the fingerprint of the state that produced
//! it. One merged-state read feeds both, so the fingerprint always matches
//! the rendered digest's material; relevance query terms drive the render
//! but stay out of the fingerprint (the digest is frozen per delivery).

use std::path::PathBuf;

use eukhe_chord::context::Context;
use eukhe_durable::harness::Conversation;
use eukhe_durable::session::SessionResult;
use eukhe_types::pi_ai::{AssistantContentBlock, Message, UserContent, UserContentBlock};

use crate::refinement::ranking::{
    format_harness_state_for_prompt, harness_digest_fingerprint, harness_query_terms,
    HarnessDigestRenderFlags, HarnessQueryTerms, HarnessStatePromptOptions,
};
use crate::refinement::{
    get_global_harness_state_dir, get_local_harness_state_dir, load_harness_state,
    merge_harness_states, HarnessScope,
};

use super::super::HostDeps;

/// The custom row type of a delivered digest (the old engine's
/// `HARNESS_DIGEST_CUSTOM_TYPE`).
pub const HARNESS_DIGEST_CUSTOM_TYPE: &str = "harness_digest";

/// Full digest frame prefix (the old engine's `HARNESS_DIGEST_PREFIX`).
pub const HARNESS_DIGEST_PREFIX: &str =
    "[harness-digest]\n\nThe persistent memories produced across this session so far:\n\n<harness_state>\n";
/// Full digest frame suffix (the old engine's `HARNESS_DIGEST_SUFFIX`).
pub const HARNESS_DIGEST_SUFFIX: &str = "\n</harness_state>";

/// Session-scoped digest inputs: where harness state lives and which
/// interfaces the digest may reference.
#[derive(Debug, Clone)]
pub struct HarnessDigestContext {
    /// Global harness state directory (`<agent dir>/harness`).
    pub global_dir: PathBuf,
    /// Session-local harness state directory (session artifact dir), when the
    /// session persists artifacts.
    pub local_dir: Option<PathBuf>,
    /// The session exposes the Python REPL (`ipython` tool active).
    pub include_ipython: bool,
    /// The session exposes `bash` as a model tool.
    pub include_shell_examples: bool,
    /// The `refine` skill is visible to the model.
    pub include_refine: bool,
}

/// The digest inputs of a durable session: harness-state directories from
/// the deps, interface flags from the conversation's resolved tool names
/// and the loaded skills.
#[must_use]
pub fn digest_context(deps: &HostDeps, tool_names: &[&str]) -> HarnessDigestContext {
    HarnessDigestContext {
        global_dir: get_global_harness_state_dir(&deps.agent_dir),
        local_dir: get_local_harness_state_dir(deps.storage_dir.as_deref()),
        include_ipython: tool_names.contains(&"ipython"),
        include_shell_examples: tool_names.contains(&"bash"),
        include_refine: deps.resources.skills.iter().any(|skill| {
            !skill.disable_model_invocation
                && skill.name == crate::prompts::system_prompt::REFINE_SKILL_NAME
        }),
    }
}

/// Relevance terms for digest entry ranking: the active goal objective
/// (strongest) plus the last few user/assistant texts, newest first (the
/// old engine's `digest_query_terms`).
#[must_use]
pub fn digest_query_terms(
    goal_objective: Option<&str>,
    recent_texts_newest_first: &[String],
) -> HarnessQueryTerms {
    fn add_text(terms: &mut HarnessQueryTerms, text: &str, weight: f64) {
        for raw in harness_query_terms(text) {
            if terms.len() >= 48 && !terms.contains_key(&raw) {
                return;
            }
            terms.entry(raw).or_insert(weight);
        }
    }
    let mut terms: HarnessQueryTerms = std::collections::HashMap::new();
    add_text(&mut terms, goal_objective.unwrap_or_default(), 3.0);
    let mut recency_weight = 2.0;
    for text in recent_texts_newest_first.iter().take(4) {
        add_text(&mut terms, text, recency_weight);
        recency_weight = (recency_weight - 0.5).max(1.0);
    }
    terms
}

/// One digest render: the body plus the fingerprint of the harness state
/// that produced it.
#[derive(Debug, Clone, PartialEq)]
pub struct HarnessDigestRender {
    pub digest: String,
    pub state_fingerprint: String,
}

/// Render the digest body and its state fingerprint from one merged-state
/// read.
#[must_use]
pub fn render_digest_with_fingerprint(
    context: &HarnessDigestContext,
    query_terms: HarnessQueryTerms,
) -> HarnessDigestRender {
    let global = load_harness_state(&context.global_dir, HarnessScope::Global);
    let local = context
        .local_dir
        .as_ref()
        .map(|dir| load_harness_state(dir, HarnessScope::Local));
    let merged = merge_harness_states(&global, local.as_ref());
    let render_flags = HarnessDigestRenderFlags {
        include_ipython_examples: context.include_ipython,
        include_shell_examples: context.include_shell_examples,
        // TS: includeRefineExamples = hasIpython && hasRefineSkill.
        include_refine_examples: context.include_ipython && context.include_refine,
    };
    let digest = format_harness_state_for_prompt(
        &merged,
        &HarnessStatePromptOptions {
            include_ipython_examples: Some(context.include_ipython),
            include_shell_examples: context.include_shell_examples,
            include_refine_examples: Some(render_flags.include_refine_examples),
            query_terms: Some(query_terms),
            ..Default::default()
        },
    );
    let state_fingerprint = harness_digest_fingerprint(&merged, render_flags);
    HarnessDigestRender {
        digest,
        state_fingerprint,
    }
}

/// The digest of `conversation` right now: interface flags from its
/// resolved agent, relevance terms from the active goal objective and the
/// conversation's recent texts.
///
/// # Errors
///
/// Agent, goal, or context reads fail.
pub async fn conversation_digest(
    deps: &HostDeps,
    conversation: &Conversation,
    cx: &Context,
) -> SessionResult<HarnessDigestRender> {
    let harness = deps.harness.require()?;
    let agent = conversation.agent(cx).await?;
    let tool_names: Vec<&str> = agent.tools.iter().map(|tool| tool.name.as_str()).collect();
    let context = digest_context(deps, &tool_names);
    let view = conversation.context(cx).await?;
    let goal = super::super::goals::goal_state(&harness, conversation.id(), cx).await?;
    let terms = digest_query_terms(
        goal.objective.as_deref(),
        &recent_texts_newest_first(&view.messages),
    );
    Ok(render_digest_with_fingerprint(&context, terms))
}

/// The last four user/assistant texts, newest first (digest ranking; TS
/// `.filter(user || assistant).slice(-4).reverse()`).
#[must_use]
pub fn recent_texts_newest_first(messages: &[Message]) -> Vec<String> {
    let mut texts: Vec<String> = messages
        .iter()
        .filter_map(|message| match message {
            Message::User(user) => Some(user_text(&user.content)),
            Message::Assistant(assistant) => {
                let text = assistant
                    .content
                    .iter()
                    .filter_map(|block| match block {
                        AssistantContentBlock::Text(text) => Some(text.text.clone()),
                        AssistantContentBlock::Thinking(_) | AssistantContentBlock::ToolCall(_) => {
                            None
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                (!text.is_empty()).then_some(text)
            }
            Message::System(_) | Message::ToolResult(_) => None,
        })
        .collect();
    // `.slice(-4)`: keep the newest four texts (the window tail), then
    // reverse to newest first.
    if texts.len() > 4 {
        texts.drain(..texts.len() - 4);
    }
    texts.reverse();
    texts
}

/// The text of a user message: text blocks joined by newlines.
fn user_text(content: &UserContent) -> String {
    match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(|block| match block {
                UserContentBlock::Text(text) => Some(text.text.as_str()),
                UserContentBlock::Image(_) => None,
            })
            .collect::<Vec<_>>()
            .join("\n"),
    }
}

/// Full digest message text (prefix + state + suffix).
#[must_use]
pub fn harness_digest_message_text(digest: &str) -> String {
    format!("{HARNESS_DIGEST_PREFIX}{digest}{HARNESS_DIGEST_SUFFIX}")
}

/// The raw digest carried by a framed text (a delivered digest row or the
/// digest block that leads a compaction summary), if any.
#[must_use]
pub fn digest_from_frame(text: &str) -> Option<&str> {
    let after_prefix = text.strip_prefix(HARNESS_DIGEST_PREFIX).or_else(|| {
        text.find(HARNESS_DIGEST_PREFIX)
            .map(|at| &text[at + HARNESS_DIGEST_PREFIX.len()..])
    })?;
    let end = after_prefix
        .find(HARNESS_DIGEST_SUFFIX)
        .map(|at| &after_prefix[..at])?;
    Some(end.trim_end_matches('\n'))
}
