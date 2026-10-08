//! Cold-boundary digest delivery over the durable conversation (the
//! `_ensureHarnessDigestContext` / `_appendHarnessDigestIfStale` invariant
//! of the old engine): the generation's `before_request` renders a fresh
//! digest and, when the newest in-context digest is stale against it,
//! appends a `eukhe.custom` `harness_digest` entry — `display: false`, the
//! framed digest as its model message, the raw digest and its state
//! fingerprint in `details` — and rides the entry's message on the current
//! request. The append supersedes the older in-context copies with context
//! edits (an `omit` per older digest entry, and the live compaction
//! summary's digest block stripped), so exactly one digest reaches the
//! model; persisted transcripts keep every copy, the newest remaining
//! authoritative. A crash between the commit and the request is benign:
//! the committed digest is fresh, so the next request delivers nothing.
//!
//! Delivery boundaries fall out of the staleness check: a fresh session has
//! no in-context digest (first request), a reopened one keeps its newest
//! digest entry and re-delivers only when the harness state changed
//! (resume), and a compaction head cuts digests out of the context unless
//! the summary itself carries the newest snapshot (compaction head).

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_durable::harness::define::{define_extension, hook};
use eukhe_durable::harness::types::{
    Extension, GenerationHooks, HookApi, HookResult, RequestMessages,
};
use eukhe_durable::harness::GENERATION_TASK;
use eukhe_durable::session::SessionError;
use eukhe_durable::types::{ContextEdit, ContextEditAction, EntryId, EntryRecord};
use eukhe_types::pi_ai::{Message, UserContent, UserMessage};
use futures::FutureExt;

use super::super::entries::{CustomEntryData, CUSTOM_ENTRY};
use super::super::HostDeps;
use super::render::{
    digest_context, digest_from_frame, digest_query_terms, harness_digest_message_text,
    recent_texts_newest_first, render_digest_with_fingerprint, HARNESS_DIGEST_CUSTOM_TYPE,
    HARNESS_DIGEST_PREFIX, HARNESS_DIGEST_SUFFIX,
};
use crate::autonomous::now_millis;

/// The extension name.
pub const DIGEST_EXTENSION: &str = "eukhe.digest";

/// The `eukhe.digest` extension of a session: the digest-delivery
/// `before_request` hook. It installs before `eukhe.optchat`, whose
/// transform collects the new entry as a state row of the call.
#[must_use]
pub(crate) fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let delivering = Arc::clone(deps);
    define_extension(Extension {
        hooks: vec![hook(
            &*GENERATION_TASK,
            GenerationHooks {
                before_request: Some(Arc::new(
                    move |request: &RequestMessages, api: &HookApi, cx: &Context| {
                        deliver(
                            Arc::clone(&delivering),
                            request.clone(),
                            api.clone(),
                            cx.clone(),
                        )
                        .boxed()
                    },
                )),
                ..GenerationHooks::default()
            },
        )],
        ..Extension::named(DIGEST_EXTENSION)
    })
}

/// The `before_request` transform: deliver a stale digest, or keep the
/// request as it is.
async fn deliver(
    deps: Arc<HostDeps>,
    _request: RequestMessages,
    api: HookApi,
    cx: Context,
) -> HookResult<RequestMessages> {
    let harness = deps.harness.require()?;
    let conversation_id = api.conversation_id();
    let Some(conversation) = harness.conversation(conversation_id, &cx).await? else {
        return Ok(None);
    };
    let view = conversation.context(&cx).await?;
    let latest = latest_in_context_digest(&view.entries, &view.contributions);
    let agent = conversation.agent(&cx).await?;
    let tool_names: Vec<&str> = agent.tools.iter().map(|tool| tool.name.as_str()).collect();
    let context = digest_context(&deps, &tool_names);
    let goal = super::super::goals::goal_state(&harness, conversation_id, &cx).await?;
    let terms = digest_query_terms(
        goal.objective.as_deref(),
        &recent_texts_newest_first(&view.messages),
    );
    let fresh = render_digest_with_fingerprint(&context, terms);
    // A fingerprint match is fresh regardless of the rendered text (query
    // terms drive the render only); a fingerprint-less latest (an imported
    // row or a compaction snapshot) compares rendered text instead.
    let fresh_matches = match &latest {
        Some(latest) => match latest.state_fingerprint.as_deref() {
            Some(state_fingerprint) => state_fingerprint == fresh.state_fingerprint,
            None => latest.digest == fresh.digest,
        },
        None => false,
    };
    if fresh_matches {
        return Ok(None);
    }
    let edits = supersede_edits(&view.entries, &view.contributions);
    let details = serde_json::json!({
        "digest": fresh.digest,
        "stateFingerprint": fresh.state_fingerprint,
    });
    let draft = super::super::entries::custom_entry_draft(
        HARNESS_DIGEST_CUSTOM_TYPE,
        UserContent::Text(harness_digest_message_text(&fresh.digest)),
        false,
        Some(details),
        now_millis(),
    )
    .map_err(SessionError::other)?;
    let mut draft = draft;
    draft.edits = (!edits.is_empty()).then_some(edits);
    let message = draft
        .model
        .as_deref()
        .and_then(<[Message]>::first)
        .cloned()
        .expect("a model-visible custom entry carries its message");
    conversation
        .commit(
            move |tx| async move {
                tx.append_entry(conversation_id, draft).await?;
                Ok(())
            },
            &cx,
        )
        .await?;
    // The request reflects the delivery: the superseded copies are omitted
    // (their edits landed with the new entry), and the fresh digest rides
    // ahead of the current turn's prompt rather than at the context tail,
    // where the commit placed it.
    let committed = conversation.context(&cx).await?.messages;
    let mut messages = committed;
    if let Some(at) = messages.iter().rposition(|sent| *sent == message) {
        messages.remove(at);
    }
    Ok(Some(RequestMessages {
        messages: inject(messages, message),
    }))
}

/// The newest in-context digest and its state fingerprint: the newest
/// delivered digest custom row that still contributes messages, unless the
/// compaction head's snapshot (its `harnessDigest` data, or the digest
/// block leading its summary) is newer. Entries out of the active range
/// never appear here, so they never suppress a cold-boundary delivery.
#[derive(Debug, Clone, PartialEq)]
struct LatestDigest {
    entry_id: EntryId,
    digest: String,
    state_fingerprint: Option<String>,
}

fn latest_in_context_digest(
    entries: &[EntryRecord],
    contributions: &[Vec<Message>],
) -> Option<LatestDigest> {
    let mut latest: Option<LatestDigest> = None;
    for (index, entry) in entries.iter().enumerate() {
        let candidate =
            delivered_digest(entry, contributions.get(index)).or_else(|| snapshot_digest(entry));
        if candidate.as_ref().is_some_and(|candidate| {
            latest
                .as_ref()
                .is_none_or(|latest| candidate.entry_id > latest.entry_id)
        }) {
            latest = candidate;
        }
    }
    latest
}

/// A delivered digest entry: a `eukhe.custom` `harness_digest` row whose
/// model messages are still in context. `None` for other rows, digest rows
/// an earlier delivery omitted, and rows whose data does not decode (a
/// corrupt row is not a digest).
fn delivered_digest(
    entry: &EntryRecord,
    contribution: Option<&Vec<Message>>,
) -> Option<LatestDigest> {
    if entry.kind != CUSTOM_ENTRY.kind()
        || !contribution.is_some_and(|messages| !messages.is_empty())
    {
        return None;
    }
    let decoded = CUSTOM_ENTRY.narrow(entry.clone()).ok()??;
    let data: &CustomEntryData = decoded.data();
    if data.custom_type != HARNESS_DIGEST_CUSTOM_TYPE {
        return None;
    }
    let details = data.details.as_ref()?;
    let digest = details.get("digest").and_then(|value| value.as_str())?;
    let state_fingerprint = details
        .get("stateFingerprint")
        .and_then(|value| value.as_str())
        .map(str::to_string);
    Some(LatestDigest {
        entry_id: entry.id,
        digest: digest.to_string(),
        state_fingerprint,
    })
}

/// A compaction head's digest snapshot: the `harnessDigest` /
/// `harnessStateFingerprint` fields of its data, else the digest block
/// leading its summary message. `None` for entries that carry neither.
fn snapshot_digest(entry: &EntryRecord) -> Option<LatestDigest> {
    let data = entry.data.as_ref().map(serde_json::Value::from)?;
    if let Some(digest) = data.get("harnessDigest").and_then(|value| value.as_str()) {
        return Some(LatestDigest {
            entry_id: entry.id,
            digest: digest.to_string(),
            state_fingerprint: data
                .get("harnessStateFingerprint")
                .and_then(|value| value.as_str())
                .map(str::to_string),
        });
    }
    let text = entry
        .model
        .as_deref()
        .and_then(<[Message]>::first)
        .and_then(|message| match message {
            Message::User(user) => user_text(&user.content),
            Message::System(_) | Message::Assistant(_) | Message::ToolResult(_) => None,
        })?;
    let digest = digest_from_frame(&text)?;
    Some(LatestDigest {
        entry_id: entry.id,
        digest: digest.to_string(),
        state_fingerprint: None,
    })
}

/// The context edits a fresh delivery supersedes the older in-context
/// copies with: an `omit` per still-delivered digest entry, and the live
/// compaction summary's leading digest block stripped (its summary text
/// stays, byte-identical with a summary that never carried a snapshot).
fn supersede_edits(entries: &[EntryRecord], contributions: &[Vec<Message>]) -> Vec<ContextEdit> {
    let mut edits: Vec<ContextEdit> = Vec::new();
    for (index, entry) in entries.iter().enumerate() {
        if delivered_digest(entry, contributions.get(index)).is_some() {
            edits.push(ContextEdit {
                target: entry.id,
                action: ContextEditAction::Omit,
            });
        } else if let Some(edit) = strip_summary_digest_block(entry) {
            edits.push(edit);
        }
    }
    edits
}

/// The replace edit that strips a compaction summary's leading digest
/// block; `None` for entries whose first model message is not a digest
/// frame followed by more text.
fn strip_summary_digest_block(entry: &EntryRecord) -> Option<ContextEdit> {
    if entry.kind == CUSTOM_ENTRY.kind() {
        return None;
    }
    let Some(first) = entry.model.as_deref().and_then(<[Message]>::first) else {
        return None;
    };
    let Message::User(user) = first else {
        return None;
    };
    let text = user_text(&user.content)?;
    let digest = digest_from_frame(&text)?;
    let frame = format!("{HARNESS_DIGEST_PREFIX}{digest}{HARNESS_DIGEST_SUFFIX}\n\n");
    let summary = text.strip_prefix(&frame)?;
    Some(ContextEdit {
        target: entry.id,
        action: ContextEditAction::Replace {
            messages: vec![Message::User(UserMessage {
                content: UserContent::Text(summary.to_string()),
                timestamp: user.timestamp,
            })],
        },
    })
}

/// The text of a user message: text blocks joined by newlines.
fn user_text(content: &UserContent) -> Option<String> {
    Some(match content {
        UserContent::Text(text) => text.clone(),
        UserContent::Blocks(blocks) => blocks
            .iter()
            .filter_map(|block| match block {
                eukhe_types::pi_ai::UserContentBlock::Text(text) => Some(text.text.as_str()),
                eukhe_types::pi_ai::UserContentBlock::Image(_) => None,
            })
            .collect::<Vec<_>>()
            .join("\n"),
    })
}

/// Ride the digest message ahead of the current turn's prompt (the last
/// user message of the request), or at its end when the request carries
/// none. `eukhe.optchat`, running after this hook, re-collects the
/// committed entry as a state row of the call, so the message also rides
/// every later request of the run.
fn inject(mut messages: Vec<Message>, digest: Message) -> Vec<Message> {
    let at = messages
        .iter()
        .rposition(|message| matches!(message, Message::User(_)))
        .unwrap_or(messages.len());
    messages.insert(at, digest);
    messages
}
