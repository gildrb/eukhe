//! `eukhe.retry_outcome`: the durable `provider_retry_outcome` disclosure
//! row of a provider failure episode (the old engine's single-line retry
//! UX, SANCTIONED DIVERGENCE of 2026-09-23), on the durable Harness.
//!
//! pi-durable owns the retry loop: a failed attempt's assistant entry lands
//! in the same commit that schedules the retry (`pi.live` generation
//! `retry`), and the episode ends on an assistant entry whose commit
//! schedules none. A post-commit observer watches those entries and, per
//! episode end (idempotent by the ending entry's id, recorded in the
//! conversation's `eukhe.provider_retry.outcomes` document in the same
//! commit as the row), appends ONE row:
//!
//! - a recovered episode (a settled answer after retries): `Recovered after
//!   N retries: <last error>`;
//! - a failed episode: `Retry failed after N attempts: <final error>`, and a
//!   provider failure that never retried (a permanent classification, the
//!   402 wallet drain) still discloses at attempt 0 — no provider failure
//!   settles silently.
//!
//! The attempt count is the run of failed assistant entries right before
//! the ending entry (each retried attempt appended one). Context overflows
//! belong to the compaction observer's rows, and aborts are user actions:
//! neither gets a retry row.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::Extension;
use eukhe_durable::harness::{Conversation, ConversationEntryQuery};
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{
    CommitChange, CommitPublication, ConversationId, DocumentCommitChange, EntryId, EntryRecord,
    LatestFork,
};
use eukhe_pi_ai::utils::overflow::is_context_overflow;
use eukhe_types::pi_ai::{AssistantMessage, Message, StopReason, UserContent};
use futures::FutureExt;
use serde::{Deserialize, Serialize};

use super::{custom_entry_draft, HostDeps, OpenedSession, ServiceStop};
use crate::session_engine::messages::{
    provider_retry_exhausted_text, provider_retry_recovered_text,
    PROVIDER_RETRY_OUTCOME_CUSTOM_TYPE,
};

/// The extension name.
pub const RETRY_OUTCOME_EXTENSION: &str = "eukhe.retry_outcome";

/// The live document whose generation carries a scheduled retry.
const LIVE_DOC_KIND: &str = "pi.live";

/// The faux test provider's queue exhaustion (no provider failure: the
/// old engine's disclosure gate excluded it too).
const FAUX_QUEUE_EXHAUSTED: &str = "No more faux responses queued";

static OUTCOMES_DOC: ConversationDoc<OutcomesState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.provider_retry.outcomes",
        version: 1,
        initial: OutcomesState::default,
        migrate: None,
        checkpoint_when: Some(|_, _, _| true),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.provider_retry.outcomes has a valid version"),
};

/// The ending entry ids whose episode already produced its row, `true`.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct OutcomesState {
    /// The ending entry ids already recorded.
    pub recorded: HashMap<String, bool>,
}

/// One episode end the observer services.
enum Observed {
    Ended {
        conversation_id: ConversationId,
        entry_id: EntryId,
        message: Box<AssistantMessage>,
    },
}

/// The `eukhe.retry_outcome` extension of a session: no hooks, only the
/// post-commit observer started at open.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    deps.add_service(Box::new(start));
    define_extension(Extension::named(RETRY_OUTCOME_EXTENSION))
}

/// Start the observer on the opened session; the stop unsubscribes and
/// ends the service task (servicing the facts already queued).
fn start(
    opened: OpenedSession,
) -> futures::future::BoxFuture<'static, SessionResult<Option<ServiceStop>>> {
    async move {
        let (events, mut event_rx) = tokio::sync::mpsc::unbounded_channel::<Observed>();
        // Conversations with a retry scheduled since their last episode
        // end: only those turn a settled answer into a recovered row (a
        // first-try answer needs no entry scan). In memory: a worker
        // restart mid-episode loses the recovered row, never a failure's.
        let retrying: Arc<Mutex<HashSet<ConversationId>>> = Arc::default();
        let commits = opened.harness.subscribe_commits(Arc::new(
            move |publication: &CommitPublication, _cx: &Context| {
                for change in &publication.changes {
                    let CommitChange::Entry(entry) = change else {
                        continue;
                    };
                    if let Some(observed) = episode_end(entry, publication, &retrying) {
                        let _ = events.send(observed);
                    }
                }
            },
        ))?;
        let close = Arc::new(tokio::sync::Notify::new());
        let close_signal = Arc::clone(&close);
        let subscription = opened.harness.subscribe_close(Arc::new(move || {
            close_signal.notify_one();
        }))?;
        let harness = opened.harness.clone();
        let task_close = Arc::clone(&close);
        let task = tokio::spawn(async move {
            loop {
                tokio::select! {
                    event = event_rx.recv() => {
                        let Some(event) = event else { break };
                        service(&harness, event).await;
                    }
                    () = task_close.notified() => {
                        while let Ok(event) = event_rx.try_recv() {
                            service(&harness, event).await;
                        }
                        break;
                    }
                }
            }
        });
        let stop: ServiceStop = Box::new(move || {
            async move {
                drop(commits);
                drop(subscription);
                close.notify_one();
                let _ = task.await;
            }
            .boxed()
        });
        Ok(Some(stop))
    }
    .boxed()
}

/// The episode end `entry` stands for, when it is an assistant entry whose
/// commit schedules no retry: a provider failure (gated like the old
/// disclosure), or a settled answer after a scheduled retry.
fn episode_end(
    entry: &EntryRecord,
    publication: &CommitPublication,
    retrying: &Mutex<HashSet<ConversationId>>,
) -> Option<Observed> {
    if entry.kind != ASSISTANT_ENTRY.kind() {
        return None;
    }
    let message = entry
        .model
        .as_deref()
        .and_then(<[Message]>::first)
        .and_then(Message::as_assistant)?;
    let mut retrying = retrying.lock().unwrap_or_else(PoisonError::into_inner);
    if schedules_retry(entry.conversation_id, publication) {
        retrying.insert(entry.conversation_id);
        return None;
    }
    let was_retrying = retrying.remove(&entry.conversation_id);
    let reported = match message.stop_reason {
        // Overflow recovery reports through the compaction rows.
        StopReason::Error => !is_context_overflow(message, None),
        StopReason::Aborted => false,
        StopReason::Stop
        | StopReason::Length
        | StopReason::ToolUse
        | StopReason::Pending
        | StopReason::Deferred => was_retrying,
    };
    reported.then(|| Observed::Ended {
        conversation_id: entry.conversation_id,
        entry_id: entry.id,
        message: Box::new(message.clone()),
    })
}

/// Whether the commit sets a scheduled retry on the conversation's live
/// generation (pi-durable commits the failed attempt with it).
fn schedules_retry(conversation_id: ConversationId, publication: &CommitPublication) -> bool {
    publication.changes.iter().any(|change| {
        matches!(
            change,
            CommitChange::Document(DocumentCommitChange::Document {
                record,
                conversation_id: Some(owner),
                value: Some(value),
                ..
            }) if record.kind == LIVE_DOC_KIND
                && *owner == conversation_id
                && value
                    .get("generation")
                    .and_then(|generation| generation.get("retry"))
                    .is_some_and(|retry| !retry.is_null())
        )
    })
}

/// Service one episode end; a failure is logged (the row is a disclosure,
/// never a reason to fail the session).
async fn service(harness: &eukhe_durable::harness::Harness, event: Observed) {
    let Observed::Ended {
        conversation_id,
        entry_id,
        message,
    } = event;
    let cx = BACKGROUND_CONTEXT.clone();
    let handled = async {
        let Some(conversation) = harness.conversation(conversation_id, &cx).await? else {
            return Ok(());
        };
        let failed = failed_attempts_before(&conversation, entry_id, &cx).await?;
        let Some(row) = outcome_row(&message, &failed) else {
            return Ok(());
        };
        record_row(&conversation, entry_id, row, &cx).await
    };
    if let Err(error) = handled.await {
        tracing::warn!(target: "eukhe.retry_outcome", "provider retry outcome row failed: {error:#}");
    }
}

/// The failed attempts of the episode `entry_id` ends: the run of failed
/// assistant entries right before it.
async fn failed_attempts_before(
    conversation: &Conversation,
    entry_id: EntryId,
    cx: &Context,
) -> anyhow::Result<Vec<AssistantMessage>> {
    let mut failed = Vec::new();
    let mut cursor = None;
    loop {
        let page = conversation
            .entries(
                ConversationEntryQuery {
                    max_entry_id: Some(entry_id),
                    ..ConversationEntryQuery::default()
                },
                16,
                cursor,
                cx,
            )
            .await?;
        for entry in page.items {
            if entry.id >= entry_id {
                continue;
            }
            let attempt = (entry.kind == ASSISTANT_ENTRY.kind())
                .then(|| {
                    entry
                        .model
                        .as_deref()
                        .and_then(<[Message]>::first)
                        .and_then(Message::as_assistant)
                        .filter(|message| message.stop_reason == StopReason::Error)
                        .cloned()
                })
                .flatten();
            match attempt {
                Some(message) => failed.push(message),
                None => return Ok(failed),
            }
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => return Ok(failed),
        }
    }
}

/// The episode's row: `(success, attempts, error)` over the old texts, or
/// `None` for a first-attempt failure that is no provider failure.
fn outcome_row(ending: &AssistantMessage, failed: &[AssistantMessage]) -> Option<RetryRow> {
    let attempts = u32::try_from(failed.len()).unwrap_or(u32::MAX);
    if ending.stop_reason == StopReason::Error {
        if attempts == 0 && !is_provider_failure(ending) {
            return None;
        }
        return Some(RetryRow {
            success: false,
            attempts,
            error: error_text(ending),
        });
    }
    let last = failed.first()?;
    Some(RetryRow {
        success: true,
        attempts,
        error: error_text(last),
    })
}

/// One episode verdict.
struct RetryRow {
    success: bool,
    attempts: u32,
    error: String,
}

/// Whether a failed message carries the provider stream failure diagnostic
/// (the old engine's disclosure gate): agent-lifecycle failures and the
/// faux queue exhaustion carry none.
fn is_provider_failure(message: &AssistantMessage) -> bool {
    let faux_exhausted = message.provider == "faux"
        && message.error_message.as_deref() == Some(FAUX_QUEUE_EXHAUSTED);
    !faux_exhausted
        && message.diagnostics.as_ref().is_some_and(|diagnostics| {
            diagnostics.iter().any(|diagnostic| {
                diagnostic.kind == "provider_stream_failure" && diagnostic.details.is_some()
            })
        })
}

/// The user-visible error text of a failed attempt (TS `errorMessage ||
/// "Unknown error"`).
fn error_text(message: &AssistantMessage) -> String {
    message
        .error_message
        .as_deref()
        .filter(|error| !error.is_empty())
        .unwrap_or("Unknown error")
        .to_owned()
}

/// Append the row once per ending entry: the outcomes document records the
/// entry in the same commit, so a replayed observation cannot double-write.
async fn record_row(
    conversation: &Conversation,
    entry_id: EntryId,
    row: RetryRow,
    cx: &Context,
) -> anyhow::Result<()> {
    let content = if row.success {
        provider_retry_recovered_text(row.attempts, &row.error)
    } else {
        provider_retry_exhausted_text(row.attempts, &row.error)
    };
    let draft_entry = custom_entry_draft(
        PROVIDER_RETRY_OUTCOME_CUSTOM_TYPE,
        UserContent::Text(content),
        true,
        Some(serde_json::json!({
            "success": row.success,
            "attempts": row.attempts,
            "finalError": row.error,
        })),
        crate::durable::rlm::now_millis(),
    )?;
    let key = entry_id.to_string();
    let conversation_id = conversation.id();
    conversation
        .commit(
            move |tx| async move {
                let draft = tx.doc(&OUTCOMES_DOC, conversation_id).await?;
                let mut recorded: HashMap<String, bool> = match draft.get("recorded")? {
                    Some(item) => eukhe_chord::json::from_json(&item.to_value()?)?,
                    None => HashMap::new(),
                };
                if recorded.contains_key(key.as_str()) {
                    return Ok(());
                }
                recorded.insert(key, true);
                draft.set(
                    "recorded",
                    eukhe_chord::json::to_json(&recorded)
                        .map_err(eukhe_durable::session::SessionError::other)?,
                )?;
                tx.append_entry(conversation_id, draft_entry).await?;
                Ok(())
            },
            cx,
        )
        .await?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn message(stop_reason: &str, error: Option<&str>, provider_failure: bool) -> AssistantMessage {
        let mut value = serde_json::json!({
            "role": "assistant", "content": [], "api": "openai-completions",
            "provider": "prime", "model": "m", "stopReason": stop_reason, "timestamp": 0,
            "usage": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0,
                       "totalTokens": 0,
                       "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0,
                                 "total": 0 } },
        });
        if let Some(error) = error {
            value["errorMessage"] = serde_json::Value::from(error);
        }
        if provider_failure {
            value["diagnostics"] = serde_json::json!([{
                "type": "provider_stream_failure", "timestamp": 0,
                "details": { "kind": "payment_required" },
            }]);
        }
        serde_json::from_value(value).expect("assistant message")
    }

    fn failure(error: &str, provider_failure: bool) -> AssistantMessage {
        message("error", Some(error), provider_failure)
    }

    /// The episode verdicts: a recovered answer names the newest failed
    /// attempt's error, an exhausted one the final error, and a
    /// first-attempt failure discloses only when it is a provider failure.
    #[test]
    fn rows_follow_the_episode_shape() {
        let answer = message("stop", None, false);
        let recovered = outcome_row(&answer, &[failure("second", true), failure("first", true)])
            .expect("recovered row");
        assert!(recovered.success);
        assert_eq!(
            (recovered.attempts, recovered.error.as_str()),
            (2, "second")
        );
        assert!(outcome_row(&answer, &[]).is_none());

        let exhausted =
            outcome_row(&failure("final", true), &[failure("earlier", true)]).expect("row");
        assert!(!exhausted.success);
        assert_eq!((exhausted.attempts, exhausted.error.as_str()), (1, "final"));

        let permanent = outcome_row(&failure("402 drained", true), &[]).expect("row");
        assert_eq!((permanent.attempts, permanent.success), (0, false));
        assert!(outcome_row(&failure("lifecycle", false), &[]).is_none());
    }
}
