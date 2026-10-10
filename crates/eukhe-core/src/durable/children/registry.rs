//! The children registry: the `eukhe.rlm.children` conversation document
//! (one row per `eukhe.rlm.child` task, keyed by task id), selector
//! resolution, and child-usage attribution into the parent's `pi.usage`
//! plus the `eukhe.child-usage-attributed` rows that name the spawning
//! assistant row.

use super::host::RlmChildIdentity;
use crate::durable::observe::rlm_usage::{
    attributed_aggregate, attribution_draft, entry_assistant_usage, CHILD_USAGE_ATTRIBUTED_KIND,
};
use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonObject, JsonValue};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::harness::usage::{record_usage, UsageBucket};
use eukhe_durable::session::{SessionError, SessionResult, Tx};
use eukhe_durable::types::{
    ConversationId, DocumentReader, DocumentReaderExt, EntryId, EntryQuery, LatestFork, TaskId,
};
use eukhe_types::pi_ai::{IndexMap, Usage, UsageCost};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::sync::Arc;

/// The `pi.usage` tools-bucket key child spend is attributed under: the
/// parent's billable totals include every child's spend; the per-child split
/// lives in the child's registry row.
pub(crate) const CHILD_USAGE_KEY: &str = "eukhe.rlm.child";

/// Children of one conversation, in spawn order.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub(crate) struct ChildrenState {
    /// Rows keyed by the child task id (decimal string).
    pub(crate) children: IndexMap<String, ChildRow>,
}

/// Run status of a child.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) enum ChildStatus {
    /// Admitted; the host has not created the session yet.
    Spawning,
    Running,
    Done,
    Error,
    Cancelled,
}

impl ChildStatus {
    /// Whether the run reached its verdict (TS `run.status` past running).
    pub(crate) fn is_terminal(self) -> bool {
        match self {
            Self::Spawning | Self::Running => false,
            Self::Done | Self::Error | Self::Cancelled => true,
        }
    }

    /// `rlm.collect` status: `queued` | `running` | `done` | `error` |
    /// `cancelled`.
    pub(crate) fn collect_status(self) -> &'static str {
        match self {
            Self::Spawning => "queued",
            Self::Running => "running",
            Self::Done => "done",
            Self::Error => "error",
            Self::Cancelled => "cancelled",
        }
    }

    /// `rlm.list_subagents` status: `running` | `completed` | `error` |
    /// `cancelled`.
    pub(crate) fn roster_status(self) -> &'static str {
        match self {
            Self::Spawning | Self::Running => "running",
            Self::Done => "completed",
            Self::Error => "error",
            Self::Cancelled => "cancelled",
        }
    }
}

/// One child of the conversation.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct ChildRow {
    pub(crate) task_id: u64,
    pub(crate) rlm_child_id: String,
    pub(crate) session_id: String,
    pub(crate) session_name: String,
    pub(crate) label: String,
    /// Harness clock at admission (ms).
    pub(crate) started_at: f64,
    pub(crate) status: ChildStatus,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) active_session_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) session_dir: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) model: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) answer_preview: Option<String>,
    /// Terminal error text: the failure, or the cancel/delete reason.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) error: Option<String>,
    #[serde(default)]
    pub(crate) replied_since_task: bool,
    /// Where a delete of this child stands; `None` while not deleted.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) deletion: Option<ChildDeletion>,
    /// The child task is terminal (its report, if any, was submitted).
    #[serde(default)]
    pub(crate) settled: bool,
    /// Child spend already attributed to the parent (cumulative).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) usage: Option<Usage>,
}

impl ChildRow {
    /// The selector set a child answers to: its child id, routing id,
    /// session name, or session id.
    pub(crate) fn matches(&self, target: &str) -> bool {
        self.matches_id(target) || self.session_name == target
    }

    /// The id selectors only (the `rlm.rename` target resolution): a child
    /// handle or full session id, never the name.
    pub(crate) fn matches_id(&self, target: &str) -> bool {
        self.rlm_child_id == target
            || self.active_session_id.as_deref() == Some(target)
            || self.session_id == target
    }

    pub(crate) fn task_id(&self) -> TaskId {
        TaskId::from_number(self.task_id)
    }

    /// A delete was requested: the task's abort owes the cancelled notice.
    pub(crate) fn delete_requested(&self) -> bool {
        self.deletion.is_some()
    }

    /// Deleted: a tombstone `rlm.collect` answers with a cancelled envelope.
    pub(crate) fn is_deleted(&self) -> bool {
        self.deletion == Some(ChildDeletion::Deleted)
    }
}

/// Progress of a child's delete.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) enum ChildDeletion {
    /// The delete aborts the child task; the host teardown follows.
    Requested,
    /// The host tore the child down; the row is a tombstone.
    Deleted,
}

pub(crate) static CHILDREN_DOC: ConversationDoc<ChildrenState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.rlm.children",
        version: 1,
        initial: ChildrenState::default,
        migrate: None,
        checkpoint_when: None,
    },
    // Children belong to the conversation that spawned them; a fork starts
    // without any.
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.rlm.children has a valid version"),
};

/// The deterministic identity of the child of task `task_id` in parent
/// session `parent_session_id`: a rerun of the spawn names the same child.
pub(crate) fn child_identity(parent_session_id: &str, task_id: TaskId) -> RlmChildIdentity {
    let digest = Sha256::digest(format!("eukhe.rlm.child:{parent_session_id}:{task_id}"));
    let mut bytes = [0_u8; 16];
    bytes.copy_from_slice(&digest[..16]);
    let session_id = uuid::Builder::from_random_bytes(bytes).into_uuid();
    let simple = session_id.simple().to_string();
    RlmChildIdentity {
        rlm_child_id: format!("sub-{}", &simple[..8]),
        session_id: session_id.to_string(),
    }
}

fn decode_state(value: Option<Arc<JsonObject>>) -> SessionResult<ChildrenState> {
    match value {
        None => Ok(ChildrenState::default()),
        Some(value) => Ok(from_json(&JsonValue::Object(value))?),
    }
}

/// The committed children of `conversation_id`.
pub(crate) async fn read_children(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<ChildrenState> {
    decode_state(reader.snapshot(&CHILDREN_DOC, conversation_id, cx).await?)
}

/// Whether any child of `conversation_id` is unsettled: its
/// `eukhe.rlm.child` task has not ended (the run or its report is still
/// owed). Goal and autonomous continuations defer while this holds.
///
/// # Errors
///
/// Document read failures.
pub async fn has_unsettled_children(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<bool> {
    let state = read_children(reader, conversation_id, cx).await?;
    Ok(state.children.values().any(|row| !row.settled))
}

/// The row of `task_id` inside a commit.
pub(crate) async fn tx_row(
    tx: &Tx,
    conversation_id: ConversationId,
    task_id: TaskId,
) -> SessionResult<Option<ChildRow>> {
    let children = tx
        .doc(&CHILDREN_DOC, conversation_id)
        .await?
        .child("children")?;
    match children.get(task_id.to_string())? {
        None => Ok(None),
        Some(item) => Ok(Some(from_json(&item.to_value()?)?)),
    }
}

/// Every row of the conversation inside a commit.
pub(crate) async fn tx_children(
    tx: &Tx,
    conversation_id: ConversationId,
) -> SessionResult<ChildrenState> {
    let value = tx.doc(&CHILDREN_DOC, conversation_id).await?.value()?;
    Ok(from_json(&value)?)
}

/// Write `row` inside a commit.
pub(crate) async fn tx_put_row(
    tx: &Tx,
    conversation_id: ConversationId,
    row: &ChildRow,
) -> SessionResult<()> {
    let children = tx
        .doc(&CHILDREN_DOC, conversation_id)
        .await?
        .child("children")?;
    children.set(row.task_id.to_string(), to_json(row)?)?;
    Ok(())
}

/// Remove the row of `task_id` inside a commit (a failed admission leaves no
/// child behind).
pub(crate) async fn tx_remove_row(
    tx: &Tx,
    conversation_id: ConversationId,
    task_id: TaskId,
) -> SessionResult<()> {
    let children = tx
        .doc(&CHILDREN_DOC, conversation_id)
        .await?
        .child("children")?;
    children.delete(task_id.to_string())?;
    Ok(())
}

/// Change the row of `task_id` inside a commit.
///
/// # Errors
///
/// `RLM child task {id} has no registry row` when the row is gone.
pub(crate) async fn tx_update_row(
    tx: &Tx,
    conversation_id: ConversationId,
    task_id: TaskId,
    change: impl FnOnce(&mut ChildRow),
) -> SessionResult<ChildRow> {
    let Some(mut row) = tx_row(tx, conversation_id, task_id).await? else {
        return Err(SessionError::error(format!(
            "RLM child task {task_id} has no registry row"
        )));
    };
    change(&mut row);
    tx_put_row(tx, conversation_id, &row).await?;
    Ok(row)
}

/// Attribute the child's spend observed since the last attribution: the
/// delta between `cumulative` and the row's attributed total lands in the
/// parent's `pi.usage` (tools bucket, [`CHILD_USAGE_KEY`]) and one
/// `eukhe.child-usage-attributed` entry names the spawning assistant row
/// with the cumulative aggregate, in the same commit that advances the
/// row, so a rerun never bills twice. Without an assistant row to fold
/// (a spawn outside a model turn) the delta still bills, with no row —
/// the old engine's unregistered-child drop.
pub(crate) async fn tx_attribute_usage(
    tx: &Tx,
    conversation_id: ConversationId,
    row: &mut ChildRow,
    cumulative: &Usage,
) -> SessionResult<()> {
    let attributed = row.usage.unwrap_or_default();
    let delta = usage_delta(cumulative, &attributed);
    if delta == Usage::default() {
        return Ok(());
    }
    record_usage(
        tx,
        conversation_id,
        UsageBucket::Tools,
        CHILD_USAGE_KEY,
        &delta,
    )
    .await?;
    let mut total = attributed;
    eukhe_durable::harness::usage::add_usage(&mut total, &delta);
    row.usage = Some(total);
    let cumulative_total = total;
    if let Some(target) = tx_attribution_target(tx, conversation_id).await? {
        // The row's aggregate is the row's own usage plus the CUMULATIVE
        // child usage (the old engine rewrote the row to own +
        // cumulative); the entry is immutable, so `own` is always the
        // assistant row's own usage and never a prior aggregate.
        let aggregate = attributed_aggregate(&target.own, &cumulative_total, target.context_tokens);
        tx.append_entry(
            conversation_id,
            attribution_draft(target.entry_id, &delta, &aggregate)?,
        )
        .await?;
    }
    Ok(())
}

/// The parent assistant row a child-usage attribution targets.
struct AttributionTarget {
    entry_id: EntryId,
    /// The row's own model-facing context size (`totalTokens`).
    context_tokens: u64,
    /// The row's own usage — the immutable base every cumulative
    /// aggregate sums onto.
    own: Usage,
}

/// Resolve the attribution target of `conversation_id` inside a commit:
/// the newest assistant entry (the old `_findLastAssistantMessage`) and
/// its own usage; `None` when the conversation has no assistant row.
async fn tx_attribution_target(
    tx: &Tx,
    conversation_id: ConversationId,
) -> SessionResult<Option<AttributionTarget>> {
    let mut cursor = None;
    loop {
        let page = tx
            .scan_entries(
                EntryQuery::new(conversation_id),
                ATTRIBUTION_SCAN_PAGE,
                cursor,
            )
            .await?;
        for entry in &page.items {
            if entry.kind != CHILD_USAGE_ATTRIBUTED_KIND {
                if let Some(usage) = entry_assistant_usage(entry) {
                    return Ok(Some(AttributionTarget {
                        entry_id: entry.id,
                        context_tokens: usage.total_tokens,
                        own: usage,
                    }));
                }
            }
        }
        if page.next.is_none() {
            return Ok(None);
        }
        cursor = page.next;
    }
}

/// Entries per attribution-target scan page.
const ATTRIBUTION_SCAN_PAGE: usize = 64;

/// What `current` adds over `previous`; a counter the host reports lower
/// (a restarted host recounting) adds nothing.
fn usage_delta(current: &Usage, previous: &Usage) -> Usage {
    let optional = |current: Option<u64>, previous: Option<u64>| {
        current.map(|value| value.saturating_sub(previous.unwrap_or(0)))
    };
    let cost = |current: f64, previous: f64| (current - previous).max(0.0);
    Usage {
        input: current.input.saturating_sub(previous.input),
        output: current.output.saturating_sub(previous.output),
        cache_read: current.cache_read.saturating_sub(previous.cache_read),
        cache_write: current.cache_write.saturating_sub(previous.cache_write),
        cache_write_1h: optional(current.cache_write_1h, previous.cache_write_1h)
            .filter(|value| *value > 0),
        reasoning: optional(current.reasoning, previous.reasoning).filter(|value| *value > 0),
        total_tokens: current.total_tokens.saturating_sub(previous.total_tokens),
        cost: UsageCost {
            input: cost(current.cost.input, previous.cost.input),
            output: cost(current.cost.output, previous.cost.output),
            cache_read: cost(current.cost.cache_read, previous.cost.cache_read),
            cache_write: cost(current.cost.cache_write, previous.cost.cache_write),
            total: cost(current.cost.total, previous.cost.total),
        },
    }
}

/// The selector errors of a roster lookup (TS `No direct RLM {kind}
/// matches ...` / `... is ambiguous ...`).
pub(crate) enum Resolved<'a> {
    One(&'a ChildRow),
    None,
    Ambiguous,
}

/// The one row among `rows` that `target` selects.
pub(crate) fn resolve<'a>(rows: impl Iterator<Item = &'a ChildRow>, target: &str) -> Resolved<'a> {
    let mut found: Option<&ChildRow> = None;
    for row in rows.filter(|row| row.matches(target)) {
        if found.is_some() {
            return Resolved::Ambiguous;
        }
        found = Some(row);
    }
    found.map_or(Resolved::None, Resolved::One)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn child_identity_is_deterministic_per_task() {
        let first = child_identity("parent", TaskId::from_number(7));
        assert_eq!(first, child_identity("parent", TaskId::from_number(7)));
        assert_ne!(first, child_identity("parent", TaskId::from_number(8)));
        assert_ne!(first, child_identity("other", TaskId::from_number(7)));
        assert!(first.rlm_child_id.starts_with("sub-"));
        assert_eq!(first.rlm_child_id.len(), 12);
        assert!(first.session_id.starts_with(&first.rlm_child_id[4..]));
        assert!(uuid::Uuid::parse_str(&first.session_id).is_ok());
    }

    #[test]
    fn usage_delta_subtracts_the_attributed_total() {
        let previous = Usage {
            input: 10,
            output: 5,
            total_tokens: 15,
            cost: UsageCost {
                total: 0.5,
                ..UsageCost::default()
            },
            ..Usage::default()
        };
        let current = Usage {
            input: 25,
            output: 5,
            reasoning: Some(3),
            total_tokens: 33,
            cost: UsageCost {
                total: 1.25,
                ..UsageCost::default()
            },
            ..Usage::default()
        };
        assert_eq!(
            usage_delta(&current, &previous),
            Usage {
                input: 15,
                reasoning: Some(3),
                total_tokens: 18,
                cost: UsageCost {
                    total: 0.75,
                    ..UsageCost::default()
                },
                ..Usage::default()
            }
        );
        assert_eq!(usage_delta(&previous, &current), Usage::default());
    }
}
