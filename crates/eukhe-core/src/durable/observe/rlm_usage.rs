//! RLM child-usage attribution rows (the durable form of the old engine's
//! `child_usage_attributed` session rows): one display-only entry per
//! attributed batch, naming the spawning parent assistant row and the
//! cumulative aggregate, plus the read-side fold that restores the old
//! `applyChildUsageAttributions` view (the newest aggregate per target
//! replaces the target row's usage; totals keep the row's own context
//! size).
//!
//! Durable entries are immutable, so the fold the old engine performed at
//! append time (rewriting the assistant row in the session file) becomes a
//! fold at read: [`apply_child_usage_attributions`] over the entries a
//! surface is about to render. The parent's billable session totals are
//! unaffected — they come from the `pi.usage` attribution the children
//! registry bills in the same commit.

use eukhe_chord::json::{from_json, to_json};
use eukhe_durable::harness::usage::add_usage;
use eukhe_durable::types::{EntryDraft, EntryId, EntryRecord};
use eukhe_types::pi_ai::{AssistantMessage, Message, Usage};
use eukhe_types::session::ChildUsageOrigin;
use serde::{Deserialize, Serialize};

/// The entry kind of one attribution row.
pub const CHILD_USAGE_ATTRIBUTED_KIND: &str = "eukhe.child-usage-attributed";

/// The data of one `eukhe.child-usage-attributed` entry: the old JSONL
/// row's payload over the durable entry id (a number).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ChildUsageAttributionData {
    /// The parent assistant entry the batch attributes to.
    pub target_id: EntryId,
    /// The usage attributed by this batch alone.
    pub child_usage: Usage,
    /// Cumulative: the target row's own usage plus every batch attributed
    /// to it; `totalTokens` stays at the row's own context size.
    pub aggregate_usage: Usage,
    /// Which parent surface the child's spend belonged to; `None` on the
    /// durable path (the child host reports one cumulative total, not
    /// per-origin batches like the old engine's child-file walk).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub origin: Option<ChildUsageOrigin>,
}

/// The display-only entry of one attribution batch.
///
/// # Errors
///
/// The data does not serialize to JSON (never for these field types).
pub fn attribution_draft(
    target_id: EntryId,
    child_usage: &Usage,
    aggregate_usage: &Usage,
) -> Result<EntryDraft, eukhe_chord::json::JsonError> {
    Ok(EntryDraft {
        kind: CHILD_USAGE_ATTRIBUTED_KIND.to_owned(),
        model: None,
        data: Some(to_json(&ChildUsageAttributionData {
            target_id,
            child_usage: *child_usage,
            aggregate_usage: *aggregate_usage,
            origin: None,
        })?),
        head: None,
        edits: None,
    })
}

/// The cumulative aggregate after attributing `delta` onto `base` (the
/// target row's running aggregate, or its own usage before the first
/// batch): fields and cost sum, `total_tokens` stays the parent row's own
/// context size — child work affects billable totals, not the parent's
/// model-facing context.
#[must_use]
pub fn attributed_aggregate(base: &Usage, delta: &Usage, parent_context_tokens: u64) -> Usage {
    let mut aggregate = *base;
    add_usage(&mut aggregate, delta);
    aggregate.total_tokens = parent_context_tokens;
    aggregate
}

/// The first assistant message an entry contributes, when it is one (the
/// old `_findLastAssistantMessage` had no stop-reason filter).
fn assistant_of(entry: &EntryRecord) -> Option<&AssistantMessage> {
    let messages = entry.model.as_ref()?;
    messages.iter().find_map(|message| match message {
        Message::Assistant(assistant) => Some(assistant),
        _ => None,
    })
}

/// The usage of the first assistant message an entry contributes (the
/// attribution target's own usage); `None` when the entry is not an
/// assistant row.
pub(crate) fn entry_assistant_usage(entry: &EntryRecord) -> Option<Usage> {
    assistant_of(entry).map(|assistant| assistant.usage)
}

/// The read-side fold (the old `applyChildUsageAttributions`): the newest
/// `aggregateUsage` per target replaces the target assistant entry's
/// usage; aggregates are cumulative, so they are never summed. `entries`
/// arrive in storage scan order (newest first), so the FIRST row per
/// target is its newest. Rows with undecodable data or a missing target
/// are skipped — an attribution never fails the read it rides.
pub fn apply_child_usage_attributions(entries: &mut [EntryRecord]) {
    let mut newest: std::collections::HashMap<EntryId, Usage> = std::collections::HashMap::new();
    for entry in entries.iter() {
        if entry.kind != CHILD_USAGE_ATTRIBUTED_KIND {
            continue;
        }
        let Some(data) = entry.data.as_ref() else {
            continue;
        };
        if let Ok(attribution) = from_json::<ChildUsageAttributionData>(data) {
            newest
                .entry(attribution.target_id)
                .or_insert(attribution.aggregate_usage);
        }
    }
    if newest.is_empty() {
        return;
    }
    for entry in entries.iter_mut() {
        let Some(aggregate) = newest.get(&entry.id) else {
            continue;
        };
        let Some(messages) = entry.model.as_mut() else {
            continue;
        };
        for message in messages.iter_mut() {
            if let Message::Assistant(assistant) = message {
                assistant.usage = *aggregate;
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_chord::json::JsonValue;
    use eukhe_durable::types::ConversationId;
    use eukhe_types::pi_ai::{StopReason, UsageCost};

    fn usage(input: u64, output: u64, total_tokens: u64) -> Usage {
        Usage {
            input,
            output,
            cache_read: 0,
            cache_write: 0,
            cache_write_1h: None,
            reasoning: None,
            total_tokens,
            cost: UsageCost {
                input: 0.0,
                output: 0.0,
                cache_read: 0.0,
                cache_write: 0.0,
                total: 0.0,
            },
        }
    }

    fn assistant_entry(id: u64, own: Usage) -> EntryRecord {
        EntryRecord {
            model: Some(vec![Message::Assistant(AssistantMessage {
                content: Vec::new(),
                api: "faux".to_owned(),
                provider: "faux".to_owned(),
                model: "faux-1".to_owned(),
                response_model: None,
                response_id: None,
                provider_thinking_level: None,
                thinking_level: None,
                diagnostics: None,
                usage: own,
                stop_reason: StopReason::Stop,
                deferred: None,
                error_message: None,
                raw_stop_reason: None,
                end_turn: None,
                timestamp: 0,
            })]),
            data: None,
            edits: None,
            kind: "pi.message".to_owned(),
            id: EntryId::from_number(id),
            conversation_id: ConversationId::from_number(1),
            head: None,
            by_task_id: None,
        }
    }

    fn attribution_entry(id: u64, target: u64, aggregate: Usage) -> EntryRecord {
        let data = to_json(&ChildUsageAttributionData {
            target_id: EntryId::from_number(target),
            child_usage: usage(1, 1, 2),
            aggregate_usage: aggregate,
            origin: None,
        })
        .unwrap();
        EntryRecord {
            model: None,
            data: Some(data),
            edits: None,
            kind: CHILD_USAGE_ATTRIBUTED_KIND.to_owned(),
            id: EntryId::from_number(id),
            conversation_id: ConversationId::from_number(1),
            head: None,
            by_task_id: None,
        }
    }

    fn assistant_usage_of(entries: &[EntryRecord], id: u64) -> Usage {
        entries
            .iter()
            .find(|entry| entry.id == EntryId::from_number(id))
            .and_then(assistant_of)
            .unwrap()
            .usage
    }

    #[test]
    fn aggregate_sums_fields_and_keeps_parent_context_tokens() {
        let base = usage(1_000, 200, 1_200);
        let delta = usage(100, 50, 150);
        let aggregate = attributed_aggregate(&base, &delta, 1_200);
        assert_eq!(aggregate.input, 1_100);
        assert_eq!(aggregate.output, 250);
        assert_eq!(aggregate.total_tokens, 1_200);
    }

    #[test]
    fn fold_replaces_with_the_newest_aggregate_per_target() {
        // Storage scan order: newest first.
        let mut entries = vec![
            attribution_entry(12, 10, usage(1_500, 30, 1_000)),
            attribution_entry(11, 10, usage(1_100, 10, 1_000)),
            assistant_entry(10, usage(1_000, 0, 1_000)),
        ];
        apply_child_usage_attributions(&mut entries);
        assert_eq!(assistant_usage_of(&entries, 10), usage(1_500, 30, 1_000));
    }

    #[test]
    fn fold_skips_undecodable_data_and_missing_targets() {
        let mut torn = attribution_entry(11, 10, usage(1, 1, 1));
        torn.data = Some(JsonValue::from("torn"));
        let mut entries = vec![
            assistant_entry(10, usage(1_000, 0, 1_000)),
            torn,
            attribution_entry(12, 999, usage(7, 7, 7)),
        ];
        apply_child_usage_attributions(&mut entries);
        assert_eq!(assistant_usage_of(&entries, 10), usage(1_000, 0, 1_000));
    }

    #[test]
    fn draft_round_trips_the_old_row_payload() {
        let draft = attribution_draft(
            EntryId::from_number(10),
            &usage(100, 20, 120),
            &usage(1_100, 220, 1_200),
        )
        .unwrap();
        assert_eq!(draft.kind, CHILD_USAGE_ATTRIBUTED_KIND);
        assert!(draft.model.is_none());
        let data = from_json::<ChildUsageAttributionData>(draft.data.as_ref().unwrap()).unwrap();
        assert_eq!(
            data,
            ChildUsageAttributionData {
                target_id: EntryId::from_number(10),
                child_usage: usage(100, 20, 120),
                aggregate_usage: usage(1_100, 220, 1_200),
                origin: None,
            }
        );
        // The old row's camelCase wire names ride the durable entry.
        assert_eq!(
            draft.data.as_ref().unwrap()["targetId"],
            to_json(&10_u64).unwrap()
        );
        assert!(draft.data.as_ref().unwrap()["aggregateUsage"]["totalTokens"].is_number());
    }
}
