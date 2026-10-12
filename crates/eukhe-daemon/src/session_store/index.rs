//! The index concern (moved with its concern): the entry-chain index
//! maintenance - the push-side `by_id`/`leaf_id` bookkeeping and the live
//! and end-of-load child-usage attribution folds.

use super::{HashMap, SessionEntry, SessionFile, Value};

/// `applyChildUsageAttributions` (TS `core/session-manager.ts`): fold each
/// `child_usage_attributed` entry's `aggregateUsage` into its target
/// assistant row. TS performs this fold on every session read, so the
/// daemon's usage walks — which sum assistant rows — must see the same
/// attributed aggregates the live turn did (`get_session_stats`, the
/// /context own/total split, and the top-bar cost all read folded rows).
/// The last attribution per target wins (each aggregate is cumulative),
/// and a target that never loaded stays untouched. In-memory only: the
/// file keeps the raw row plus the attribution entries, the same view the
/// TS loader serves.
pub(super) fn fold_child_usage_attributions(entries: &mut [SessionEntry]) {
    let mut assistant_rows: HashMap<&str, usize> = HashMap::new();
    for (index, entry) in entries.iter().enumerate() {
        if entry.type_ == "message"
            && entry
                .fields
                .get("message")
                .and_then(|message| message.get("role"))
                .and_then(Value::as_str)
                == Some("assistant")
        {
            assistant_rows.insert(entry.id.as_str(), index);
        }
    }
    let mut folds: Vec<(usize, Value)> = Vec::new();
    for entry in entries.iter() {
        if entry.type_ != "child_usage_attributed" {
            continue;
        }
        let Some(row) = entry
            .fields
            .get("targetId")
            .and_then(Value::as_str)
            .and_then(|id| assistant_rows.get(id))
        else {
            continue;
        };
        // A malformed aggregate (null, a scalar) must not overwrite the
        // row's valid usage with nothing — the typed session reader
        // rejects invalid attribution payloads the same way.
        let Some(aggregate) = entry
            .fields
            .get("aggregateUsage")
            .filter(|aggregate| aggregate.is_object())
        else {
            continue;
        };
        folds.push((*row, aggregate.clone()));
    }
    for (row, aggregate) in folds {
        // TS assigns `target.message.usage = cloneUsage(aggregate)` —
        // assignment, not merge: a row that never carried a `usage` field
        // still gets the aggregate inserted (an assistant row without
        // usage exists in foreign or synthetic files), and a row that
        // carried one is overwritten. Insert-through, exactly like TS.
        if let Some(message) = entries[row].fields.get_mut("message") {
            if let Some(object) = message.as_object_mut() {
                object.insert("usage".to_string(), aggregate);
            }
        }
    }
}

impl SessionFile {
    /// Index one entry as the new leaf. An attribution entry joining the
    /// index folds its aggregate into the target assistant row (TS
    /// `SessionManager.append_child_usage_attribution`'s live fold); the
    /// end-of-load fold re-applies idempotently (the fold SETS the
    /// aggregate) and also catches forward references in foreign files.
    pub(super) fn push_index(&mut self, entry: SessionEntry) {
        if entry.type_ == "child_usage_attributed" {
            self.fold_live_attribution(&entry);
        }
        self.by_id.insert(entry.id.clone(), self.entries.len());
        self.leaf_id = Some(entry.id.clone());
        self.entries.push(entry);
    }

    /// Fold one attribution entry's aggregate into its already-indexed
    /// target assistant row, when the row has joined the index.
    fn fold_live_attribution(&mut self, entry: &SessionEntry) {
        let Some(row) = entry
            .fields
            .get("targetId")
            .and_then(Value::as_str)
            .and_then(|id| self.by_id.get(id).copied())
        else {
            return;
        };
        // A malformed aggregate (null, a scalar) must not overwrite the
        // row's valid usage with nothing — the typed session reader
        // rejects invalid attribution payloads the same way.
        let Some(aggregate) = entry
            .fields
            .get("aggregateUsage")
            .filter(|aggregate| aggregate.is_object())
        else {
            return;
        };
        // TS assigns `target.message.usage = cloneUsage(aggregate)`:
        // insert the aggregate even when the row never carried a `usage`
        // field (the same insert-through as the end-of-load fold).
        if let Some(message) = self.entries[row].fields.get_mut("message") {
            if let Some(object) = message.as_object_mut() {
                object.insert("usage".to_string(), aggregate.clone());
            }
        }
    }
}
