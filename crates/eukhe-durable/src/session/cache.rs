//! The Session's loaded document cache, bounded by use (TS `SessionImpl`
//! `#documents`, `#idleDocuments`, `#attachedDocuments`, `#documentSweep`).
//!
//! A document with no watch or document state attached leaves the cache once
//! it was not read or written for the retention period; the next access loads
//! it from Storage. The Session evicts only on its mutation line, so no
//! transaction ever holds a tracker that leaves.

use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use super::transaction::LoadedDocument;
use crate::types::DocumentId;

/// Default document retention: ten minutes, as for kept contexts.
const DEFAULT_DOCUMENT_RETENTION_MS: f64 = 600_000.0;

/// A retention as given, when it is a number of milliseconds, `0` or more
/// (`f64::INFINITY` keeps documents); otherwise the default.
#[must_use]
pub fn document_retention(ms: Option<f64>) -> f64 {
    match ms {
        Some(ms) if ms >= 0.0 => ms,
        _ => DEFAULT_DOCUMENT_RETENTION_MS,
    }
}

/// Internal, for tests: how many documents the cache holds, how many are
/// idle, and how many incarnations are pinned by attached observers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DocumentCacheSizes {
    pub cached: usize,
    pub idle: usize,
    pub attached: usize,
}

/// The pending eviction: a timer for the oldest idle document, or a line job
/// when it already expired. It stays set until its job runs, so touches while
/// the line is busy queue no more.
pub(super) struct PendingSweep {
    /// The Session time it evicts at.
    pub(super) at: f64,
    /// Identity of this sweep; a job runs only for the pending one.
    pub(super) id: u64,
    /// The timer that enqueues the job; `None` when the job was enqueued at
    /// once.
    pub(super) timer: Option<tokio::task::JoinHandle<()>>,
}

/// One idle document: its address and the time of its last use.
struct IdleUse {
    address_id: String,
    since: f64,
}

#[derive(Default)]
pub(super) struct DocumentCache {
    documents: HashMap<String, Arc<LoadedDocument>>,
    /// Cached documents with no observer attached, by address, with the
    /// place of their last use in `idle_order`.
    idle: HashMap<String, u64>,
    /// The last use of every idle document, oldest first.
    idle_order: BTreeMap<u64, IdleUse>,
    next_order: u64,
    /// Observers attached per document incarnation (record ID); a cached
    /// incarnation with any is never evicted.
    attached: HashMap<DocumentId, usize>,
    sweep: Option<PendingSweep>,
    next_sweep: u64,
}

impl DocumentCache {
    pub(super) fn get(&self, address_id: &str) -> Option<&Arc<LoadedDocument>> {
        self.documents.get(address_id)
    }

    /// Cache a loaded or newly committed incarnation; the caller then touches
    /// it.
    pub(super) fn insert(&mut self, document: Arc<LoadedDocument>) {
        self.documents.insert(document.address_id.clone(), document);
    }

    pub(super) fn drop_document(&mut self, address_id: &str) {
        self.documents.remove(address_id);
        self.forget_idle(address_id);
    }

    /// Drop every loaded tracker; attached observers stay counted.
    pub(super) fn unload(&mut self) {
        self.documents.clear();
        self.idle.clear();
        self.idle_order.clear();
    }

    /// Drop every tracker and pin at close.
    pub(super) fn close(&mut self) {
        self.unload();
        self.attached.clear();
    }

    /// Drop the pending sweep, stopping its timer.
    pub(super) fn stop_sweep(&mut self) {
        if let Some(timer) = self.sweep.take().and_then(|sweep| sweep.timer) {
            timer.abort();
        }
    }

    pub(super) fn sizes(&self) -> DocumentCacheSizes {
        DocumentCacheSizes {
            cached: self.documents.len(),
            idle: self.idle.len(),
            attached: self.attached.len(),
        }
    }

    /// Whether a use of `address_id` would make it idle: it is cached and no
    /// observer pins it.
    pub(super) fn idle_candidate(&self, address_id: &str) -> bool {
        self.documents
            .get(address_id)
            .is_some_and(|cached| !self.attached.contains_key(&cached.record.id))
    }

    /// Note a use of a cached document at `now`: an unattached one becomes
    /// the newest idle one. Returns whether an eviction should be scheduled.
    pub(super) fn touch(&mut self, address_id: &str, now: f64, retention: f64) -> bool {
        let Some(cached) = self.documents.get(address_id) else {
            return false;
        };
        if self.attached.contains_key(&cached.record.id) {
            return false;
        }
        // A hot document moves to the back at most once per granule, a tenth
        // of the retention up to 1 s: it may then leave up to a granule early,
        // which costs a reload, while a commit-heavy workload skips the
        // reordering.
        if let Some(previous) = self.idle.get(address_id) {
            let since = self.idle_order.get(previous).map(|idle| idle.since);
            if since.is_some_and(|since| now - since < f64::min(1_000.0, retention / 10.0)) {
                return false;
            }
            self.idle_order.remove(previous);
        }
        let order = self.next_order;
        self.next_order += 1;
        self.idle.insert(address_id.to_owned(), order);
        self.idle_order.insert(
            order,
            IdleUse {
                address_id: address_id.to_owned(),
                since: now,
            },
        );
        // A pending sweep for the oldest document comes first unless the
        // retention was shortened since; then it moves up.
        self.sweep
            .as_ref()
            .is_none_or(|sweep| sweep.at > now + retention)
    }

    /// When the oldest idle document expires, unless a pending sweep already
    /// runs by then.
    pub(super) fn next_sweep_at(&self, retention: f64) -> Option<f64> {
        let at = self.idle_order.values().next()?.since + retention;
        if self.sweep.as_ref().is_some_and(|sweep| sweep.at <= at) {
            return None;
        }
        Some(at)
    }

    /// A fresh sweep identity.
    pub(super) fn next_sweep_id(&mut self) -> u64 {
        let id = self.next_sweep;
        self.next_sweep += 1;
        id
    }

    /// Replace the pending sweep, stopping the old one's timer.
    pub(super) fn replace_sweep(&mut self, sweep: PendingSweep) {
        self.stop_sweep();
        self.sweep = Some(sweep);
    }

    /// Clear the pending sweep if it is still `id`.
    pub(super) fn finish_sweep(&mut self, id: u64) {
        if self.sweep.as_ref().is_some_and(|sweep| sweep.id == id) {
            self.sweep = None;
        }
    }

    /// Evict the idle documents last used at `expired` or before, oldest
    /// first.
    pub(super) fn expire(&mut self, expired: f64) {
        while let Some(entry) = self.idle_order.first_entry() {
            if entry.get().since > expired {
                break;
            }
            let IdleUse { address_id, .. } = entry.remove();
            self.idle.remove(&address_id);
            self.documents.remove(&address_id);
        }
    }

    /// Pin a cached incarnation for one observer.
    pub(super) fn pin(&mut self, address_id: &str, record_id: DocumentId) {
        *self.attached.entry(record_id).or_insert(0) += 1;
        self.forget_idle(address_id);
    }

    /// Release one observer's pin; returns whether the incarnation is now
    /// unpinned and still the cached occupant of its address, so idle again.
    pub(super) fn unpin(&mut self, address_id: &str, record_id: DocumentId) -> bool {
        let Some(count) = self.attached.get_mut(&record_id) else {
            return false;
        };
        *count -= 1;
        if *count > 0 {
            return false;
        }
        self.attached.remove(&record_id);
        self.documents
            .get(address_id)
            .is_some_and(|cached| cached.record.id == record_id)
    }

    fn forget_idle(&mut self, address_id: &str) {
        if let Some(order) = self.idle.remove(address_id) {
            self.idle_order.remove(&order);
        }
    }
}
