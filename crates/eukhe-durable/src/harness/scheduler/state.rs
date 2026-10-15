//! In-memory scheduler state, guarded by one mutex that is never held across
//! an await.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use indexmap::{IndexMap, IndexSet};

use crate::harness::util::Waiters;
use crate::session::{SessionError, Unsubscribe};
use crate::tasks::{AnyTask, SettledTask};
use crate::types::{AnyTaskRecord, ConversationId, TaskId};

pub(super) use super::contexts::{Expiry, KeptContext};
use super::invocation::Invocation;
use super::ownership::{Links, Node, TaskNode};

/// Definition whose migration failed for one task, and the failure.
#[derive(Clone)]
pub(super) struct FailedMigration {
    pub(super) task: AnyTask,
    pub(super) error: SessionError,
}

/// Every field TS keeps on the `TaskScheduler` instance besides its options.
///
/// The ownership indexes (`edges`, `settled`, `below`, `roots`, `unloaded`)
/// are bounded by live work: an owner edge and an ended task's ownership
/// fields are kept only while something is listed below them in `below`, so
/// only the chains above live tasks are known, whole. Work that appears later
/// below a dropped node finds it unknown and loads its chain from storage
/// again. No pass visits every live task: the candidate sets (`intent`,
/// `runnable`, `finalize_checks`, `fail_fast_checks`) hold each pass's
/// candidates.
#[derive(Default)]
#[expect(
    clippy::struct_excessive_bools,
    reason = "the TS scheduler's independent flags: #enabled, #closing, #dirty, #draining, #reconcileScheduled, #sweepScheduled, #cascadePending"
)]
pub(super) struct State {
    /// Every committed non-terminal task record (pending, running, waiting,
    /// completing), in first-insertion order like a JS `Map`.
    pub(super) live: IndexMap<TaskId, AnyTaskRecord>,
    pub(super) invocations: HashMap<TaskId, Arc<Invocation>>,
    /// Definition whose migration failed per task; retried only once the
    /// registry resolves another definition.
    pub(super) failed_migrations: HashMap<TaskId, FailedMigration>,
    /// Owner task of each known conversation, `None` when ownerless.
    pub(super) edges: HashMap<ConversationId, Option<TaskId>>,
    /// Ownership fields of the known terminal tasks, which walks pass
    /// through.
    pub(super) settled: HashMap<TaskId, TaskNode>,
    /// Ended tasks and conversations found unneeded, dropped by the sweep at
    /// the end of the commit's publication unless needed again by then: a
    /// chain load installs nodes before the work below them is listed.
    pub(super) drop_queue: HashSet<Node>,
    /// The tree downward around live work: each node's child nodes that are
    /// live tasks or have nodes listed below them. A conversation's parent is
    /// its owner task; ownerless ones with work are in `roots`.
    pub(super) below: Links,
    pub(super) roots: HashSet<ConversationId>,
    /// Known tasks whose chain may not be loaded; every other known task's
    /// chain is, and stays, loaded.
    pub(super) unloaded: IndexSet<TaskId>,
    /// Live tasks with cancellation intent, the sources of abort cascades
    /// (spec §5.4).
    pub(super) intent: IndexSet<TaskId>,
    /// Live tasks that are not `completing`, the candidates of a reservation
    /// pass; ones found waiting leave it.
    pub(super) runnable: IndexSet<TaskId>,
    /// `completing` tasks the next finalize pass checks: those that started
    /// holding, and holders of ended work.
    pub(super) finalize_checks: IndexSet<TaskId>,
    /// Live waiting tasks by each task in their `on`.
    pub(super) waiters: HashMap<TaskId, IndexSet<TaskId>>,
    /// `failFast` waiters the next reconcile checks for a failed task in `on`:
    /// at open, when they start waiting, and when one of their tasks fails.
    pub(super) fail_fast_checks: IndexSet<TaskId>,
    /// Live tasks with `abandon_on_restart` found at open, from an earlier
    /// Harness. The first reservation pass abort-marks them with reason
    /// `restart`, so nothing of them or below them runs a phase again.
    pub(super) abandoned: IndexSet<TaskId>,
    pub(super) reconcile_scheduled: bool,
    pub(super) sweep_scheduled: bool,
    pub(super) cascade_pending: bool,
    pub(super) unsubscribe_registry: Option<Unsubscribe>,
    /// The commit and close listeners; Session close removes them.
    pub(super) subscriptions: Vec<Unsubscribe>,
    pub(super) task_waiters: Waiters<TaskId, SettledTask>,
    /// Idle waiters by conversation; `None` waits for the whole Harness.
    pub(super) idle_waiters: Waiters<Option<ConversationId>, ()>,
    pub(super) enabled: bool,
    pub(super) closing: bool,
    pub(super) dirty: bool,
    pub(super) draining: bool,
    /// Context range last read through a task runtime, per conversation: a
    /// later read, by any of its tasks, scans only newer entries. Derived and
    /// never persisted; dropped at the first idle check after
    /// `settings.context_retention_ms` of idleness, and at close.
    pub(super) contexts: HashMap<ConversationId, KeptContext>,
    /// Timer for the earliest expiry of an idle context.
    pub(super) expiry: Option<Expiry>,
}

/// Sizes of the ownership indexes, for tests that bound the scheduler's
/// memory (TS `indexSizes`).
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct IndexSizes {
    pub(crate) live: usize,
    pub(crate) settled: usize,
    pub(crate) edges: usize,
    /// Listed child nodes, summed over every parent.
    pub(crate) below: usize,
    pub(crate) roots: usize,
    pub(crate) unloaded: usize,
    pub(crate) drop_queue: usize,
}
