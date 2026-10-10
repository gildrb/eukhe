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
use super::ownership::TaskNode;

/// Definition whose migration failed for one task, and the failure.
#[derive(Clone)]
pub(super) struct FailedMigration {
    pub(super) task: AnyTask,
    pub(super) error: SessionError,
}

/// Every field TS keeps on the `TaskScheduler` instance besides its options.
#[derive(Default)]
#[expect(
    clippy::struct_excessive_bools,
    reason = "the TS scheduler's independent flags: #enabled, #closing, #dirty, #draining, #reconcileScheduled, #cascadePending"
)]
pub(super) struct State {
    /// Every committed non-terminal task record (pending, running, waiting,
    /// completing), in first-insertion order like a JS `Map`.
    pub(super) live: IndexMap<TaskId, AnyTaskRecord>,
    pub(super) invocations: HashMap<TaskId, Arc<Invocation>>,
    /// Definition whose migration failed per task; retried only once the
    /// registry resolves another definition.
    pub(super) failed_migrations: HashMap<TaskId, FailedMigration>,
    /// Owner task of each loaded conversation, `None` when ownerless.
    pub(super) edges: HashMap<ConversationId, Option<TaskId>>,
    /// Tasks that own a loaded conversation; their nodes stay in `settled`
    /// once terminal.
    pub(super) conversation_owners: HashSet<TaskId>,
    /// Ownership fields of terminal tasks that walks pass through.
    pub(super) settled: HashMap<TaskId, TaskNode>,
    /// `failFast` waiters the next reconcile checks for a failed task in `on`:
    /// at open, when they start waiting, and when one of their tasks fails.
    pub(super) fail_fast_checks: IndexSet<TaskId>,
    /// Live tasks with `abandon_on_restart` found at open, from an earlier
    /// Harness. The first reservation pass abort-marks them with reason
    /// `restart`, so nothing of them or below them runs a phase again.
    pub(super) abandoned: IndexSet<TaskId>,
    pub(super) reconcile_scheduled: bool,
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
