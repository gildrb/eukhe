//! The live task mirror: open reconciliation, the synchronous commit listener,
//! the close seal, and loading of owner chains on the Session line.

use std::sync::Arc;

use eukhe_chord::context::Context;
use indexmap::IndexSet;

use crate::harness::util::{closed_error, scan_all};
use crate::session::{SessionResult, TransactionScope};
use crate::tasks::SettledTask;
use crate::types::{
    AnyTaskRecord, CommitChange, CommitPublication, ConversationId, JoinPolicy, SubmissionQuery,
    SubmissionStatus, SubmissionType, TaskId, TaskQuery, TaskState, TaskStatus,
};

use super::invocation::InvocationMode;
use super::ownership::{
    cancellation_intent, failed_outcome, owner_task, parent_of, Edge, Overlay, TaskNode, Up,
};
use super::state::State;
use super::{Inner, SCAN_PAGE_SIZE};

const LIVE_STATUSES: [TaskStatus; 4] = [
    TaskStatus::Pending,
    TaskStatus::Running,
    TaskStatus::Waiting,
    TaskStatus::Completing,
];

/// Whether loading scopes also loads the chains of conversations with queued
/// submissions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Queued {
    Skip,
    Load,
}

/// Replace a live record's state; memos disappear once an outcome is decided.
pub(super) fn with_state(record: &AnyTaskRecord, state: TaskState) -> AnyTaskRecord {
    let memos = match state {
        TaskState::Pending { .. } | TaskState::Running { .. } | TaskState::Waiting { .. } => {
            record.memos.clone()
        }
        TaskState::Completing { .. } | TaskState::Terminal { .. } => None,
    };
    AnyTaskRecord {
        id: record.id,
        conversation_id: record.conversation_id,
        kind: record.kind.clone(),
        version: record.version,
        input: record.input.clone(),
        owner: record.owner,
        background: record.background,
        abort_requested: record.abort_requested,
        state,
        memos,
    }
}

/// The record with its abort mark set.
pub(super) fn marked(record: &AnyTaskRecord) -> AnyTaskRecord {
    AnyTaskRecord {
        abort_requested: true,
        ..record.clone()
    }
}

/// The record's checkpoint; `null` for a record that holds an outcome.
pub(super) fn checkpoint_of(record: &AnyTaskRecord) -> eukhe_chord::json::JsonValue {
    record.state.checkpoint().cloned().unwrap_or_default()
}

impl Inner {
    pub(super) async fn open(&self, cx: &Context) -> SessionResult<()> {
        let this = Arc::downgrade(&self.arc());
        let commits = self.session.subscribe_commits(Arc::new({
            let this = this.clone();
            move |publication, _| {
                if let Some(inner) = this.upgrade() {
                    inner.observe(publication);
                }
            }
        }))?;
        let close = self.session.subscribe_close(Arc::new({
            let this = this.clone();
            move || {
                if let Some(inner) = this.upgrade() {
                    inner.seal();
                }
            }
        }))?;
        let registry = self.registry.subscribe(Arc::new(move || {
            if let Some(inner) = this.upgrade() {
                inner.kick();
            }
        }));
        {
            let mut state = self.lock();
            state.subscriptions.extend([commits, close]);
            state.unsubscribe_registry = Some(registry);
        }
        let inner = self.arc();
        self.session
            .commit_with(
                move |tx| async move {
                    // Every table read before the first write.
                    let mut scans = Vec::new();
                    for status in LIVE_STATUSES {
                        let query = TaskQuery {
                            status: Some(status),
                            ..TaskQuery::default()
                        };
                        scans.push(
                            scan_all(|cursor| tx.scan_tasks(query.clone(), SCAN_PAGE_SIZE, cursor))
                                .await?,
                        );
                    }
                    for records in scans {
                        for record in records {
                            let mut state = inner.lock();
                            state.live.insert(record.id, record.clone());
                            match &record.state {
                                TaskState::Running { checkpoint } => {
                                    let checkpoint = checkpoint.clone();
                                    drop(state);
                                    tx.set_task(with_state(
                                        &record,
                                        TaskState::Pending { checkpoint },
                                    ))?;
                                }
                                TaskState::Waiting { policy, .. } => {
                                    if *policy == JoinPolicy::FailFast {
                                        state.fail_fast_checks.insert(record.id);
                                    }
                                }
                                TaskState::Pending { .. }
                                | TaskState::Completing { .. }
                                | TaskState::Terminal { .. } => {}
                            }
                        }
                    }
                    Ok(())
                },
                cx,
                TransactionScope::default(),
            )
            .await?;
        // Derive abort marks a crash left unapplied below cancelled owners, and
        // finalize held outcomes.
        self.lock().cascade_pending = true;
        self.schedule_reconcile();
        Ok(())
    }

    /// The commit listener: mirror every task change, then wake whatever the
    /// changes affect.
    pub(super) fn observe(&self, publication: &CommitPublication) {
        let observed = {
            let mut state = self.lock();
            let mut observed = Observed::default();
            for change in &publication.changes {
                if let CommitChange::Task(record) = change {
                    state.mirror_task(record, &mut observed);
                }
            }
            state.observe_scopes(publication, &mut observed);
            observed
        };
        if observed.reconcile {
            self.schedule_reconcile();
        }
        if !observed.changed {
            return;
        }
        self.resolve_idle_waiters();
        self.kick();
    }

    pub(super) fn resolve_idle_waiters(&self) {
        let state = self.lock();
        for conversation_id in state.idle_waiters.keys() {
            if state.idle(conversation_id) {
                state.idle_waiters.resolve(&conversation_id, &());
            }
        }
    }

    /// Close listener: runs synchronously once admission is sealed, before
    /// `join()`.
    pub(super) fn seal(&self) {
        let (unsubscribe, invocations) = {
            let mut state = self.lock();
            state.closing = true;
            let unsubscribe = state.unsubscribe_registry.take();
            state.task_waiters.reject_all(&closed_error());
            state.idle_waiters.reject_all(&closed_error());
            let invocations: Vec<_> = state.invocations.values().cloned().collect();
            (unsubscribe, invocations)
        };
        if let Some(unsubscribe) = unsubscribe {
            unsubscribe.unsubscribe();
        }
        for invocation in invocations {
            invocation.controller.abort(None);
        }
    }

    /// Load the owner chains of every live task and, with `Queued::Load`, of
    /// every conversation with queued submissions, on the Session line;
    /// returns the latter. Reads committed Storage directly, so it may run
    /// inside a commit callback.
    pub(super) async fn load_scopes(&self, queued: Queued) -> SessionResult<Vec<ConversationId>> {
        let parents: Vec<Up> = self.lock().live.values().map(parent_of).collect();
        for parent in parents {
            if !self.lock().chain_known(parent, None) {
                self.load_chain(parent, None).await?;
            }
        }
        if queued == Queued::Skip {
            return Ok(Vec::new());
        }
        let query = SubmissionQuery {
            status: Some(SubmissionStatus::Queued),
            ..SubmissionQuery::default()
        };
        let submissions = scan_all(|cursor| {
            let storage = Arc::clone(&self.storage);
            let cx = self.context.clone();
            async move {
                Ok(storage
                    .scan_submissions(&query, SCAN_PAGE_SIZE, cursor.as_ref(), &cx)
                    .await?)
            }
        })
        .await?;
        let conversations: IndexSet<ConversationId> = submissions
            .iter()
            .map(|submission| submission.conversation_id)
            .collect();
        for id in &conversations {
            self.load_chain(Up::Conversation(*id), None).await?;
        }
        Ok(conversations.into_iter().collect())
    }

    /// Load the owner edges and task nodes from `start` up to its ownerless root.
    pub(super) async fn load_chain(
        &self,
        start: Up,
        overlay: Option<&Overlay>,
    ) -> SessionResult<()> {
        let mut at = Some(start);
        while let Some(up) = at {
            match up {
                Up::Task(id) => {
                    let known = self.lock().node(id, overlay);
                    let node = if let Some(node) = known {
                        node
                    } else {
                        let Some(record) = self.storage.task(id, &self.context).await? else {
                            return Ok(());
                        };
                        let node = TaskNode::of(&record);
                        if record.state.status() == TaskStatus::Terminal {
                            self.lock().settled.insert(record.id, node);
                        }
                        node
                    };
                    at = Some(node.parent());
                }
                Up::Conversation(id) => {
                    let known = self.lock().edge(id, overlay);
                    let owner = match known {
                        Edge::Loaded(owner) => owner,
                        Edge::Unloaded => {
                            let record = self.storage.conversation(id, &self.context).await?;
                            let owner = record.and_then(|record| owner_task(record.owner.as_ref()));
                            self.lock().set_edge(id, owner);
                            owner
                        }
                    };
                    at = owner.map(Up::Task);
                }
            }
        }
        Ok(())
    }
}

/// What one publication changed in the mirror.
#[derive(Default)]
struct Observed {
    /// A task record changed.
    changed: bool,
    reconcile: bool,
    /// Live records the publication replaced.
    updated: Vec<TaskId>,
    /// Tasks that now hold or ended with an outcome other than `completed`.
    failed: Vec<TaskId>,
}

impl State {
    /// Mirror one committed task record.
    fn mirror_task(&mut self, record: &AnyTaskRecord, observed: &mut Observed) {
        observed.changed = true;
        let previous = self.live.get(&record.id);
        let previous_marked = previous.is_some_and(|previous| previous.abort_requested);
        let previous_status = previous.map(|previous| previous.state.status());
        if failed_outcome(record) && !previous.is_some_and(failed_outcome) {
            observed.failed.push(record.id);
        }
        if record.state.status() == TaskStatus::Terminal {
            self.live.shift_remove(&record.id);
            self.failed_migrations.remove(&record.id);
            self.fail_fast_checks.shift_remove(&record.id);
            if self.conversation_owners.contains(&record.id) {
                self.settled.insert(record.id, TaskNode::of(record));
            }
            if let Some(settled) = SettledTask::from_record(record.clone()) {
                self.task_waiters.resolve(&record.id, &settled);
            }
            // Its owner may finalize now.
            observed.reconcile = true;
            return;
        }
        if record.abort_requested && !previous_marked {
            self.cascade_pending = true;
            // Signal a run invocation of the newly marked task; its next step ends it.
            if let Some(invocation) = self.invocations.get(&record.id) {
                if invocation.mode == InvocationMode::Run {
                    invocation.controller.abort(None);
                }
            }
        }
        match &record.state {
            TaskState::Completing { .. } => {
                if previous_status != Some(TaskStatus::Completing) {
                    if cancellation_intent(record) {
                        self.cascade_pending = true;
                    }
                    observed.reconcile = true;
                }
            }
            TaskState::Waiting { policy, .. } => {
                if *policy == JoinPolicy::FailFast && previous_status != Some(TaskStatus::Waiting) {
                    self.fail_fast_checks.insert(record.id);
                    observed.reconcile = true;
                }
            }
            TaskState::Pending { .. } | TaskState::Running { .. } | TaskState::Terminal { .. } => {}
        }
        self.live.insert(record.id, record.clone());
        observed.updated.push(record.id);
    }

    /// After the task changes: `failFast` checks, new owner edges, and
    /// cascades owed to queued inputs and new work below cancelled owners.
    fn observe_scopes(&mut self, publication: &CommitPublication, observed: &mut Observed) {
        for id in &observed.failed {
            let waiters: Vec<TaskId> = self
                .live
                .values()
                .filter(|record| match &record.state {
                    TaskState::Waiting { policy, on, .. } => {
                        *policy == JoinPolicy::FailFast && on.contains(id)
                    }
                    TaskState::Pending { .. }
                    | TaskState::Running { .. }
                    | TaskState::Completing { .. }
                    | TaskState::Terminal { .. } => false,
                })
                .map(|record| record.id)
                .collect();
            for waiter in waiters {
                self.fail_fast_checks.insert(waiter);
                observed.reconcile = true;
            }
        }
        for change in &publication.changes {
            if let CommitChange::Conversation(conversation) = change {
                if !self.edges.contains_key(&conversation.id) {
                    self.set_edge(conversation.id, owner_task(conversation.owner.as_ref()));
                }
            }
        }
        for change in &publication.changes {
            // A queued input below a cancelled owner is withdrawn, even after its cascade.
            let CommitChange::Submission(submission) = change else {
                continue;
            };
            if submission.state.status() != SubmissionStatus::Queued
                || submission.state.submission_type() != SubmissionType::Input
            {
                continue;
            }
            let up = Up::Conversation(submission.conversation_id);
            if !self.chain_known(up, None) || self.below_cancelled(up) {
                self.cascade_pending = true;
            }
        }
        for id in &observed.updated {
            // Work created below a cancelled owner, even after its cascade, is aborted too.
            let Some(record) = self.live.get(id) else {
                continue;
            };
            let parent = parent_of(record);
            if !self.chain_known(parent, None) {
                observed.reconcile = true;
            } else if !record.background && !record.abort_requested && self.below_cancelled(parent)
            {
                self.cascade_pending = true;
            }
        }
        // Also retries, with the next commit of any kind, a cascade whose commit failed.
        if self.cascade_pending {
            observed.reconcile = true;
        }
    }
}
