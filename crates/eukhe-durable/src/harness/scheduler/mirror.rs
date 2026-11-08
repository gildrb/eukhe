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
use super::life;
use super::ownership::{
    cancellation_intent, failed_outcome, owner_task, parent_of, Edge, Node, Overlay, TaskNode,
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
        abort_reason: record.abort_reason,
        abandon_on_restart: record.abandon_on_restart,
        state,
        memos,
        started_at: record.started_at,
        ended_at: record.ended_at,
    }
}

/// The record's checkpoint; `null` for a record that holds an outcome.
pub(super) fn checkpoint_of(record: &AnyTaskRecord) -> eukhe_chord::json::JsonValue {
    record.state.checkpoint().cloned().unwrap_or_default()
}

impl Inner {
    pub(super) async fn open(&self, cx: &Context) -> SessionResult<()> {
        let this = Arc::downgrade(&self.arc());
        let commits = self.session.observe_commits(Arc::new({
            let this = this.clone();
            move |publication, _| {
                if let Some(inner) = this.upgrade() {
                    inner.observe(publication);
                }
                Ok(())
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
                            state.track(&record);
                            if record.abandon_on_restart {
                                state.abandoned.insert(record.id);
                            }
                            // A new Harness resumes each stored state as the
                            // task-life rules decide (`life::resume`).
                            let resumed = life::resume(&record)?;
                            if resumed.check_fail_fast {
                                state.fail_fast_checks.insert(record.id);
                            }
                            drop(state);
                            if resumed.state.status() != record.state.status() {
                                tx.set_task(with_state(&record, resumed.state))?;
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
        let observed = self.lock().observe(publication);
        if observed.reconcile {
            self.schedule_reconcile();
        }
        if !observed.changed {
            return;
        }
        self.settle_idle();
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
    /// `join()`, or when the Session fails.
    pub(super) fn seal(&self) {
        let error = closed_error(&self.session);
        let unsubscribe = {
            let mut state = self.lock();
            state.closing = true;
            let unsubscribe = state.unsubscribe_registry.take();
            state.task_waiters.reject_all(&error);
            state.idle_waiters.reject_all(&error);
            state.contexts.clear();
            if let Some(expiry) = state.expiry.take() {
                expiry.timer.abort();
            }
            unsubscribe
        };
        if let Some(unsubscribe) = unsubscribe {
            unsubscribe.unsubscribe();
        }
    }

    /// Load the owner chains of the tasks in `unloaded` and, with
    /// `Queued::Load`, of every conversation with queued inputs, on the
    /// Session line; returns the latter. Reads committed Storage directly, so
    /// it may run inside a commit callback.
    pub(super) async fn load_scopes(&self, queued: Queued) -> SessionResult<Vec<ConversationId>> {
        let unloaded: Vec<TaskId> = self.lock().unloaded.iter().copied().collect();
        for id in unloaded {
            // An earlier load in this loop may have passed it.
            if self.lock().unloaded.contains(&id) {
                self.load_chain(Node::Task(id), None).await?;
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
            .filter(|submission| submission.state.submission_type() == SubmissionType::Input)
            .map(|submission| submission.conversation_id)
            .collect();
        for id in &conversations {
            self.load_chain(Node::Conversation(*id), None).await?;
        }
        Ok(conversations.into_iter().collect())
    }

    /// Load the owner edges and task nodes from `start` up to its ownerless
    /// root. A known task outside `unloaded` ends the walk, as its chain is
    /// loaded; the `unloaded` tasks passed have a loaded chain afterwards.
    /// Loading a node can reveal a cancelled owner, so it makes the next
    /// reconcile derive cascade marks.
    pub(super) async fn load_chain(
        &self,
        start: Node,
        overlay: Option<&Overlay>,
    ) -> SessionResult<()> {
        let mut passed = Vec::new();
        let mut at = Some(start);
        while let Some(node) = at {
            match node {
                Node::Task(id) => {
                    let (known, unloaded) = {
                        let state = self.lock();
                        (state.known_node(id), state.unloaded.contains(&id))
                    };
                    let node = match known {
                        Some(_) if !unloaded => break,
                        Some(node) => node,
                        // Created in this commit: the load from its own record
                        // covers what is above it.
                        None if overlay.is_some_and(|overlay| overlay.tasks.contains_key(&id)) => {
                            break;
                        }
                        None => {
                            let Some(record) = self.storage.task(id, &self.context).await? else {
                                return Ok(());
                            };
                            let node = TaskNode::of(&record);
                            if record.state.status() == TaskStatus::Terminal {
                                // Known, so walks pass through it; its own
                                // chain is not loaded yet.
                                let mut state = self.lock();
                                state.settled.insert(id, node);
                                state.unloaded.insert(id);
                                state.relist(Node::Task(id));
                                state.drop_if_unneeded(Node::Task(id));
                            }
                            // A loaded node can reveal a cancelling owner: the
                            // next reconcile derives marks again.
                            self.schedule_reconcile();
                            node
                        }
                    };
                    passed.push(id);
                    at = Some(node.parent());
                }
                Node::Conversation(id) => {
                    let known = self.lock().edge(id, overlay);
                    let owner = match known {
                        Edge::Loaded(owner) => owner,
                        Edge::Unloaded => {
                            let record = self.storage.conversation(id, &self.context).await?;
                            let owner = record.and_then(|record| owner_task(record.owner.as_ref()));
                            self.lock().set_edge(id, owner);
                            // A loaded node can reveal a cancelling owner: the
                            // next reconcile derives marks again.
                            self.schedule_reconcile();
                            owner
                        }
                    };
                    at = owner.map(Node::Task);
                }
            }
        }
        {
            let mut state = self.lock();
            for id in passed {
                state.unloaded.shift_remove(&id);
            }
            // Sweep what the load left unneeded in a job of its own on the
            // Session line, after the operation underway: a rejected commit,
            // one with nothing to write, and a read publish nothing, so the
            // sweep at the end of `observe` would not run for it.
            if state.drop_queue.is_empty() || state.sweep_scheduled || state.closing {
                return Ok(());
            }
            state.sweep_scheduled = true;
        }
        let inner = self.arc();
        // Enqueued now; rejected only once the Session is closing or failed,
        // when nothing is kept anyway.
        drop(self.session.read_on_line(async move {
            let mut state = inner.lock();
            state.sweep_scheduled = false;
            state.sweep();
            Ok(())
        }));
        Ok(())
    }
}

/// What one publication changed in the mirror, and what its task changes
/// owe.
#[derive(Default)]
struct Observed<'a> {
    /// A task record changed.
    changed: bool,
    reconcile: bool,
    /// Tasks that now hold or ended with an outcome other than `completed`.
    failed: Vec<TaskId>,
    /// Records that became live.
    updated: Vec<&'a AnyTaskRecord>,
}

impl State {
    /// Mirror every task change of a publication, then note what the changes
    /// owe. Sweeps once all is tracked.
    fn observe<'a>(&mut self, publication: &'a CommitPublication) -> Observed<'a> {
        let mut observed = Observed::default();
        // Edges first, so the tasks a commit creates in a new conversation
        // hang from it.
        for change in &publication.changes {
            if let CommitChange::Conversation(conversation) = change {
                if !self.edges.contains_key(&conversation.id) {
                    self.set_edge(conversation.id, owner_task(conversation.owner.as_ref()));
                }
            }
        }
        for change in &publication.changes {
            if let CommitChange::Task(record) = change {
                self.mirror_task(record, &mut observed);
            }
        }
        self.observe_scopes(publication, &mut observed);
        self.sweep();
        observed
    }

    /// Mirror one committed task record.
    fn mirror_task<'a>(&mut self, record: &'a AnyTaskRecord, observed: &mut Observed<'a>) {
        observed.changed = true;
        let previous = self.track(record);
        if failed_outcome(record) && !previous.as_ref().is_some_and(failed_outcome) {
            observed.failed.push(record.id);
        }
        if record.state.status() == TaskStatus::Terminal {
            self.failed_migrations.remove(&record.id);
            self.fail_fast_checks.shift_remove(&record.id);
            if let Some(settled) = SettledTask::from_record(record.clone()) {
                self.task_waiters.resolve(&record.id, &settled);
            }
            // Its owner may finalize now.
            observed.reconcile = true;
            return;
        }
        if record.abort_requested
            && !previous
                .as_ref()
                .is_some_and(|previous| previous.abort_requested)
        {
            self.cascade_pending = true;
            // Signal a run invocation of the newly marked task; its next step ends it.
            if let Some(invocation) = self.invocations.get(&record.id) {
                if invocation.mode == InvocationMode::Run {
                    invocation.controller.abort(None);
                }
            }
        }
        // A request replacing a `restart` mark upgrades the marks of the work below.
        if previous
            .as_ref()
            .is_some_and(|previous| previous.abort_reason.is_some())
            && record.abort_reason.is_none()
        {
            self.cascade_pending = true;
        }
        let previous_status = previous.as_ref().map(|previous| previous.state.status());
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
        // Its owners and place never change: what is above it is checked
        // once, when it becomes live.
        if previous.is_none() {
            observed.updated.push(record);
        }
    }

    /// After the task changes: `failFast` checks of the waiters of failed
    /// tasks, and cascades owed to queued inputs and new work below
    /// cancelled owners.
    fn observe_scopes(&mut self, publication: &CommitPublication, observed: &mut Observed<'_>) {
        for id in &observed.failed {
            let Some(waiters) = self.waiters.get(id) else {
                continue;
            };
            for waiter in waiters {
                let fail_fast = self.live.get(waiter).is_some_and(|record| {
                    matches!(
                        record.state,
                        TaskState::Waiting {
                            policy: JoinPolicy::FailFast,
                            ..
                        }
                    )
                });
                if fail_fast {
                    self.fail_fast_checks.insert(*waiter);
                    observed.reconcile = true;
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
            // Only an owner with cancellation intent withdraws it; a later
            // intent's mark runs the cascade then.
            if self.intent.is_empty() {
                continue;
            }
            let conversation = Node::Conversation(submission.conversation_id);
            if !self.known(conversation) || self.below_cancelled(conversation) {
                self.cascade_pending = true;
            }
        }
        for record in &observed.updated {
            // Work created below a cancelled owner, even after its cascade, is aborted too.
            if self.unloaded.contains(&record.id) {
                observed.reconcile = true;
            } else if !record.background
                && !record.abort_requested
                && self.below_cancelled(parent_of(record))
            {
                self.cascade_pending = true;
            }
        }
        // A cascade that a reservation or step found pending runs with the
        // next commit of any kind.
        if self.cascade_pending {
            observed.reconcile = true;
        }
    }
}
