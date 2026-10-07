//! The task graph view (`harness/task-graph.ts`, spec §9.5): every live task
//! of the Session, built lazily on the Session line and advanced from the
//! Session's commit publications.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};

use eukhe_chord::context::{without_abort_signal, Context};
use eukhe_chord::delta::{apply_immutable, Op, Seg};
use eukhe_chord::json::{from_json, to_json, JsonObject, JsonValue};
use eukhe_chord::{
    replicated_state_from_source, AttachedReplicatedState, ReplicatedStateSourceOptions,
};
use futures::future::{BoxFuture, FutureExt};
use serde::{Deserialize, Serialize};

use crate::harness::util::{closed_error, scan_all};
use crate::harness::view::Detach;
use crate::session::{
    CommittedStateSource, CommittedWatch, ObservedValue, Ops, Session, SessionError, SessionResult,
};
use crate::types::{
    AnyTaskRecord, CommitChange, CommitPublication, ConversationId, ConversationQuery, JoinPolicy,
    Storage, TaskId, TaskOutcomeStatus, TaskQuery, TaskState, TaskStatus,
};

const LIVE_STATUSES: [TaskStatus; 4] = [
    TaskStatus::Pending,
    TaskStatus::Running,
    TaskStatus::Waiting,
    TaskStatus::Completing,
];
const SCAN_PAGE_SIZE: usize = 256;

/// A live task's durable status without its checkpoint and outcome payloads
/// (spec §9.5).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "camelCase")]
pub enum TaskGraphState {
    Pending {
        /// The checkpoint's `phase`; absent when it is not a string.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        phase: Option<String>,
    },
    Running {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        phase: Option<String>,
    },
    Waiting {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        phase: Option<String>,
        on: Vec<TaskId>,
        policy: JoinPolicy,
    },
    /// Outcome held until its ordinary owned work drains.
    Completing { outcome: TaskOutcomeStatus },
}

impl TaskGraphState {
    /// The TS `status` string.
    #[must_use]
    pub fn status(&self) -> &'static str {
        match self {
            Self::Pending { .. } => "pending",
            Self::Running { .. } => "running",
            Self::Waiting { .. } => "waiting",
            Self::Completing { .. } => "completing",
        }
    }
}

/// One live task of the graph.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TaskGraphNode {
    pub id: TaskId,
    pub kind: String,
    pub conversation_id: ConversationId,
    /// Owner task; absent for a conversation-owned task.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub owner: Option<TaskId>,
    pub background: bool,
    pub abort_requested: bool,
    pub state: TaskGraphState,
    /// Conversations this task owns, in ID order.
    pub conversations: Vec<ConversationId>,
}

/// Every live task of the Session (spec §9.5): the JSON
/// `{ tasks: { [decimal id]: TaskGraphNode } }`. Clones share the value.
#[derive(Debug, Clone, PartialEq)]
pub struct TaskGraph(JsonValue);

impl TaskGraph {
    /// The graph's JSON.
    #[must_use]
    pub fn json(&self) -> &JsonValue {
        &self.0
    }

    /// The `tasks` object, keyed by decimal task ID.
    ///
    /// # Panics
    ///
    /// Never: every graph this module builds holds a `tasks` object.
    #[must_use]
    pub fn tasks(&self) -> &JsonObject {
        match &self.0["tasks"] {
            JsonValue::Object(tasks) => tasks,
            JsonValue::Null
            | JsonValue::Bool(_)
            | JsonValue::Number(_)
            | JsonValue::String(_)
            | JsonValue::Array(_) => unreachable!("a task graph always holds a tasks object"),
        }
    }

    /// The node of task `id`, or `None` when it is not live.
    ///
    /// # Errors
    ///
    /// The node's JSON does not decode (never for a graph this module built).
    pub fn node(&self, id: TaskId) -> SessionResult<Option<TaskGraphNode>> {
        self.tasks()
            .get(&id.to_string())
            .map(from_json)
            .transpose()
            .map_err(SessionError::from)
    }

    /// Every node in key order.
    ///
    /// # Errors
    ///
    /// A node's JSON does not decode (never for a graph this module built).
    pub fn nodes(&self) -> SessionResult<Vec<TaskGraphNode>> {
        self.tasks()
            .values()
            .map(|node| from_json(node).map_err(SessionError::from))
            .collect()
    }

    /// Whether both graphs are the same revision (TS `toBe`).
    #[must_use]
    pub fn same(&self, other: &Self) -> bool {
        self.0.strict_equals(&other.0)
    }
}

impl ObservedValue for TaskGraph {
    fn is_retirement(&self) -> bool {
        false
    }

    fn to_json(&self) -> JsonValue {
        self.0.clone()
    }
}

/// Serialized exact-frame watch of the task graph.
pub type TaskGraphWatch = CommittedWatch<TaskGraph>;

#[derive(Clone)]
enum Observer {
    State(CommittedStateSource),
    Watch(TaskGraphWatch),
}

impl Observer {
    fn advance(&self, value: &TaskGraph, ops: &Ops, cx: &Context) {
        match self {
            Self::State(source) => source.advance(value, Arc::clone(ops), cx.clone()),
            Self::Watch(watch) => watch.advance(value.clone(), Arc::clone(ops), cx.clone()),
        }
    }

    fn close_session(&self) {
        match self {
            Self::State(source) => source.close_session(),
            Self::Watch(watch) => watch.close_session(),
        }
    }
}

struct Mount {
    value: TaskGraph,
    observers: Vec<(u64, Observer)>,
}

type SharedMount = Arc<Mutex<Mount>>;

struct GraphState {
    mount: Option<SharedMount>,
    closed: bool,
    next_observer: u64,
}

struct Inner {
    session: Session,
    storage: Arc<dyn Storage>,
    state: Mutex<GraphState>,
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The Harness's task graph mount: built on the Session line by its first
/// observer and dropped with its last. It advances from the Session's commit
/// publications, which are durable.
#[derive(Clone)]
pub(crate) struct TaskGraphView {
    inner: Arc<Inner>,
}

impl TaskGraphView {
    pub(crate) fn new(session: Session, storage: Arc<dyn Storage>) -> Self {
        Self {
            inner: Arc::new(Inner {
                session,
                storage,
                state: Mutex::new(GraphState {
                    mount: None,
                    closed: false,
                    next_observer: 0,
                }),
            }),
        }
    }

    /// Observe the Session's commits and close.
    ///
    /// # Errors
    ///
    /// The Session is closed or poisoned.
    pub(crate) fn subscribe(&self) -> SessionResult<()> {
        let weak = Arc::downgrade(&self.inner);
        let commits = self
            .inner
            .session
            .subscribe_commits(Arc::new(move |publication, cx| {
                if let Some(inner) = weak.upgrade() {
                    let mount = lock(&inner.state).mount.clone();
                    if let Some(mount) = mount {
                        advance(&mount, publication, cx);
                    }
                }
            }))?;
        // The subscription lives as long as the Session; dropping the handle keeps it.
        drop(commits);
        let weak = Arc::downgrade(&self.inner);
        let close = self.inner.session.subscribe_close(Arc::new(move || {
            let Some(inner) = weak.upgrade() else {
                return;
            };
            let mount = {
                let mut state = lock(&inner.state);
                state.closed = true;
                state.mount.take()
            };
            let Some(mount) = mount else {
                return;
            };
            let observers: Vec<_> = lock(&mount)
                .observers
                .iter()
                .map(|(_, observer)| observer.clone())
                .collect();
            for observer in observers {
                observer.close_session();
            }
        }))?;
        drop(close);
        Ok(())
    }

    /// A disposable read-only Chord state of the graph.
    pub(crate) fn state(
        &self,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<AttachedReplicatedState>> {
        let attached = self.attach(
            |value, release| Observer::State(CommittedStateSource::new(&value, release)),
            cx,
        );
        async move {
            let (observer, detach) = attached.await?;
            let Observer::State(source) = observer else {
                unreachable!("the factory creates a state source")
            };
            replicated_state_from_source(&source, ReplicatedStateSourceOptions::default()).map_err(
                |error| {
                    detach();
                    SessionError::other(error)
                },
            )
        }
        .boxed()
    }

    /// A serialized exact-frame watch of the graph; cancelling `cx` stops it.
    pub(crate) fn watch(&self, cx: &Context) -> BoxFuture<'static, SessionResult<TaskGraphWatch>> {
        let attached = self.attach(
            |value, release| Observer::Watch(CommittedWatch::new(value, release, None)),
            cx,
        );
        let signal = cx.abort_signal();
        async move {
            let (observer, _detach) = attached.await?;
            let Observer::Watch(watch) = observer else {
                unreachable!("the factory creates a watch")
            };
            if let Some(signal) = &signal {
                if let Some(reason) = signal.reason() {
                    watch.cancel();
                    return Err(SessionError::Aborted(reason));
                }
                watch.observe_cancellation(signal)?;
            }
            Ok(watch)
        }
        .boxed()
    }

    /// Register an observer created from the current revision, atomically on
    /// the Session line.
    fn attach(
        &self,
        create: impl FnOnce(TaskGraph, Box<dyn FnOnce() + Send>) -> Observer + Send + 'static,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<(Observer, Detach)>> {
        let inner = Arc::clone(&self.inner);
        let cx = cx.clone();
        self.inner
            .session
            .read_on_line(async move {
                let existing = lock(&inner.state).mount.clone();
                let mount = match existing {
                    Some(mount) => mount,
                    None => Arc::new(Mutex::new(Mount {
                        value: inner.build(&cx).await?,
                        observers: Vec::new(),
                    })),
                };
                let observer_id = {
                    let mut state = lock(&inner.state);
                    state.next_observer += 1;
                    state.next_observer
                };
                let detach: Arc<dyn Fn() + Send + Sync> = {
                    let views = Arc::downgrade(&inner);
                    let mount = Arc::clone(&mount);
                    Arc::new(move || detach_observer(&views, &mount, observer_id))
                };
                let release = {
                    let detach = Arc::clone(&detach);
                    Box::new(move || detach()) as Box<dyn FnOnce() + Send>
                };
                let value = lock(&mount).value.clone();
                let observer = create(value, release);
                // Close or cancellation may begin while the mount builds; register nothing then.
                let mut mounted = lock(&mount);
                {
                    let mut state = lock(&inner.state);
                    if state.closed {
                        return Err(closed_error());
                    }
                    if let Some(reason) = cx.abort_signal().and_then(|signal| signal.reason()) {
                        return Err(SessionError::Aborted(reason));
                    }
                    state.mount = Some(Arc::clone(&mount));
                }
                mounted.observers.push((observer_id, observer.clone()));
                drop(mounted);
                Ok((observer, detach))
            })
            .boxed()
    }
}

impl Inner {
    async fn build(&self, cx: &Context) -> SessionResult<TaskGraph> {
        let storage = &*self.storage;
        let mut records: Vec<AnyTaskRecord> = Vec::new();
        for status in LIVE_STATUSES {
            let query = TaskQuery {
                status: Some(status),
                ..TaskQuery::default()
            };
            records.extend(
                scan_all(|cursor| {
                    let query = query.clone();
                    async move {
                        Ok(storage
                            .scan_tasks(&query, SCAN_PAGE_SIZE, cursor.as_ref(), cx)
                            .await?)
                    }
                })
                .await?,
            );
        }
        records.sort_by_key(|record| record.id);
        let mut tasks = JsonObject::with_capacity(records.len());
        for record in &records {
            let query = ConversationQuery {
                owner_task_id: Some(record.id),
                ..ConversationQuery::default()
            };
            let owned = scan_all(|cursor| async move {
                Ok(storage
                    .scan_conversations(&query, SCAN_PAGE_SIZE, cursor.as_ref(), cx)
                    .await?)
            })
            .await?;
            let mut conversations: Vec<ConversationId> =
                owned.iter().map(|conversation| conversation.id).collect();
            conversations.sort_unstable();
            tasks.insert(
                record.id.to_string(),
                to_json(&node_of(record, conversations))?,
            );
        }
        let mut root = JsonObject::with_capacity(1);
        root.insert("tasks", JsonValue::Object(Arc::new(tasks)));
        Ok(TaskGraph(JsonValue::Object(Arc::new(root))))
    }
}

fn detach_observer(views: &Weak<Inner>, mount: &SharedMount, observer: u64) {
    let mut mounted = lock(mount);
    mounted.observers.retain(|(other, _)| *other != observer);
    if !mounted.observers.is_empty() {
        return;
    }
    let Some(views) = views.upgrade() else {
        return;
    };
    let mut state = lock(&views.state);
    if state
        .mount
        .as_ref()
        .is_some_and(|current| Arc::ptr_eq(current, mount))
    {
        state.mount = None;
    }
}

/// Derive the mount's operations from one publication, apply them, and hand
/// the revision to every observer.
#[expect(
    clippy::too_many_lines,
    reason = "one-to-one port of the TS `advance`: task nodes, then owned conversations"
)]
fn advance(mount: &SharedMount, publication: &CommitPublication, cx: &Context) {
    let (value, ops, observers) = {
        let mut mounted = lock(mount);
        let mut ops: Vec<Op> = Vec::new();
        // Nodes this publication set or deleted, over the mount's value.
        let mut changed: HashMap<String, Option<TaskGraphNode>> = HashMap::new();
        let current = mounted.value.clone();
        let node = |changed: &HashMap<String, Option<TaskGraphNode>>,
                    key: &str|
         -> Option<TaskGraphNode> {
            match changed.get(key) {
                Some(node) => node.clone(),
                None => current.tasks().get(key).map(decode_node),
            }
        };
        for change in &publication.changes {
            let CommitChange::Task(record) = change else {
                continue;
            };
            let key = record.id.to_string();
            let previous = node(&changed, &key);
            if matches!(record.state, TaskState::Terminal { .. }) {
                if previous.is_none() {
                    continue;
                }
                ops.push(Op::Delete(vec![
                    Seg::from("tasks"),
                    Seg::from(key.as_str()),
                ]));
                changed.insert(key, None);
                continue;
            }
            let next = node_of(
                record,
                previous
                    .as_ref()
                    .map(|previous| previous.conversations.clone())
                    .unwrap_or_default(),
            );
            let json = node_json(&next);
            if previous
                .as_ref()
                .is_some_and(|previous| node_json(previous).to_string() == json.to_string())
            {
                continue;
            }
            ops.push(Op::Set(
                vec![Seg::from("tasks"), Seg::from(key.as_str())],
                json,
            ));
            changed.insert(key, Some(next));
        }
        // After the tasks, so a conversation created with its owner task in one
        // commit finds the owner's node. Change order within a publication is
        // unspecified, so each owner's list is sorted again.
        let mut created: Vec<(String, Vec<ConversationId>)> = Vec::new();
        for change in &publication.changes {
            let CommitChange::Conversation(conversation) = change else {
                continue;
            };
            let Some(owner) = &conversation.owner else {
                continue;
            };
            let key = owner.task_id.to_string();
            if node(&changed, &key).is_none() {
                continue;
            }
            match created.iter_mut().find(|(other, _)| *other == key) {
                Some((_, ids)) => ids.push(conversation.id),
                None => created.push((key, vec![conversation.id])),
            }
        }
        for (key, ids) in created {
            let Some(owner) = node(&changed, &key) else {
                continue;
            };
            let mut conversations = owner.conversations;
            conversations.extend(ids);
            conversations.sort_unstable();
            // Conversation IDs are safe integers.
            let json = to_json(&conversations).expect("conversation IDs are JSON");
            ops.push(Op::Set(
                vec![
                    Seg::from("tasks"),
                    Seg::from(key.as_str()),
                    Seg::from("conversations"),
                ],
                json,
            ));
        }
        if ops.is_empty() {
            return;
        }
        // The operations were derived from the mounted value.
        let next = apply_immutable(mounted.value.json(), &ops)
            .expect("graph operations apply to the mounted graph");
        mounted.value = TaskGraph(next);
        let observers: Vec<_> = mounted
            .observers
            .iter()
            .map(|(_, observer)| observer.clone())
            .collect();
        (mounted.value.clone(), Ops::from(ops), observers)
    };
    let frame_cx = without_abort_signal(cx);
    for observer in observers {
        observer.advance(&value, &ops, &frame_cx);
    }
}

fn decode_node(json: &JsonValue) -> TaskGraphNode {
    // Every node in the mount was encoded by this module.
    from_json(json).expect("mounted graph nodes decode")
}

fn node_json(node: &TaskGraphNode) -> JsonValue {
    // Task records are JSON, so their nodes are.
    to_json(node).expect("graph nodes are JSON")
}

fn node_of(record: &AnyTaskRecord, conversations: Vec<ConversationId>) -> TaskGraphNode {
    TaskGraphNode {
        id: record.id,
        kind: record.kind.clone(),
        conversation_id: record.conversation_id,
        owner: record.owner,
        background: record.background,
        abort_requested: record.abort_requested,
        state: state_of(&record.state),
        conversations,
    }
}

fn state_of(state: &TaskState) -> TaskGraphState {
    match state {
        TaskState::Pending { checkpoint } => TaskGraphState::Pending {
            phase: phase_of(checkpoint),
        },
        TaskState::Running { checkpoint } => TaskGraphState::Running {
            phase: phase_of(checkpoint),
        },
        TaskState::Waiting {
            checkpoint,
            on,
            policy,
        } => TaskGraphState::Waiting {
            phase: phase_of(checkpoint),
            on: on.clone(),
            policy: *policy,
        },
        // Terminal records never reach here: they leave the graph.
        TaskState::Completing { outcome } | TaskState::Terminal { outcome } => {
            TaskGraphState::Completing {
                outcome: outcome.status(),
            }
        }
    }
}

fn phase_of(checkpoint: &JsonValue) -> Option<String> {
    checkpoint["phase"].as_str().map(str::to_owned)
}

/// A graph over a state's JSON value, for assertions on Chord states.
#[cfg(test)]
pub(crate) fn graph_from_json(value: JsonValue) -> TaskGraph {
    TaskGraph(value)
}

impl crate::harness::Harness {
    /// A disposable read-only Chord state of the task graph.
    #[must_use = "the state is attached only when the future runs"]
    pub fn task_graph(
        &self,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<AttachedReplicatedState>> {
        self.core().task_graph().state(cx)
    }

    /// A serialized exact-frame watch of the task graph; cancelling `cx`
    /// stops it.
    #[must_use = "the watch is attached only when the future runs"]
    pub fn watch_task_graph(
        &self,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<TaskGraphWatch>> {
        self.core().task_graph().watch(cx)
    }
}
