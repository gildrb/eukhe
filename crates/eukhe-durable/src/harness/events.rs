//! Experimental agent events (`harness/events.ts`, spec §9.4): one
//! conversation's commits translated into events shaped like the coding
//! agent's session events, one batch per commit.

use std::collections::{HashMap, HashSet};
use std::future::Future;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::delta::{Op, Seg};
use eukhe_chord::json::{from_json, JsonObject, JsonValue};
use eukhe_types::pi_ai::{AssistantContentBlock, AssistantMessage, Message, Usage};
use futures::future::{BoxFuture, FutureExt};
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use crate::harness::live::{CompactionStatus, LiveGeneration, NestedToolSlot, ToolSlot};
use crate::harness::tool::NESTED_RESULT_DOC;
use crate::harness::types::{
    AgentState, CompactionReason, NestedToolExecutionResult, ToolDiagnostic,
};
use crate::harness::usage::UsageState;
use crate::harness::util::scan_all;
use crate::harness::view::{ConversationView, ViewObserver};
use crate::harness::Harness;
use crate::session::{
    CommittedWatch, ObservedValue, Ops, SessionError, SessionResult, WatchEnd, WatchListenerError,
};
use crate::types::{
    AnyTaskRecord, CommitChange, CommitPublication, ConversationId, DocumentCommitChange, EntryId,
    EntryRecord, Storage, SubmissionId, SubmissionRecord, TaskId, TaskOutcome, TaskQuery,
    TaskStatus,
};

const GENERATION_KIND: &str = "pi.generation";

/// One segment of a tool-call argument path.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum PathSegment {
    Key(String),
    Index(usize),
}

impl From<&Seg> for PathSegment {
    fn from(segment: &Seg) -> Self {
        match segment {
            Seg::Key(key) => Self::Key(key.to_string()),
            Seg::Index(index) => Self::Index(*index),
        }
    }
}

/// One change to the in-flight assistant message, relative to that message.
#[expect(
    clippy::large_enum_variant,
    reason = "changes move once into their event; boxing would allocate per change"
)]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "type",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum MessageChange {
    TextStart {
        content_index: usize,
        block: AssistantContentBlock,
    },
    ThinkingStart {
        content_index: usize,
        block: AssistantContentBlock,
    },
    #[serde(rename = "toolcall_start")]
    ToolcallStart {
        content_index: usize,
        block: AssistantContentBlock,
    },
    TextDelta {
        content_index: usize,
        delta: String,
    },
    ThinkingDelta {
        content_index: usize,
        delta: String,
    },
    #[serde(rename = "toolcall_delta")]
    ToolcallDelta {
        content_index: usize,
        path: Vec<PathSegment>,
        delta: String,
    },
    Block {
        content_index: usize,
        block: AssistantContentBlock,
    },
    Message {
        message: AssistantMessage,
    },
}

/// A queued inbox item: its submission and mode.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct QueuedItem {
    pub id: SubmissionId,
    /// `"steer"`, `"followUp"`, or `"write"`.
    pub mode: String,
}

/// The run of a snapshot.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SnapshotRun {
    pub inputs: Vec<SubmissionId>,
}

/// The state of one conversation at attachment, or at an overflow.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SnapshotEvent {
    pub entries: Vec<EntryRecord>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub run: Option<SnapshotRun>,
    /// Current generation attempt: its in-flight partial, retry backoff, or
    /// deferred poll.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub generation: Option<LiveGeneration>,
    pub tools: Vec<ToolSlot>,
    /// `pi.live.nestedTools`: nested calls of running tool calls.
    #[serde(rename = "nestedTools")]
    pub nested_tools: Vec<NestedToolSlot>,
    /// `pi.live.compactions`: live compactions with their attempt and retry backoff.
    pub compactions: Vec<CompactionStatus>,
    pub inbox: Vec<QueuedItem>,
    /// `pi.agent`; `{}` when absent.
    pub agent: AgentState,
    pub usage: UsageState,
}

/// Output change of a running tool slot: a front trim and then an append of
/// the retained window, or its replacement.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum ToolOutputUpdate {
    Set {
        set: String,
    },
    #[serde(rename_all = "camelCase")]
    Window {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        trim_start: Option<usize>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        append: Option<String>,
    },
}

/// Which call a tool event is about. `tool_call_id` is the call's ID in the
/// transcript and in tool events: the provider's ID for a model-issued call,
/// `<parent call ID>/<key>` for a nested one. Match events by it; do not
/// parse it. `task_id` is the call's tool task, absent for a call that never
/// got one (not offered, or not started in a sequential round). A nested call
/// also names the call that made it, by call ID and by tool task.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ToolEventCall {
    pub tool_call_id: String,
    pub tool_name: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub task_id: Option<TaskId>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parent_tool_call_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parent_task_id: Option<TaskId>,
}

/// Experimental agent event, shaped like the coding agent's session events
/// (spec §9.4).
#[expect(
    clippy::large_enum_variant,
    reason = "events move once into their batch; boxing would allocate per event"
)]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "type",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum AgentEvent {
    Snapshot(SnapshotEvent),
    RunStart {
        inputs: Vec<SubmissionId>,
    },
    RunEnd {
        inputs: Vec<SubmissionId>,
    },
    TurnStart,
    TurnEnd,
    MessageStart {
        message: Message,
    },
    /// `usage` is the partial's current usage, as in the coding agent's JSON mode.
    MessageUpdate {
        usage: Usage,
        changes: Vec<MessageChange>,
    },
    MessageEnd {
        entry: EntryRecord,
    },
    ToolExecutionStart {
        #[serde(flatten)]
        call: ToolEventCall,
        args: JsonValue,
    },
    ToolExecutionUpdate {
        #[serde(flatten)]
        call: ToolEventCall,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        output: Option<ToolOutputUpdate>,
        /// `Some(null)` when a safe replay removed the details.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        details: Option<JsonValue>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        diagnostics: Option<Vec<ToolDiagnostic>>,
    },
    /// A model-issued call ends with its result `entry`, a nested call with
    /// its `result`. Both are absent when the tool task faulted or was
    /// orphaned, or when the call's slot left `pi.live` unfinished: its run
    /// ended, or its parent settled first.
    ToolExecutionEnd {
        #[serde(flatten)]
        call: ToolEventCall,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        entry: Option<EntryRecord>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        result: Option<NestedToolExecutionResult>,
    },
    InboxUpdate {
        items: Vec<QueuedItem>,
    },
    Submission {
        record: SubmissionRecord,
    },
    AutoRetryStart {
        attempt: u64,
        at: f64,
        error_message: String,
    },
    AutoRetryEnd {
        attempt: u64,
    },
    DeferredPoll {
        poll_at: f64,
    },
    EntryAppended {
        entry: EntryRecord,
    },
    AgentChanged {
        agent: AgentState,
    },
    UsageChanged {
        usage: UsageState,
    },
    TaskFailed {
        task_id: TaskId,
        kind: String,
        message: String,
    },
    CompactionStart {
        task_id: TaskId,
        reason: CompactionReason,
        blocking: bool,
    },
    /// The task's receipt tells whether it produced a summary; the summary
    /// entry has its own events.
    CompactionEnd {
        task_id: TaskId,
        reason: CompactionReason,
    },
}

impl AgentEvent {
    /// The TS `type` string.
    #[must_use]
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Snapshot(_) => "snapshot",
            Self::RunStart { .. } => "run_start",
            Self::RunEnd { .. } => "run_end",
            Self::TurnStart => "turn_start",
            Self::TurnEnd => "turn_end",
            Self::MessageStart { .. } => "message_start",
            Self::MessageUpdate { .. } => "message_update",
            Self::MessageEnd { .. } => "message_end",
            Self::ToolExecutionStart { .. } => "tool_execution_start",
            Self::ToolExecutionUpdate { .. } => "tool_execution_update",
            Self::ToolExecutionEnd { .. } => "tool_execution_end",
            Self::InboxUpdate { .. } => "inbox_update",
            Self::Submission { .. } => "submission",
            Self::AutoRetryStart { .. } => "auto_retry_start",
            Self::AutoRetryEnd { .. } => "auto_retry_end",
            Self::DeferredPoll { .. } => "deferred_poll",
            Self::EntryAppended { .. } => "entry_appended",
            Self::AgentChanged { .. } => "agent_changed",
            Self::UsageChanged { .. } => "usage_changed",
            Self::TaskFailed { .. } => "task_failed",
            Self::CompactionStart { .. } => "compaction_start",
            Self::CompactionEnd { .. } => "compaction_end",
        }
    }
}

/// One commit's events.
pub type AgentEventBatch = Arc<[AgentEvent]>;

impl ObservedValue for AgentEventBatch {
    fn is_retirement(&self) -> bool {
        false
    }

    fn to_json(&self) -> JsonValue {
        // Events hold committed JSON records only.
        eukhe_chord::json::to_json(&**self).expect("agent events are JSON")
    }
}

/// The sole asynchronous listener of an event stream: `(events, context)`.
pub type AgentEventListener = Arc<
    dyn Fn(AgentEventBatch, Context) -> BoxFuture<'static, Result<(), WatchListenerError>>
        + Send
        + Sync,
>;

/// Serialized stream of one conversation's event batches, one per commit.
#[derive(Debug, Clone)]
pub struct AgentEventStream {
    snapshot: SnapshotEvent,
    watch: CommittedWatch<AgentEventBatch>,
}

impl AgentEventStream {
    /// The `snapshot` event at attachment.
    #[must_use]
    pub fn snapshot(&self) -> &SnapshotEvent {
        &self.snapshot
    }

    /// Install the sole listener. Never invokes it inline.
    ///
    /// # Errors
    ///
    /// `Watch is already started`, or `Watch is stopped` after termination.
    pub fn start(&self, listener: AgentEventListener) -> SessionResult<()> {
        self.watch
            .start(Arc::new(move |events, _ops, cx| listener(events, cx)))
    }

    /// Idempotently stop future batches and return the terminal result.
    pub fn stop(&self) -> impl Future<Output = WatchEnd> + Send + 'static {
        self.watch.stop()
    }

    /// eukhe addition (TS has no counterpart): resolves once every batch
    /// queued when this is called has been passed to the listener and its
    /// future has settled; at once when the stream has terminated, and as
    /// soon as it terminates later. Commits queue their batches before their
    /// commit future resolves, so after `wait_for_idle()` this is a barrier
    /// for every batch committed so far. See [`CommittedWatch::delivered`].
    pub fn delivered(&self) -> impl Future<Output = ()> + Send + 'static {
        self.watch.delivered()
    }

    /// Settles when the stream terminates.
    pub fn closed(&self) -> impl Future<Output = WatchEnd> + Send + 'static {
        self.watch.closed()
    }
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Decode committed JSON into its typed form.
fn decode<T: DeserializeOwned>(json: &JsonValue) -> T {
    // Built-in documents and their parts were validated when committed.
    from_json(json).expect("committed built-in documents decode")
}

fn get<'a>(value: Option<&'a JsonValue>, key: &str) -> Option<&'a JsonValue> {
    value.and_then(|value| value.get(key))
}

/// JS `===` of two possibly absent values.
fn same(left: Option<&JsonValue>, right: Option<&JsonValue>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => left.strict_equals(right),
        (None, None) => true,
        (Some(_), None) | (None, Some(_)) => false,
    }
}

/// The typed parts of a view the events read.
struct Parts<'a> {
    live: Option<&'a JsonValue>,
    inbox: Option<&'a JsonValue>,
    agent: Option<&'a JsonValue>,
    usage: Option<&'a JsonValue>,
}

impl<'a> Parts<'a> {
    fn of(view: &'a ConversationView) -> Self {
        Self {
            live: view.doc("pi.live"),
            inbox: view.doc("pi.inbox"),
            agent: view.doc("pi.agent"),
            usage: view.doc("pi.usage"),
        }
    }

    fn live(&self, key: &str) -> Option<&'a JsonValue> {
        get(self.live, key)
    }

    fn slots(&self) -> &'a [JsonValue] {
        self.list("tools")
    }

    fn nested(&self) -> &'a [JsonValue] {
        self.list("nestedTools")
    }

    fn list(&self, key: &str) -> &'a [JsonValue] {
        self.live(key)
            .and_then(JsonValue::as_array)
            .unwrap_or_default()
    }

    fn compactions(&self) -> &'a [JsonValue] {
        self.list("compactions")
    }
}

fn snapshot_of(view: &ConversationView) -> SnapshotEvent {
    let parts = Parts::of(view);
    SnapshotEvent {
        entries: view.entries().as_ref().clone(),
        run: parts.live("run").map(|run| SnapshotRun {
            inputs: decode(&run["inputs"]),
        }),
        generation: parts.live("generation").map(decode),
        tools: parts.live("tools").map(decode).unwrap_or_default(),
        nested_tools: parts.live("nestedTools").map(decode).unwrap_or_default(),
        compactions: parts.live("compactions").map(decode).unwrap_or_default(),
        inbox: queued(parts.inbox),
        agent: parts.agent.map(decode).unwrap_or_default(),
        usage: parts.usage.map(decode).unwrap_or_default(),
    }
}

fn queued(inbox: Option<&JsonValue>) -> Vec<QueuedItem> {
    get(inbox, "items")
        .and_then(JsonValue::as_array)
        .unwrap_or_default()
        .iter()
        .map(|item| QueuedItem {
            id: decode(&item["id"]),
            mode: item["mode"].as_str().unwrap_or_default().to_owned(),
        })
        .collect()
}

/// The view observer translating each publication into one batch.
#[derive(Clone)]
struct EventsObserver {
    conversation_id: ConversationId,
    watch: CommittedWatch<AgentEventBatch>,
    current: Arc<Mutex<ConversationView>>,
    /// Generations whose held outcome already ended their turn.
    held: Arc<Mutex<HashSet<TaskId>>>,
    snapshot: SnapshotEvent,
}

impl ViewObserver for EventsObserver {
    fn publication(
        &self,
        before: &ConversationView,
        after: &ConversationView,
        ops: &Ops,
        publication: &CommitPublication,
        cx: &Context,
    ) {
        *lock(&self.current) = after.clone();
        let events = {
            let mut held = lock(&self.held);
            translate(
                self.conversation_id,
                before,
                after,
                ops,
                publication,
                &mut held,
            )
        };
        if !events.is_empty() {
            self.watch
                .advance(Arc::from(events), Arc::from(Vec::new()), cx.clone());
        }
    }

    fn close_session(&self, failure: Option<Arc<SessionError>>) {
        self.watch.close_session(failure);
    }
}

/// Experimental: attach to one conversation's agent events (spec §9.4). The
/// snapshot and the registration for later commits are captured atomically
/// on the Session line; overflow replaces undelivered batches with one
/// snapshot.
#[must_use = "the stream is attached only when the future runs"]
pub fn watch_events(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> BoxFuture<'static, SessionResult<AgentEventStream>> {
    let scan_cx = cx.clone();
    let views = harness.core().views();
    let report: Arc<dyn Fn(SessionError) + Send + Sync> = {
        let views = views.clone();
        Arc::new(move |error| views.report(error))
    };
    let attached = views.attach(
        conversation_id,
        Box::new(move |initial, release, storage: Arc<dyn Storage>| {
            async move {
                // Generations whose held outcome already ended their turn, read on the line with the snapshot.
                let query = TaskQuery {
                    conversation_id: Some(conversation_id),
                    kind: Some(GENERATION_KIND.to_owned()),
                    status: Some(TaskStatus::Completing),
                    ..TaskQuery::default()
                };
                let storage = &*storage;
                let completing: Vec<AnyTaskRecord> = scan_all(|cursor| {
                    let (query, cx) = (query.clone(), &scan_cx);
                    async move { Ok(storage.scan_tasks(&query, 100, cursor.as_ref(), cx).await?) }
                })
                .await?;
                let held = completing.iter().map(|record| record.id).collect();
                let snapshot = snapshot_of(&initial);
                let current = Arc::new(Mutex::new(initial));
                // Batches are the watch's values; an overflow delivers a snapshot of the newest view instead.
                let replace_current = Arc::clone(&current);
                let watch = CommittedWatch::new(
                    Arc::from(Vec::new()),
                    release,
                    report,
                    Some(Box::new(move || -> AgentEventBatch {
                        Arc::from(vec![AgentEvent::Snapshot(snapshot_of(&lock(
                            &replace_current,
                        )))])
                    })),
                );
                Ok(EventsObserver {
                    conversation_id,
                    watch,
                    current,
                    held: Arc::new(Mutex::new(held)),
                    snapshot,
                })
            }
            .boxed()
        }),
        cx,
    );
    let signal = cx.abort_signal();
    async move {
        let (observer, _detach) = attached.await?;
        // Like a watch, the acquisition context governs the stream's lifetime.
        if let Some(signal) = &signal {
            if let Some(reason) = signal.reason() {
                observer.watch.cancel();
                return Err(SessionError::Aborted(reason));
            }
            observer.watch.observe_cancellation(signal)?;
        }
        Ok(AgentEventStream {
            snapshot: observer.snapshot,
            watch: observer.watch,
        })
    }
    .boxed()
}

/// The tool result for `call_id` among `entries`.
fn result_of<'a>(entries: &[&'a EntryRecord], call_id: &str) -> Option<&'a EntryRecord> {
    entries.iter().copied().find(|entry| {
        matches!(
            entry.model.as_ref().and_then(|model| model.first()),
            Some(Message::ToolResult(result)) if result.tool_call_id == call_id
        )
    })
}

fn str_at<'a>(value: &'a JsonValue, key: &str) -> &'a str {
    value[key].as_str().unwrap_or_default()
}

fn is_status(slot: Option<&JsonValue>, status: &str) -> bool {
    slot.is_some_and(|slot| slot["status"].as_str() == Some(status))
}

fn entry_id_of(value: &JsonValue) -> Option<EntryId> {
    match value {
        JsonValue::Null => None,
        JsonValue::Bool(_)
        | JsonValue::Number(_)
        | JsonValue::String(_)
        | JsonValue::Array(_)
        | JsonValue::Object(_) => Some(decode(value)),
    }
}

/// The identifying fields of a slot's tool events, model-issued or nested.
fn call_of(slot: &JsonValue) -> ToolEventCall {
    ToolEventCall {
        tool_call_id: str_at(slot, "callId").to_owned(),
        tool_name: str_at(slot, "name").to_owned(),
        task_id: slot.get("taskId").map(decode),
        parent_tool_call_id: slot
            .get("parentCallId")
            .map(|id| id.as_str().unwrap_or_default().to_owned()),
        parent_task_id: slot.get("parentTaskId").map(decode),
    }
}

fn is_nested(slot: &JsonValue) -> bool {
    slot.get("parentCallId").is_some()
}

/// One `tool_execution_end` of a model-issued call before its entry is placed.
struct ToolEnd<'a> {
    slot: &'a JsonValue,
    entry: Option<&'a EntryRecord>,
}

impl ToolEnd<'_> {
    fn event(&self) -> AgentEvent {
        AgentEvent::ToolExecutionEnd {
            call: call_of(self.slot),
            entry: self.entry.cloned(),
            result: None,
        }
    }
}

/// Every event one publication causes, in the order of spec §9.4.
#[expect(
    clippy::too_many_lines,
    reason = "one-to-one port of the TS translation, whose order is the spec's"
)]
fn translate(
    conversation_id: ConversationId,
    before: &ConversationView,
    after: &ConversationView,
    view_ops: &[Op],
    publication: &CommitPublication,
    held: &mut HashSet<TaskId>,
) -> Vec<AgentEvent> {
    let mut entries: Vec<&EntryRecord> = Vec::new();
    // Insertion-ordered, as a JS Map: a later record replaces an earlier one in place.
    let mut tasks: Vec<&AnyTaskRecord> = Vec::new();
    let mut submissions: Vec<&SubmissionRecord> = Vec::new();
    // Nested results this commit stored, by nested task ID; read now, since the caller's documents may retire next.
    let mut nested_results: HashMap<&str, NestedToolExecutionResult> = HashMap::new();
    for change in &publication.changes {
        match change {
            CommitChange::Entry(entry) if entry.conversation_id == conversation_id => {
                entries.push(entry);
            }
            CommitChange::Task(task) if task.conversation_id == conversation_id => {
                match tasks.iter_mut().find(|other| other.id == task.id) {
                    Some(slot) => *slot = task,
                    None => tasks.push(task),
                }
            }
            CommitChange::Submission(record) if record.conversation_id == conversation_id => {
                submissions.push(record);
            }
            CommitChange::Document(DocumentCommitChange::Document {
                record,
                conversation_id: Some(owner),
                value: Some(value),
                ..
            }) if *owner == conversation_id
                && record.kind == NESTED_RESULT_DOC.definition().kind =>
            {
                if let (Some(key), Some(result)) = (&record.key, value.get("result")) {
                    nested_results.insert(key, decode(result));
                }
            }
            CommitChange::Entry(_)
            | CommitChange::Task(_)
            | CommitChange::Submission(_)
            | CommitChange::Conversation(_)
            | CommitChange::Document(_) => {}
        }
    }
    if view_ops.is_empty() && entries.is_empty() && tasks.is_empty() && submissions.is_empty() {
        return Vec::new();
    }
    let task = |id: TaskId| tasks.iter().copied().find(|task| task.id == id);
    // Entries are appended in ID order; submission records are published in the order the commit first touched them.
    submissions.sort_by_key(|record| record.id);
    let was = Parts::of(before);
    let now = Parts::of(after);
    let mut events: Vec<AgentEvent> = Vec::new();

    // Progress: tool starts, the in-flight message, tool updates, retry and deferred state.
    let mut slots_before: Vec<(&str, &JsonValue)> = Vec::new();
    for slot in was.slots() {
        let call_id = str_at(slot, "callId");
        match slots_before.iter_mut().find(|(other, _)| *other == call_id) {
            Some(entry) => entry.1 = slot,
            None => slots_before.push((call_id, slot)),
        }
    }
    let previous_slot = |call_id: &str| {
        slots_before
            .iter()
            .find(|(other, _)| *other == call_id)
            .map(|(_, slot)| *slot)
    };
    let slots = now.slots();
    let nested_before = nested_by_task(was.nested());
    let previous_nested = |task_id: TaskId| {
        nested_before
            .iter()
            .find(|(other, _)| *other == task_id)
            .map(|(_, slot)| *slot)
    };
    let nested = now.nested();
    for slot in slots.iter().chain(nested) {
        let previous = if is_nested(slot) {
            previous_nested(decode(&slot["taskId"]))
        } else {
            previous_slot(str_at(slot, "callId"))
        };
        if !is_status(Some(slot), "running") || is_status(previous, "running") {
            continue;
        }
        // A nested slot carries the arguments the call runs with; a model-issued call's are in its intent checkpoint.
        let args = if is_nested(slot) {
            slot["arguments"].clone()
        } else {
            slot.get("taskId")
                .map(decode::<TaskId>)
                .and_then(task)
                .and_then(|record| record.state.checkpoint())
                .and_then(|checkpoint| checkpoint.get("arguments"))
                .cloned()
                .unwrap_or_else(|| JsonValue::Object(Arc::new(JsonObject::new())))
        };
        events.push(AgentEvent::ToolExecutionStart {
            call: call_of(slot),
            args,
        });
    }
    let generation_before = was.live("generation");
    let generation = now.live("generation");
    let partial_before = get(generation_before, "message");
    let partial = get(generation, "message");
    if let Some(partial) = partial {
        if partial_before.is_none() {
            events.push(AgentEvent::MessageStart {
                message: decode(partial),
            });
        } else if !same(Some(partial), partial_before) {
            let message: AssistantMessage = decode(partial);
            events.push(AgentEvent::MessageUpdate {
                usage: message.usage,
                changes: message_changes(view_ops, &message),
            });
        }
    }
    for (index, slot) in slots.iter().enumerate() {
        let Some(previous) = previous_slot(str_at(slot, "callId")) else {
            continue;
        };
        push_update(&mut events, view_ops, ("tools", index), slot, previous);
    }
    for (index, slot) in nested.iter().enumerate() {
        let Some(previous) = previous_nested(decode(&slot["taskId"])) else {
            continue;
        };
        push_update(
            &mut events,
            view_ops,
            ("nestedTools", index),
            slot,
            previous,
        );
    }
    let retry = get(generation, "retry");
    let retry_before = get(generation_before, "retry");
    if let (Some(generation), Some(retry), None) = (generation, retry, retry_before) {
        events.push(AgentEvent::AutoRetryStart {
            attempt: decode(&generation["attempt"]),
            at: decode(&retry["at"]),
            error_message: str_at(retry, "error").to_owned(),
        });
    }
    if let (Some(generation_before), Some(_), None) = (generation_before, retry_before, retry) {
        events.push(AgentEvent::AutoRetryEnd {
            attempt: decode(&generation_before["attempt"]),
        });
    }
    if let Some(deferred) = get(generation, "deferred") {
        let poll_at = &deferred["pollAt"];
        let previous = get(get(generation_before, "deferred"), "pollAt");
        if !same(Some(poll_at), previous) {
            events.push(AgentEvent::DeferredPoll {
                poll_at: decode(poll_at),
            });
        }
    }

    // Tools that end in this commit: a slot that becomes done, one created done
    // (a call not offered), or an unfinished one that vanishes because its run
    // ended. A done slot that vanishes ended earlier.
    let mut tool_ends: Vec<ToolEnd<'_>> = Vec::new();
    let mut end_tool = |slot, entry_id: Option<EntryId>| {
        let entry = entries
            .iter()
            .copied()
            .find(|candidate| Some(candidate.id) == entry_id);
        tool_ends.push(ToolEnd { slot, entry });
    };
    for (call_id, previous) in &slots_before {
        if is_status(Some(previous), "done") {
            continue;
        }
        let slot = slots
            .iter()
            .find(|candidate| str_at(candidate, "callId") == *call_id);
        match slot {
            Some(slot) if is_status(Some(slot), "done") => {
                end_tool(slot, slot.get("entry").and_then(entry_id_of));
            }
            Some(_) => {}
            // A slot whose run ended in this commit may have had its result appended with it, as for unstarted calls.
            None => end_tool(previous, result_of(&entries, call_id).map(|entry| entry.id)),
        }
    }
    for slot in slots {
        if is_status(Some(slot), "done") && previous_slot(str_at(slot, "callId")).is_none() {
            end_tool(slot, slot.get("entry").and_then(entry_id_of));
        }
    }
    // Nested calls that end in this commit, the same way, children before
    // the calls that made them: the lists hold parents first, so walk them
    // backwards.
    let mut end_nested = |slot: &JsonValue| {
        let task_id: TaskId = decode(&slot["taskId"]);
        events.push(AgentEvent::ToolExecutionEnd {
            call: call_of(slot),
            entry: None,
            result: nested_results.get(task_id.to_string().as_str()).cloned(),
        });
    };
    let nested_now = nested_by_task(nested);
    for (task_id, previous) in nested_before.iter().rev() {
        if is_status(Some(previous), "done") {
            continue;
        }
        let slot = nested_now
            .iter()
            .find(|(other, _)| other == task_id)
            .map(|(_, slot)| *slot);
        match slot {
            Some(slot) if is_status(Some(slot), "done") => end_nested(slot),
            Some(_) => {}
            None => end_nested(previous),
        }
    }
    for slot in nested.iter().rev() {
        if is_status(Some(slot), "done") && previous_nested(decode(&slot["taskId"])).is_none() {
            end_nested(slot);
        }
    }

    // Entries in append order; a tool's end directly precedes its result's message, as in the coding agent.
    let mut assistant_appended = false;
    for entry in &entries {
        events.extend(
            tool_ends
                .iter()
                .filter(|end| end.entry.is_some_and(|ended| std::ptr::eq(ended, *entry)))
                .map(ToolEnd::event),
        );
        let Some(message) = entry.model.as_ref().and_then(|model| model.first()) else {
            events.push(AgentEvent::EntryAppended {
                entry: (*entry).clone(),
            });
            continue;
        };
        let assistant = matches!(message, Message::Assistant(_));
        // A streamed answer already started with its first partial.
        let streamed = assistant && partial_before.is_some() && !assistant_appended;
        if assistant {
            assistant_appended = true;
        }
        if !streamed {
            events.push(AgentEvent::MessageStart {
                message: message.clone(),
            });
        }
        events.push(AgentEvent::MessageEnd {
            entry: (*entry).clone(),
        });
    }
    // Ends without a result entry: a faulted or orphaned tool, or one whose run ended.
    events.extend(
        tool_ends
            .iter()
            .filter(|end| end.entry.is_none())
            .map(ToolEnd::event),
    );

    // Compaction ends, task failures, then turn and run ends.
    let compactions_before = was.compactions();
    let compactions = now.compactions();
    let has_compaction = |list: &[JsonValue], task_id: &JsonValue| {
        list.iter().any(|status| status["taskId"] == *task_id)
    };
    for status in compactions_before {
        if !has_compaction(compactions, &status["taskId"]) {
            events.push(AgentEvent::CompactionEnd {
                task_id: decode(&status["taskId"]),
                reason: decode(&status["reason"]),
            });
        }
    }
    // A generation's turn ends when its outcome is committed: at a `completing`
    // hold or at terminal, whichever comes first, so a successor created at
    // the hold starts after it.
    let mut turn_ended = false;
    for task in &tasks {
        let status = task.state.status();
        let generation_task = task.kind == GENERATION_KIND;
        if generation_task && status == TaskStatus::Completing && held.insert(task.id) {
            turn_ended = true;
        }
        if status != TaskStatus::Terminal {
            continue;
        }
        if generation_task && !held.remove(&task.id) {
            turn_ended = true;
        }
        let message = match task.state.outcome() {
            Some(TaskOutcome::Faulted { error }) => Some(error.message.clone()),
            Some(TaskOutcome::Orphaned { reason }) => Some(reason.clone()),
            Some(
                TaskOutcome::Completed { .. }
                | TaskOutcome::Failed { .. }
                | TaskOutcome::Aborted { .. },
            )
            | None => None,
        };
        if let Some(message) = message {
            events.push(AgentEvent::TaskFailed {
                task_id: task.id,
                kind: task.kind.clone(),
                message,
            });
        }
    }
    if turn_ended {
        events.push(AgentEvent::TurnEnd);
    }
    let run = now.live("run");
    let run_before = was.live("run");
    let first_input = |run: Option<&JsonValue>| {
        get(run, "inputs")
            .and_then(|inputs| inputs.get_index(0))
            .cloned()
    };
    let run_changed = first_input(run) != first_input(run_before);
    if let Some(run_before) = run_before {
        if run_changed {
            events.push(AgentEvent::RunEnd {
                inputs: decode(&run_before["inputs"]),
            });
        }
    }

    // Submissions, document state, then what began.
    events.extend(submissions.iter().map(|record| AgentEvent::Submission {
        record: (*record).clone(),
    }));
    if !same(now.inbox, was.inbox) {
        events.push(AgentEvent::InboxUpdate {
            items: queued(now.inbox),
        });
    }
    // A retired document reads as its initial value, as in a snapshot.
    if !same(now.agent, was.agent) {
        events.push(AgentEvent::AgentChanged {
            agent: now.agent.map(decode).unwrap_or_default(),
        });
    }
    if !same(now.usage, was.usage) {
        events.push(AgentEvent::UsageChanged {
            usage: now.usage.map(decode).unwrap_or_default(),
        });
    }
    for status in compactions {
        if !has_compaction(compactions_before, &status["taskId"]) {
            events.push(AgentEvent::CompactionStart {
                task_id: decode(&status["taskId"]),
                reason: decode(&status["reason"]),
                blocking: status["blocking"].as_bool().unwrap_or_default(),
            });
        }
    }
    if let Some(run) = run {
        if run_changed {
            events.push(AgentEvent::RunStart {
                inputs: decode(&run["inputs"]),
            });
        }
        let task_id = &run["taskId"];
        if !same(Some(task_id), get(run_before, "taskId"))
            && task(decode(task_id)).is_some_and(|record| record.kind == GENERATION_KIND)
        {
            events.push(AgentEvent::TurnStart);
        }
    }
    events
}

/// `["docs", "pi.live", "generation", "message"]`.
fn partial_path() -> [Seg; 4] {
    [
        Seg::from("docs"),
        Seg::from("pi.live"),
        Seg::from("generation"),
        Seg::from("message"),
    ]
}

fn is_key(segment: Option<&Seg>, key: &str) -> bool {
    matches!(segment, Some(Seg::Key(other)) if &**other == key)
}

/// Translate the view operations on the in-flight message into message
/// changes (spec §9.4).
fn message_changes(view_ops: &[Op], message: &AssistantMessage) -> Vec<MessageChange> {
    let whole_message = || {
        vec![MessageChange::Message {
            message: message.clone(),
        }]
    };
    let partial_path = partial_path();
    let mut changes = Vec::new();
    // A block sent whole already holds every later change to it in this batch.
    let mut whole: HashSet<usize> = HashSet::new();
    for op in view_ops {
        // View operations never replace the root.
        let path = op.path();
        if !path.starts_with(&partial_path) {
            // The whole message or generation was replaced.
            if partial_path.starts_with(path) {
                return whole_message();
            }
            continue;
        }
        let rest = &path[partial_path.len()..];
        if is_key(rest.first(), "usage") {
            continue;
        }
        if !is_key(rest.first(), "content") {
            return whole_message();
        }
        if rest.len() == 1 {
            let Op::Splice(_, start, 0, items) = op else {
                return whole_message();
            };
            for (offset, item) in items.iter().enumerate() {
                let content_index = start + offset;
                let block: AssistantContentBlock = decode(item);
                changes.push(match item["type"].as_str() {
                    Some("text") => MessageChange::TextStart {
                        content_index,
                        block,
                    },
                    Some("thinking") => MessageChange::ThinkingStart {
                        content_index,
                        block,
                    },
                    _ => MessageChange::ToolcallStart {
                        content_index,
                        block,
                    },
                });
            }
            continue;
        }
        let Some(Seg::Index(content_index)) = rest.get(1) else {
            return whole_message();
        };
        let content_index = *content_index;
        let field = rest.get(2);
        if whole.contains(&content_index) {
            continue;
        }
        match op {
            Op::Append(_, delta) if rest.len() == 3 && is_key(field, "text") => {
                changes.push(MessageChange::TextDelta {
                    content_index,
                    delta: delta.clone(),
                });
            }
            Op::Append(_, delta) if rest.len() == 3 && is_key(field, "thinking") => {
                changes.push(MessageChange::ThinkingDelta {
                    content_index,
                    delta: delta.clone(),
                });
            }
            Op::Append(_, delta) if is_key(field, "arguments") => {
                changes.push(MessageChange::ToolcallDelta {
                    content_index,
                    path: rest[3..].iter().map(PathSegment::from).collect(),
                    delta: delta.clone(),
                });
            }
            Op::Replace(_)
            | Op::Set(..)
            | Op::Delete(_)
            | Op::Append(..)
            | Op::Truncate(..)
            | Op::Splice(..)
            | Op::Move(..) => {
                whole.insert(content_index);
                let Some(block) = message.content.get(content_index) else {
                    // The block no longer exists in this revision: the whole message carries the batch.
                    return whole_message();
                };
                changes.push(MessageChange::Block {
                    content_index,
                    block: block.clone(),
                });
            }
        }
    }
    changes
}

/// Nested slots by task ID, in list order.
fn nested_by_task(list: &[JsonValue]) -> Vec<(TaskId, &JsonValue)> {
    let mut slots: Vec<(TaskId, &JsonValue)> = Vec::new();
    for slot in list {
        let task_id: TaskId = decode(&slot["taskId"]);
        match slots.iter_mut().find(|(other, _)| *other == task_id) {
            Some(entry) => entry.1 = slot,
            None => slots.push((task_id, slot)),
        }
    }
    slots
}

/// Push the update event of a slot running before and after, if it changed.
fn push_update(
    events: &mut Vec<AgentEvent>,
    view_ops: &[Op],
    at: (&'static str, usize),
    slot: &JsonValue,
    previous: &JsonValue,
) {
    if !is_status(Some(slot), "running") || !is_status(Some(previous), "running") {
        return;
    }
    let Some((output, details, diagnostics)) = tool_update(view_ops, at, slot, previous) else {
        return;
    };
    events.push(AgentEvent::ToolExecutionUpdate {
        call: call_of(slot),
        output,
        details,
        diagnostics,
    });
}

type ToolUpdate = (
    Option<ToolOutputUpdate>,
    Option<JsonValue>,
    Option<Vec<ToolDiagnostic>>,
);

/// Output, details, and diagnostics changes of a running slot at `at` in
/// `pi.live` (`tools` or `nestedTools`, and its index), from the view
/// operations on it.
fn tool_update(
    view_ops: &[Op],
    (list, index): (&'static str, usize),
    slot: &JsonValue,
    previous: &JsonValue,
) -> Option<ToolUpdate> {
    let output_path = [
        Seg::from("docs"),
        Seg::from("pi.live"),
        Seg::from(list),
        Seg::from(index),
        Seg::from("output"),
    ];
    let mut trim_start = 0;
    let mut append = String::new();
    let mut set = false;
    for op in view_ops {
        if !op.path().starts_with(&output_path) {
            continue;
        }
        match op {
            Op::Truncate(_, count) => trim_start += count,
            Op::Append(_, text) => append.push_str(text),
            Op::Replace(_) | Op::Set(..) | Op::Delete(_) | Op::Splice(..) | Op::Move(..) => {
                set = true;
            }
        }
    }
    let output_now = slot.get("output");
    let output = if set
        || (!same(output_now, previous.get("output")) && trim_start == 0 && append.is_empty())
    {
        Some(ToolOutputUpdate::Set {
            set: output_now
                .and_then(JsonValue::as_str)
                .unwrap_or_default()
                .to_owned(),
        })
    } else if trim_start > 0 || !append.is_empty() {
        Some(ToolOutputUpdate::Window {
            trim_start: (trim_start > 0).then_some(trim_start),
            append: (!append.is_empty()).then_some(append),
        })
    } else {
        None
    };
    // A safe replay clears a running slot's progress: removed details send `null`, removed diagnostics `[]`.
    let details = (!same(slot.get("details"), previous.get("details")))
        .then(|| slot.get("details").cloned().unwrap_or(JsonValue::Null));
    let diagnostics = (!same(slot.get("diagnostics"), previous.get("diagnostics")))
        .then(|| slot.get("diagnostics").map(decode).unwrap_or_default());
    if output.is_none() && details.is_none() && diagnostics.is_none() {
        return None;
    }
    Some((output, details, diagnostics))
}
