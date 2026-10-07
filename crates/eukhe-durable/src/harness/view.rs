//! Conversation view mounts (`harness/view.ts`, spec §9.3): one
//! conversation's active transcript and built-in documents, built lazily on
//! the Session line and advanced from the Session's commit publications.

use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};

use eukhe_chord::context::{without_abort_signal, Context};
use eukhe_chord::delta::{apply_immutable, Op, Path, Seg};
use eukhe_chord::json::{to_json, JsonObject, JsonValue};
use eukhe_chord::{
    replicated_state_from_source, AttachedReplicatedState, ReplicatedStateSourceOptions,
};
use futures::future::{BoxFuture, FutureExt};

use crate::harness::agent::AGENT_DOC;
use crate::harness::context::{active_entries, capture_context_bounds};
use crate::harness::inbox::INBOX_DOC;
use crate::harness::live::LIVE_DOC;
use crate::harness::provider::PROVIDER_DOC;
use crate::harness::usage::USAGE_DOC;
use crate::harness::util::closed_error;
use crate::session::{
    CommittedStateSource, CommittedWatch, ObservedValue, OnLineDocument, Ops, Session,
    SessionError, SessionResult,
};
use crate::types::{
    CommitChange, CommitPublication, ConversationId, ConversationRecord, DocumentCommitChange,
    DocumentId, EntryRecord, Storage,
};

/// Kinds of the mounted built-in documents, in mount order.
const MOUNTED_KINDS: [&str; 5] = ["pi.agent", "pi.live", "pi.inbox", "pi.provider", "pi.usage"];

/// Structural mount of one conversation's active transcript and built-in
/// documents (spec §9.3). Clones share every part; [`ObservedValue::to_json`]
/// is the TS object `{ conversation, entries, docs }`, shared between clones.
#[derive(Clone, Debug)]
pub struct ConversationView {
    conversation: Arc<ConversationRecord>,
    entries: Arc<Vec<EntryRecord>>,
    entries_json: JsonValue,
    docs: Arc<JsonObject>,
    json: JsonValue,
}

impl ConversationView {
    fn new(
        conversation: Arc<ConversationRecord>,
        conversation_json: JsonValue,
        entries: Arc<Vec<EntryRecord>>,
        entries_json: JsonValue,
        docs: Arc<JsonObject>,
    ) -> Self {
        let mut root = JsonObject::with_capacity(3);
        root.insert("conversation", conversation_json);
        root.insert("entries", entries_json.clone());
        root.insert("docs", JsonValue::Object(Arc::clone(&docs)));
        Self {
            conversation,
            entries,
            entries_json,
            docs,
            json: JsonValue::Object(Arc::new(root)),
        }
    }

    /// The conversation's record.
    #[must_use]
    pub fn conversation(&self) -> &ConversationRecord {
        &self.conversation
    }

    /// Raw active entries, as `ContextView.entries`: the head marker, then the
    /// non-head entries from its head.
    #[must_use]
    pub fn entries(&self) -> &Arc<Vec<EntryRecord>> {
        &self.entries
    }

    /// Built-in conversation documents keyed by kind; absent documents are absent.
    #[must_use]
    pub fn docs(&self) -> &Arc<JsonObject> {
        &self.docs
    }

    /// One built-in document, or `None` when absent.
    #[must_use]
    pub fn doc(&self, kind: &str) -> Option<&JsonValue> {
        self.docs.get(kind)
    }

    /// The view's JSON, `{ conversation, entries, docs }`; clones of one
    /// revision share it.
    #[must_use]
    pub fn to_json_value(&self) -> JsonValue {
        self.json.clone()
    }

    fn conversation_json(&self) -> JsonValue {
        self.json["conversation"].clone()
    }
}

/// Deep equality of the view's JSON (TS `toEqual`).
impl PartialEq for ConversationView {
    fn eq(&self, other: &Self) -> bool {
        self.json == other.json
    }
}

impl ObservedValue for ConversationView {
    fn is_retirement(&self) -> bool {
        false
    }

    fn to_json(&self) -> JsonValue {
        self.json.clone()
    }
}

/// Serialized exact-frame watch of one conversation's view.
pub type ConversationWatch = CommittedWatch<ConversationView>;

/// Receives each next revision of a mount, and the Session's close.
///
/// Implementations must not block or call Session operations: every method
/// runs synchronously inside the Session's commit or close listener.
pub(crate) trait ViewObserver: Send + Sync {
    /// The next revision and the mount's operations that produced it.
    fn advance(&self, _value: &ConversationView, _ops: &Ops, _cx: &Context) {}

    /// Every publication, after the mount took it; `ops` are the mount's,
    /// possibly none.
    fn publication(
        &self,
        _before: &ConversationView,
        _after: &ConversationView,
        _ops: &Ops,
        _publication: &CommitPublication,
        _cx: &Context,
    ) {
    }

    /// The Session began closing.
    fn close_session(&self);
}

impl ViewObserver for CommittedStateSource {
    fn advance(&self, value: &ConversationView, ops: &Ops, cx: &Context) {
        CommittedStateSource::advance(self, value, Arc::clone(ops), cx.clone());
    }

    fn close_session(&self) {
        CommittedStateSource::close_session(self);
    }
}

impl ViewObserver for CommittedWatch<ConversationView> {
    fn advance(&self, value: &ConversationView, ops: &Ops, cx: &Context) {
        CommittedWatch::advance(self, value.clone(), Arc::clone(ops), cx.clone());
    }

    fn close_session(&self) {
        CommittedWatch::close_session(self);
    }
}

/// Drops one observer, and the mount with its last observer. Idempotent.
pub(crate) type Detach = Arc<dyn Fn() + Send + Sync>;

/// Creates an observer from the current revision, on the Session line:
/// `(value, release, storage)`; `release` detaches it.
pub(crate) type CreateObserver<O> = Box<
    dyn FnOnce(
            ConversationView,
            Box<dyn FnOnce() + Send>,
            Arc<dyn Storage>,
        ) -> BoxFuture<'static, SessionResult<O>>
        + Send,
>;

/// Mounted incarnation and definition version of one document kind; another
/// incarnation or version is set whole.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Incarnation {
    id: DocumentId,
    version: Option<u64>,
}

/// One conversation's mount: its current revision, the document incarnations
/// it shows, and its observers.
struct Mount {
    value: ConversationView,
    docs: HashMap<String, Incarnation>,
    observers: Vec<(u64, Arc<dyn ViewObserver>)>,
}

type SharedMount = Arc<Mutex<Mount>>;

struct ViewsState {
    mounts: BTreeMap<ConversationId, SharedMount>,
    closed: bool,
    next_observer: u64,
}

struct Inner {
    session: Session,
    storage: Arc<dyn Storage>,
    state: Mutex<ViewsState>,
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The Harness's conversation view mounts: at most one per conversation,
/// built on the Session line by its first observer and dropped with its last.
/// Each mount advances from the Session's commit publications, which are
/// durable.
#[derive(Clone)]
pub(crate) struct ConversationViews {
    inner: Arc<Inner>,
}

impl ConversationViews {
    pub(crate) fn new(session: Session, storage: Arc<dyn Storage>) -> Self {
        Self {
            inner: Arc::new(Inner {
                session,
                storage,
                state: Mutex::new(ViewsState {
                    mounts: BTreeMap::new(),
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
                    inner.publish(publication, cx);
                }
            }))?;
        // The subscription lives as long as the Session; dropping the handle keeps it.
        drop(commits);
        let weak = Arc::downgrade(&self.inner);
        let close = self.inner.session.subscribe_close(Arc::new(move || {
            if let Some(inner) = weak.upgrade() {
                inner.close();
            }
        }))?;
        drop(close);
        Ok(())
    }

    /// A disposable read-only Chord state of the view.
    pub(crate) fn state(
        &self,
        id: ConversationId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<AttachedReplicatedState>> {
        let attached = self.attach(
            id,
            Box::new(|value, release, _storage| {
                async move { Ok(CommittedStateSource::new(&value, release)) }.boxed()
            }),
            cx,
        );
        async move {
            let (source, detach) = attached.await?;
            replicated_state_from_source(&source, ReplicatedStateSourceOptions::default()).map_err(
                |error| {
                    detach();
                    SessionError::other(error)
                },
            )
        }
        .boxed()
    }

    /// A serialized exact-frame watch of the view; cancelling `cx` stops it.
    pub(crate) fn watch(
        &self,
        id: ConversationId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<ConversationWatch>> {
        let attached = self.attach(
            id,
            Box::new(|value, release, _storage| {
                async move { Ok(CommittedWatch::new(value, release, None)) }.boxed()
            }),
            cx,
        );
        let signal = cx.abort_signal();
        async move {
            let (watch, _detach) = attached.await?;
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
    /// the Session line: it sees every later publication and nothing earlier.
    /// `create` may read committed Storage, still on the line. The returned
    /// detach drops it, and the mount with its last observer.
    pub(crate) fn attach<O>(
        &self,
        id: ConversationId,
        create: CreateObserver<O>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<(O, Detach)>>
    where
        O: ViewObserver + Clone + 'static,
    {
        let inner = Arc::clone(&self.inner);
        let cx = cx.clone();
        self.inner
            .session
            .read_on_line(async move { Inner::attach(&inner, id, create, &cx).await })
            .boxed()
    }
}

impl Inner {
    fn lock(&self) -> MutexGuard<'_, ViewsState> {
        lock(&self.state)
    }

    async fn attach<O>(
        this: &Arc<Self>,
        id: ConversationId,
        create: CreateObserver<O>,
        cx: &Context,
    ) -> SessionResult<(O, Detach)>
    where
        O: ViewObserver + Clone + 'static,
    {
        let existing = this.lock().mounts.get(&id).cloned();
        let mount = match existing {
            Some(mount) => mount,
            None => Arc::new(Mutex::new(this.build(id, cx).await?)),
        };
        let observer_id = {
            let mut state = this.lock();
            state.next_observer += 1;
            state.next_observer
        };
        let detach: Detach = {
            let views = Arc::downgrade(this);
            let mount = Arc::clone(&mount);
            Arc::new(move || detach_observer(&views, id, &mount, observer_id))
        };
        let release = {
            let detach = Arc::clone(&detach);
            Box::new(move || detach()) as Box<dyn FnOnce() + Send>
        };
        let value = lock(&mount).value.clone();
        let observer = create(value, release, Arc::clone(&this.storage)).await?;
        // Close or cancellation may begin while the mount hydrates; register nothing then.
        let mut mounted = lock(&mount);
        {
            let mut state = this.lock();
            if state.closed {
                return Err(closed_error());
            }
            if let Some(reason) = cx.abort_signal().and_then(|signal| signal.reason()) {
                return Err(SessionError::Aborted(reason));
            }
            state.mounts.insert(id, Arc::clone(&mount));
        }
        mounted.observers.push((
            observer_id,
            Arc::new(observer.clone()) as Arc<dyn ViewObserver>,
        ));
        drop(mounted);
        Ok((observer, detach))
    }

    async fn build(&self, id: ConversationId, cx: &Context) -> SessionResult<Mount> {
        let storage = &*self.storage;
        let Some(conversation) = storage.conversation(id, cx).await? else {
            return Err(SessionError::error(format!(
                "Conversation {id} does not exist"
            )));
        };
        let bounds = capture_context_bounds(storage, id, cx, None).await?;
        let entries = active_entries(storage, id, bounds.as_ref(), cx).await?;
        let session = &self.session;
        let loaded: [(&str, Option<OnLineDocument>); 5] = [
            (
                "pi.agent",
                session
                    .conversation_document_on_line(&AGENT_DOC, id, cx)
                    .await?,
            ),
            (
                "pi.live",
                session
                    .conversation_document_on_line(&LIVE_DOC, id, cx)
                    .await?,
            ),
            (
                "pi.inbox",
                session
                    .conversation_document_on_line(&INBOX_DOC, id, cx)
                    .await?,
            ),
            (
                "pi.provider",
                session
                    .conversation_document_on_line(&PROVIDER_DOC, id, cx)
                    .await?,
            ),
            (
                "pi.usage",
                session
                    .conversation_document_on_line(&USAGE_DOC, id, cx)
                    .await?,
            ),
        ];
        let mut docs = JsonObject::new();
        let mut incarnations = HashMap::new();
        for (kind, document) in loaded {
            let Some(document) = document else {
                continue;
            };
            docs.insert(kind, JsonValue::Object(document.value));
            incarnations.insert(
                kind.to_owned(),
                Incarnation {
                    id: document.record.id,
                    version: Some(document.version),
                },
            );
        }
        let conversation_json = to_json(&conversation)?;
        let entries_json =
            JsonValue::Array(Arc::new(entries.iter().map(entry_json).collect::<Vec<_>>()));
        Ok(Mount {
            value: ConversationView::new(
                Arc::new(conversation),
                conversation_json,
                Arc::new(entries),
                entries_json,
                Arc::new(docs),
            ),
            docs: incarnations,
            observers: Vec::new(),
        })
    }

    /// Advance every mount from one publication.
    fn publish(&self, publication: &CommitPublication, cx: &Context) {
        let mounts: Vec<_> = self
            .lock()
            .mounts
            .iter()
            .map(|(id, mount)| (*id, Arc::clone(mount)))
            .collect();
        for (id, mount) in mounts {
            advance(id, &mount, publication, cx);
        }
    }

    fn close(&self) {
        let mounts = {
            let mut state = self.lock();
            state.closed = true;
            std::mem::take(&mut state.mounts)
        };
        for mount in mounts.into_values() {
            let observers: Vec<_> = lock(&mount)
                .observers
                .iter()
                .map(|(_, observer)| Arc::clone(observer))
                .collect();
            for observer in observers {
                observer.close_session();
            }
        }
    }
}

fn detach_observer(views: &Weak<Inner>, id: ConversationId, mount: &SharedMount, observer: u64) {
    let mut mounted = lock(mount);
    mounted.observers.retain(|(other, _)| *other != observer);
    if !mounted.observers.is_empty() {
        return;
    }
    let Some(views) = views.upgrade() else {
        return;
    };
    let mut state = views.lock();
    if state
        .mounts
        .get(&id)
        .is_some_and(|current| Arc::ptr_eq(current, mount))
    {
        state.mounts.remove(&id);
    }
}

/// The JSON of a committed entry record.
fn entry_json(entry: &EntryRecord) -> JsonValue {
    // Committed entry records were validated as JSON when they were written.
    to_json(entry).expect("committed entry records are JSON")
}

/// Derive the mount's operations from one publication, apply them, and hand
/// the revision to every observer.
#[expect(
    clippy::too_many_lines,
    reason = "one-to-one port of the TS `advance`, entry and document branches in commit order"
)]
fn advance(id: ConversationId, mount: &SharedMount, publication: &CommitPublication, cx: &Context) {
    let (before, after, ops, observers) = {
        let mut mounted = lock(mount);
        let mut doc_ops: Vec<Op> = Vec::new();
        let mut entry_ops: Vec<Op> = Vec::new();
        let mut entries: Option<(Vec<EntryRecord>, Vec<JsonValue>)> = None;
        // Entry writes are published in ID order.
        for change in &publication.changes {
            match change {
                CommitChange::Entry(entry) if entry.conversation_id == id => {
                    let (list, json) = entries.get_or_insert_with(|| {
                        (
                            mounted.value.entries.as_ref().clone(),
                            mounted
                                .value
                                .entries_json
                                .as_array()
                                .unwrap_or_default()
                                .to_vec(),
                        )
                    });
                    let value = entry_json(entry);
                    let Some(target) = entry.head else {
                        entry_ops.push(Op::Splice(
                            vec![Seg::from("entries")],
                            list.len(),
                            0,
                            vec![value.clone()],
                        ));
                        list.push(entry.clone());
                        json.push(value);
                        continue;
                    };
                    // A head marker keeps the non-head entries from its head,
                    // which are always a suffix, and goes in front.
                    let kept = list
                        .iter()
                        .position(|candidate| candidate.head.is_none() && candidate.id >= target)
                        .unwrap_or(list.len());
                    entry_ops.push(Op::Splice(
                        vec![Seg::from("entries")],
                        0,
                        kept,
                        vec![value.clone()],
                    ));
                    list.splice(0..kept, [entry.clone()]);
                    json.splice(0..kept, [value]);
                }
                CommitChange::Document(DocumentCommitChange::Document {
                    record,
                    conversation_id,
                    version,
                    value,
                    ops,
                }) if *conversation_id == Some(id) => {
                    let kind = record.kind.as_str();
                    if !MOUNTED_KINDS.contains(&kind) || record.key.is_some() {
                        continue;
                    }
                    let path: Path = vec![Seg::from("docs"), Seg::from(kind)];
                    let mounted_incarnation = mounted.docs.get(kind).copied();
                    match value {
                        None => {
                            if mounted_incarnation.map(|mounted| mounted.id) != Some(record.id) {
                                continue;
                            }
                            mounted.docs.remove(kind);
                            doc_ops.push(Op::Delete(path));
                        }
                        Some(value) => {
                            let incarnation = Incarnation {
                                id: record.id,
                                version: *version,
                            };
                            if mounted_incarnation == Some(incarnation) {
                                doc_ops.extend(ops.iter().map(|op| prefixed(op, &path)));
                            } else {
                                mounted.docs.insert(kind.to_owned(), incarnation);
                                doc_ops.push(Op::Set(path, JsonValue::Object(Arc::clone(value))));
                            }
                        }
                    }
                }
                CommitChange::Entry(_)
                | CommitChange::Document(_)
                | CommitChange::Conversation(_)
                | CommitChange::Task(_)
                | CommitChange::Submission(_) => {}
            }
        }
        let before = mounted.value.clone();
        let ops: Ops = doc_ops.iter().chain(&entry_ops).cloned().collect();
        if !ops.is_empty() {
            let docs = if doc_ops.is_empty() {
                Arc::clone(&before.docs)
            } else {
                apply_docs(&before.docs, &doc_ops)
            };
            let (entries, entries_json) = match entries {
                Some((list, json)) => (Arc::new(list), JsonValue::Array(Arc::new(json))),
                None => (Arc::clone(&before.entries), before.entries_json.clone()),
            };
            mounted.value = ConversationView::new(
                Arc::clone(&before.conversation),
                before.conversation_json(),
                entries,
                entries_json,
                docs,
            );
        }
        let observers: Vec<_> = mounted
            .observers
            .iter()
            .map(|(_, observer)| Arc::clone(observer))
            .collect();
        (before, mounted.value.clone(), ops, observers)
    };
    let frame_cx = without_abort_signal(cx);
    if !ops.is_empty() {
        for observer in &observers {
            observer.advance(&after, &ops, &frame_cx);
        }
    }
    for observer in &observers {
        observer.publication(&before, &after, &ops, publication, &frame_cx);
    }
}

/// Apply document operations under `docs` to the mounted documents.
fn apply_docs(docs: &Arc<JsonObject>, ops: &[Op]) -> Arc<JsonObject> {
    let mut root = JsonObject::with_capacity(1);
    root.insert("docs", JsonValue::Object(Arc::clone(docs)));
    // Committed document operations apply to the committed revision the mount holds.
    let next = apply_immutable(&JsonValue::Object(Arc::new(root)), ops)
        .expect("committed document operations apply to the mounted documents");
    match &next["docs"] {
        JsonValue::Object(docs) => Arc::clone(docs),
        JsonValue::Null
        | JsonValue::Bool(_)
        | JsonValue::Number(_)
        | JsonValue::String(_)
        | JsonValue::Array(_) => {
            unreachable!("operations under `docs/<kind>` keep `docs` an object")
        }
    }
}

/// `op` moved under `prefix`; a root replacement becomes a set of the prefix.
pub(crate) fn prefixed(op: &Op, prefix: &[Seg]) -> Op {
    let at = |path: &Path| -> Path { prefix.iter().chain(path).cloned().collect() };
    match op {
        Op::Replace(value) => Op::Set(prefix.to_vec(), value.clone()),
        Op::Splice(path, start, deleted, items) => {
            Op::Splice(at(path), *start, *deleted, items.clone())
        }
        Op::Move(path, order) => Op::Move(at(path), order.clone()),
        Op::Set(path, value) => Op::Set(at(path), value.clone()),
        Op::Delete(path) => Op::Delete(at(path)),
        Op::Append(path, text) => Op::Append(at(path), text.clone()),
        Op::Truncate(path, count) => Op::Truncate(at(path), *count),
    }
}

impl crate::harness::Conversation {
    /// A disposable read-only Chord state of this conversation's view.
    #[must_use = "the state is attached only when the future runs"]
    pub fn view_state(
        &self,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<AttachedReplicatedState>> {
        self.core().views().state(self.id(), cx)
    }

    /// A serialized exact-frame watch of this conversation's view; cancelling
    /// `cx` stops it.
    #[must_use = "the watch is attached only when the future runs"]
    pub fn watch(&self, cx: &Context) -> BoxFuture<'static, SessionResult<ConversationWatch>> {
        self.core().views().watch(self.id(), cx)
    }
}
