//! Port of `test/session-support.ts`: memory storage with observable commits,
//! held calls, injected commit failures, and a Session over it.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, LazyLock, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::delta::Draft;
use eukhe_chord::json::{JsonObject, JsonValue};
use futures::future::BoxFuture;
use futures::FutureExt;
use tokio::sync::watch;

use crate::errors::StorageError;
use crate::session::{Session, SessionError, SessionResult, TaskDefinitionRef};
use crate::storage::MemoryStorage;
use crate::types::{
    AnyTaskRecord, CommitChange, CommitPublication, ConversationId, ConversationOwnership,
    ConversationQuery, ConversationRecord, Cursor, DocumentAddress, DocumentCommitChange,
    DocumentCopySource, DocumentId, DocumentPoint, DocumentQuery, DocumentRecord, EntryId,
    EntryQuery, EntryRecord, Page, Seq, Storage, StorageWrite, StoredDocument, StoredEntry,
    SubmissionId, SubmissionQuery, SubmissionRecord, TaskId, TaskQuery,
};

pub(crate) static CONTEXT: LazyLock<Context> = LazyLock::new(|| BACKGROUND_CONTEXT.clone());

/// The shared background context of every test.
pub(crate) fn context() -> &'static Context {
    &CONTEXT
}

/// A one-shot signal (TS deferred promise).
#[derive(Clone)]
pub(crate) struct Deferred {
    sender: Arc<watch::Sender<bool>>,
}

impl Deferred {
    pub(crate) fn new() -> Self {
        Self {
            sender: Arc::new(watch::channel(false).0),
        }
    }

    pub(crate) fn resolve(&self) {
        self.sender.send_replace(true);
    }

    pub(crate) fn wait(&self) -> impl std::future::Future<Output = ()> + Send + 'static {
        let mut receiver = self.sender.subscribe();
        async move {
            // The sender lives in `self`, which clones share.
            let _ = receiver.wait_for(|resolved| *resolved).await;
        }
    }
}

struct Held {
    gate: Deferred,
    entered: Deferred,
}

/// A gate that holds calls until released and reports when the first held
/// call arrives.
pub(crate) struct Gate {
    storage: Arc<ControlledStorage>,
    held: Arc<Held>,
    kind: GateKind,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum GateKind {
    Commit,
    Find,
}

impl Gate {
    pub(crate) fn entered(&self) -> impl std::future::Future<Output = ()> + Send + 'static {
        self.held.entered.wait()
    }

    pub(crate) fn release(&self) {
        let mut control = self.storage.control();
        let slot = match self.kind {
            GateKind::Commit => &mut control.commit_gate,
            GateKind::Find => &mut control.find_gate,
        };
        if slot
            .as_ref()
            .is_some_and(|held| Arc::ptr_eq(held, &self.held))
        {
            *slot = None;
        }
        drop(control);
        self.held.gate.resolve();
    }
}

#[derive(Default)]
struct Control {
    admitted_commits: Vec<Vec<StorageWrite>>,
    commits: Vec<Vec<StorageWrite>>,
    commit_gate: Option<Arc<Held>>,
    find_gate: Option<Arc<Held>>,
    commit_failure: Option<StorageError>,
}

/// Memory storage with observable commits, held calls, and injected commit
/// failures.
pub(crate) struct ControlledStorage {
    inner: MemoryStorage,
    control: Mutex<Control>,
    mint_count: AtomicUsize,
    document_read_count: AtomicUsize,
}

impl ControlledStorage {
    pub(crate) fn new() -> Arc<Self> {
        Arc::new(Self {
            inner: MemoryStorage::new(),
            control: Mutex::new(Control::default()),
            mint_count: AtomicUsize::new(0),
            document_read_count: AtomicUsize::new(0),
        })
    }

    fn control(&self) -> std::sync::MutexGuard<'_, Control> {
        self.control.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Batches admitted by Session (TS keeps the borrowed arrays; Rust keeps copies).
    pub(crate) fn admitted_commits(&self) -> Vec<Vec<StorageWrite>> {
        self.control().admitted_commits.clone()
    }

    /// Detached batches for value assertions.
    pub(crate) fn commits(&self) -> Vec<Vec<StorageWrite>> {
        self.control().commits.clone()
    }

    pub(crate) fn last_commit(&self) -> Vec<StorageWrite> {
        self.control()
            .commits
            .last()
            .cloned()
            .expect("a commit was admitted")
    }

    pub(crate) fn commit_count(&self) -> usize {
        self.control().commits.len()
    }

    pub(crate) fn mint_count(&self) -> usize {
        self.mint_count.load(Ordering::SeqCst)
    }

    pub(crate) fn document_read_count(&self) -> usize {
        self.document_read_count.load(Ordering::SeqCst)
    }

    pub(crate) fn hold_commits(self: &Arc<Self>) -> Gate {
        let held = Arc::new(Held {
            gate: Deferred::new(),
            entered: Deferred::new(),
        });
        self.control().commit_gate = Some(Arc::clone(&held));
        Gate {
            storage: Arc::clone(self),
            held,
            kind: GateKind::Commit,
        }
    }

    pub(crate) fn hold_find_document(self: &Arc<Self>) -> Gate {
        let held = Arc::new(Held {
            gate: Deferred::new(),
            entered: Deferred::new(),
        });
        self.control().find_gate = Some(Arc::clone(&held));
        Gate {
            storage: Arc::clone(self),
            held,
            kind: GateKind::Find,
        }
    }

    /// Simulate a crash during the held commit: it never reaches storage, and
    /// later commits proceed.
    pub(crate) fn crash(&self) {
        self.control().commit_gate = None;
    }

    pub(crate) fn fail_next_commit(&self, error: StorageError) {
        self.control().commit_failure = Some(error);
    }

    /// Reopen after `close()`, as a fresh process would reopen the same
    /// database, keeping every committed record.
    pub(crate) fn reopen(&self) -> &Self {
        self.inner.reopen();
        self
    }
}

impl Storage for ControlledStorage {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        async move {
            let held = {
                let mut control = self.control();
                control.admitted_commits.push(writes.to_vec());
                control.commits.push(writes.to_vec());
                control.commit_gate.clone()
            };
            if let Some(held) = held {
                held.entered.resolve();
                held.gate.wait().await;
            }
            if let Some(failure) = self.control().commit_failure.take() {
                return Err(failure);
            }
            self.inner.commit(writes, cx).await
        }
        .boxed()
    }

    fn mint_id(&self) -> BoxFuture<'_, Result<u64, StorageError>> {
        self.mint_count.fetch_add(1, Ordering::SeqCst);
        self.inner.mint_id()
    }

    fn conversation<'a>(
        &'a self,
        id: ConversationId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<ConversationRecord>, StorageError>> {
        self.inner.conversation(id, cx)
    }

    fn scan_conversations<'a>(
        &'a self,
        query: &'a ConversationQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<ConversationRecord>, StorageError>> {
        self.inner.scan_conversations(query, limit, cursor, cx)
    }

    fn entry<'a>(
        &'a self,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        self.inner.entry(id, cx)
    }

    fn entry_in<'a>(
        &'a self,
        conversation_id: ConversationId,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        self.inner.entry_in(conversation_id, id, cx)
    }

    fn find_latest_head_marker<'a>(
        &'a self,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<EntryRecord>, StorageError>> {
        self.inner
            .find_latest_head_marker(conversation_id, at_or_before_entry_id, cx)
    }

    fn scan_entries<'a>(
        &'a self,
        query: &'a EntryQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<EntryRecord>, StorageError>> {
        self.inner.scan_entries(query, limit, cursor, cx)
    }

    fn task<'a>(
        &'a self,
        id: TaskId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<AnyTaskRecord>, StorageError>> {
        self.inner.task(id, cx)
    }

    fn scan_tasks<'a>(
        &'a self,
        query: &'a TaskQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<AnyTaskRecord>, StorageError>> {
        self.inner.scan_tasks(query, limit, cursor, cx)
    }

    fn submission<'a>(
        &'a self,
        id: SubmissionId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        self.inner.submission(id, cx)
    }

    fn scan_submissions<'a>(
        &'a self,
        query: &'a SubmissionQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<SubmissionRecord>, StorageError>> {
        self.inner.scan_submissions(query, limit, cursor, cx)
    }

    fn submission_by_request<'a>(
        &'a self,
        conversation_id: ConversationId,
        request_id: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        self.inner
            .submission_by_request(conversation_id, request_id, cx)
    }

    fn find_document<'a>(
        &'a self,
        address: &'a DocumentAddress,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<DocumentRecord>, StorageError>> {
        async move {
            let held = self.control().find_gate.clone();
            if let Some(held) = held {
                held.entered.resolve();
                held.gate.wait().await;
            }
            self.inner.find_document(address, at, cx).await
        }
        .boxed()
    }

    fn document<'a>(
        &'a self,
        id: DocumentId,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredDocument>, StorageError>> {
        self.document_read_count.fetch_add(1, Ordering::SeqCst);
        self.inner.document(id, at, cx)
    }

    fn scan_documents<'a>(
        &'a self,
        query: &'a DocumentQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<DocumentRecord>, StorageError>> {
        self.inner.scan_documents(query, limit, cursor, cx)
    }

    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>> {
        self.inner.close(cx)
    }
}

/// Every committed publication a test Session delivered.
#[derive(Clone, Default)]
pub(crate) struct Publications(Arc<Mutex<Vec<CommitPublication>>>);

impl Publications {
    pub(crate) fn len(&self) -> usize {
        self.0.lock().unwrap_or_else(PoisonError::into_inner).len()
    }

    pub(crate) fn last(&self) -> CommitPublication {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .last()
            .cloned()
            .expect("a commit was published")
    }
}

/// Session kernel plus its controlled storage and every committed publication.
pub(crate) struct TestSession {
    pub(crate) storage: Arc<ControlledStorage>,
    pub(crate) session: Session,
    pub(crate) publications: Publications,
}

pub(crate) fn open_test_session() -> TestSession {
    let storage = ControlledStorage::new();
    let session = Session::new(Arc::clone(&storage) as Arc<dyn Storage>);
    let publications = Publications::default();
    let sink = publications.clone();
    // The listener stays registered for the Session's lifetime.
    drop(
        session
            .subscribe_commits(Arc::new(move |publication, _cx| {
                sink.0
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(publication.clone());
            }))
            .expect("a fresh Session accepts listeners"),
    );
    TestSession {
        storage,
        session,
        publications,
    }
}

/// One `type: "document"` publication change.
#[derive(Clone, Debug)]
pub(crate) struct DocumentChange {
    pub(crate) record: DocumentRecord,
    pub(crate) conversation_id: Option<ConversationId>,
    pub(crate) version: Option<u64>,
    pub(crate) value: Option<Arc<JsonObject>>,
    pub(crate) ops: crate::session::Ops,
}

/// One `type: "document.copy"` publication change.
#[derive(Clone, Debug)]
pub(crate) struct DocumentCopyChange {
    pub(crate) record: DocumentRecord,
    pub(crate) conversation_id: ConversationId,
    pub(crate) source: DocumentCopySource,
}

pub(crate) fn document_changes(publication: &CommitPublication) -> Vec<DocumentChange> {
    publication
        .changes
        .iter()
        .filter_map(|change| match change {
            CommitChange::Document(DocumentCommitChange::Document {
                record,
                conversation_id,
                version,
                value,
                ops,
            }) => Some(DocumentChange {
                record: record.clone(),
                conversation_id: *conversation_id,
                version: *version,
                value: value.clone(),
                ops: Arc::clone(ops),
            }),
            _ => None,
        })
        .collect()
}

pub(crate) fn document_copy_changes(publication: &CommitPublication) -> Vec<DocumentCopyChange> {
    publication
        .changes
        .iter()
        .filter_map(|change| match change {
            CommitChange::Document(DocumentCommitChange::Copy {
                record,
                conversation_id,
                source,
            }) => Some(DocumentCopyChange {
                record: record.clone(),
                conversation_id: *conversation_id,
                source: *source,
            }),
            _ => None,
        })
        .collect()
}

/// Create one conversation and return its ID.
pub(crate) async fn create_conversation(session: &Session) -> ConversationId {
    session
        .commit(
            |tx| async move {
                Ok(tx
                    .create_conversation(ConversationOwnership::Ownerless)
                    .await?
                    .id)
            },
            context(),
        )
        .await
        .expect("conversation creation commits")
}

/// Resolve after pending tasks have run (TS: pending microtasks and one
/// macrotask turn). Tests run on the current-thread runtime, so yielding
/// repeatedly drains every runnable task deterministically.
pub(crate) async fn flush() {
    for _ in 0..64 {
        tokio::task::yield_now().await;
    }
}

/// Parse a JSON literal.
pub(crate) fn json(text: &str) -> JsonValue {
    JsonValue::parse(text).expect("valid JSON literal")
}

/// Parse a JSON object literal.
pub(crate) fn object(text: &str) -> Arc<JsonObject> {
    match json(text) {
        JsonValue::Object(object) => object,
        other => panic!("not an object literal: {other}"),
    }
}

/// The `"r"`/`"s"`… JSON form of committed ops.
pub(crate) fn ops_json(ops: &[eukhe_chord::delta::Op]) -> JsonValue {
    ops.iter().map(eukhe_chord::delta::Op::to_json).collect()
}

/// A test error raised by a commit callback.
pub(crate) fn fail<T>(message: &str) -> SessionResult<T> {
    Err(SessionError::error(message.to_owned()))
}

/// `draft[key]` as a child draft.
pub(crate) fn child(draft: &Draft, key: &str) -> Draft {
    draft.child(key).expect("container child")
}

/// The `test.work` task definition of the TS tests.
pub(crate) struct WorkTask;

impl TaskDefinitionRef for WorkTask {
    fn name(&self) -> &'static str {
        "test.work"
    }

    fn version(&self) -> u64 {
        1
    }

    fn initial(&self, _input: &JsonValue) -> SessionResult<JsonValue> {
        Ok(json(r#"{"phase":"start"}"#))
    }
}

pub(crate) fn work_task() -> Arc<dyn TaskDefinitionRef> {
    Arc::new(WorkTask)
}

/// Assert that `result` failed with a message containing `expected`.
#[track_caller]
pub(crate) fn assert_error<T: std::fmt::Debug>(result: SessionResult<T>, expected: &str) {
    match result {
        Ok(value) => panic!("expected an error containing {expected:?}, got Ok({value:?})"),
        Err(error) => {
            let message = error.to_string();
            assert!(
                message.contains(expected),
                "expected an error containing {expected:?}, got {message:?}"
            );
        }
    }
}
