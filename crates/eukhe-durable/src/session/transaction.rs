//! Transaction for one Session commit callback.
//!
//! Every asynchronous operation runs eagerly as a tracked task, so callback
//! settlement can reject and drain unfinished work. Session calls one
//! settlement method, then either discards prepared changes or adopts them
//! once after Storage succeeds.

use std::collections::{HashMap, HashSet};
use std::future::Future;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::Context;
use eukhe_chord::delta::{track, Change, Draft, Op, Prepared, Tracker};
use eukhe_chord::json::{JsonObject, JsonValue};
use futures::future::{BoxFuture, FutureExt, Shared};
use tokio::sync::watch;

use crate::documents::{
    address_id, check_record_scope, check_record_version, document_create,
    materialize_document_value, resolve_token_address, AnyDocDefinition, DocToken, FamilyDocToken,
    ResolvedAddress, SingletonDocToken,
};
use crate::entries::Entry;
use crate::errors::ReadAfterWrite;
use crate::types::{
    AnyTaskRecord, CheckpointInfo, ConversationId, ConversationOwner, ConversationOwnership,
    ConversationParent, ConversationQuery, ConversationRecord, Cursor, DocumentAddress,
    DocumentBase, DocumentCommitChange, DocumentContent, DocumentCopySource, DocumentCreate,
    DocumentFork, DocumentId, DocumentIdentity, DocumentPoint, DocumentQuery, DocumentRecord,
    DocumentRecordScope, DocumentScope, EntryData, EntryDraft, EntryHead, EntryId, EntryQuery,
    EntryRecord, Page, Seq, Storage, StorageWrite, SubmissionCreate, SubmissionId,
    SubmissionRecord, SubmissionSettlement, TaskId, TaskOptions, TaskOwnership, TaskQuery,
    TaskState, TaskStatus, TypedEntry, TypedEntryDraft, ROOT_CONVERSATION_ID,
};

use super::error::{SessionError, SessionResult};
use super::forks::prepare_fork_document_copies;
use super::observation::Ops;
use super::plans::{
    apply_submission_change, plan_document, publishes, DocumentPlan, PlanRecord, SubmissionChange,
};

/// Erased executable task definition `tx.create_task()` needs: the persisted
/// kind and version and the first checkpoint.
///
/// The harness implements this for its typed task definitions. `initial` runs
/// once per created task, before an ID is minted; an error fails the call.
pub trait TaskDefinitionRef: Send + Sync {
    /// Registered task kind persisted in `AnyTaskRecord.kind`.
    fn name(&self) -> &str;
    /// Definition version persisted with live input and checkpoints.
    fn version(&self) -> u64;
    /// First durable checkpoint for a newly created task.
    ///
    /// # Errors
    ///
    /// The definition's own failure, propagated to `tx.create_task()`.
    fn initial(&self, input: &JsonValue) -> SessionResult<JsonValue>;
}

const INTERNAL_SCAN_PAGE_SIZE: usize = 256;

fn empty_operations() -> Ops {
    Arc::from(Vec::<Op>::new())
}

/// One committed document incarnation owned by the Session tracker cache.
pub(crate) struct LoadedDocument {
    pub(crate) address_id: String,
    pub(crate) record: DocumentRecord,
    /// Persisted definition version; older while the tracked value is migrated only in memory.
    stored_version: AtomicU64,
    /// Definition version whose shape the tracked value has; access with another version reloads from Storage.
    pub(crate) value_version: u64,
    /// Stored deltas after the newest base; advanced by adoption so the next predicate call needs no read.
    deltas_since_base: AtomicU64,
    pub(crate) tracker: Tracker,
}

impl LoadedDocument {
    pub(crate) fn new(
        address_id: String,
        record: DocumentRecord,
        stored_version: u64,
        value_version: u64,
        deltas_since_base: u64,
        tracker: Tracker,
    ) -> Self {
        Self {
            address_id,
            record,
            stored_version: AtomicU64::new(stored_version),
            value_version,
            deltas_since_base: AtomicU64::new(deltas_since_base),
            tracker,
        }
    }

    // Mutated only on the Session mutation line; the atomics only make the
    // shared cache entry `Sync`.
    pub(crate) fn stored_version(&self) -> u64 {
        self.stored_version.load(Ordering::Relaxed)
    }

    pub(crate) fn deltas_since_base(&self) -> u64 {
        self.deltas_since_base.load(Ordering::Relaxed)
    }

    /// Current tracked value.
    pub(crate) fn value(&self) -> Arc<JsonObject> {
        object_value(&self.tracker.value())
    }
}

/// The root object of a tracked document value. Document trackers are only
/// created from definition objects, so the root is always an object.
pub(crate) fn object_value(value: &JsonValue) -> Arc<JsonObject> {
    match value {
        JsonValue::Object(object) => Arc::clone(object),
        JsonValue::Null
        | JsonValue::Bool(_)
        | JsonValue::Number(_)
        | JsonValue::String(_)
        | JsonValue::Array(_) => {
            unreachable!("document trackers are created from JSON objects")
        }
    }
}

/// Erased document definition shared by a transaction and the cache.
pub(crate) type Definition = Arc<dyn AnyDocDefinition>;

/// Session services used by a transaction while it holds the mutation line.
pub(crate) trait TransactionHost: Send + Sync {
    fn storage(&self) -> &Arc<dyn Storage>;
    /// Wall clock for task lifecycle times.
    fn now(&self) -> f64;
    /// The cached current incarnation without loading.
    fn cached(&self, address_id: &str) -> Option<Arc<LoadedDocument>>;
    /// The cached current incarnation, cold-loading and migrating it when necessary.
    fn load(
        &self,
        definition: Definition,
        address_id: String,
        address: DocumentAddress,
        cx: Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<LoadedDocument>>>>;
    /// Install a newly committed incarnation.
    fn install(&self, document: LoadedDocument);
    /// Remove a retired incarnation if it is still the cached occupant of its address.
    fn evict(&self, address_id: &str, record_id: DocumentId);
    /// Stage writes that belong to every newly created or forked conversation,
    /// in its creating transaction.
    fn conversation_created(
        &self,
        tx: Tx,
        record: ConversationRecord,
    ) -> BoxFuture<'static, SessionResult<()>>;
}

type TaskRead = Shared<BoxFuture<'static, SessionResult<Option<AnyTaskRecord>>>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TaskWriteKind {
    Create,
    Replace,
}

/// Committed and candidate state for one task touched by this transaction.
#[derive(Default)]
struct TransactionTask {
    committed_read: Option<TaskRead>,
    write: Option<(TaskWriteKind, AnyTaskRecord)>,
    publication_conversation_id: Option<ConversationId>,
}

/// Defaults a commit binds to: `tx.create_task()` conversation and the task
/// attributed to appended entries.
#[derive(Clone, Copy, Debug, Default)]
pub struct TransactionScope {
    pub conversation_id: Option<ConversationId>,
    /// Task whose runtime commit this is; stamped as `byTaskId` on appended entries.
    pub task_id: Option<TaskId>,
}

/// Storage/cache provenance of one staged document incarnation.
#[derive(Clone)]
pub(super) enum DocumentTarget {
    Loaded(Arc<LoadedDocument>),
    Created {
        record: DocumentCreate,
        version: u64,
        tracker: Tracker,
    },
    ForkCopy {
        record: DocumentCreate,
        source: DocumentCopySource,
    },
    RetireOnly(DocumentRecord),
}

type DraftFuture = Shared<BoxFuture<'static, SessionResult<Draft>>>;

/// One document incarnation acquired, created, or retired by this transaction.
pub(super) struct DocumentEntry {
    pub(super) address_id: String,
    pub(super) address: DocumentAddress,
    /// Absent for definition-free fork copies and retirement entries
    /// discovered by a terminal-task scan.
    pub(super) definition: Option<Definition>,
    /// Memoized public acquisition; absent for metadata-only retirement.
    pub(super) draft: Option<DraftFuture>,
    /// Set after acquisition or retirement lookup finds the affected incarnation.
    pub(super) target: Option<DocumentTarget>,
    pub(super) change: Option<Change>,
    pub(super) prepared: Option<Prepared>,
    pub(super) retire_on_commit: bool,
}

/// The logical address of a document record.
pub(crate) fn record_address(record: &impl DocumentIdentity) -> DocumentAddress {
    DocumentAddress {
        kind: record.kind().to_owned(),
        scope: record.record_scope().scope(),
        key: record.key().map(str::to_owned),
    }
}

#[derive(Default)]
struct TxState {
    sealed: bool,
    has_table_write: bool,
    /// Atomic batch; conversation and entry writes stage eagerly, while task
    /// and document writes assemble later.
    writes: Vec<StorageWrite>,
    created_conversation_ids: HashSet<ConversationId>,
    fork_source_conversation_ids: HashSet<ConversationId>,
    fork_source_document_ids: HashSet<DocumentId>,
    /// One entry per task touched by a public read, candidate write, or
    /// document-owner lookup, in first-touch order.
    tasks: Vec<(TaskId, TransactionTask)>,
    /// Submissions created by this transaction, in creation order.
    submissions: Vec<(SubmissionId, SubmissionRecord)>,
    /// Submission settlements and placements in staging order.
    submission_changes: Vec<(SubmissionId, SubmissionChange)>,
    /// Write and publication plans of every staged incarnation, built during assembly.
    plans: Vec<DocumentPlan>,
    /// Every document acquisition or retirement marker in staging order.
    documents: Vec<DocumentEntry>,
    /// Latest transaction-local incarnation or retirement marker at each logical address.
    latest_document_by_address: HashMap<String, usize>,
}

impl TxState {
    fn task_entry(&mut self, id: TaskId) -> &mut TransactionTask {
        let index = if let Some(index) = self.tasks.iter().position(|(task_id, _)| *task_id == id) {
            index
        } else {
            self.tasks.push((id, TransactionTask::default()));
            self.tasks.len() - 1
        };
        &mut self.tasks[index].1
    }

    fn task(&self, id: TaskId) -> Option<&TransactionTask> {
        self.tasks
            .iter()
            .find(|(task_id, _)| *task_id == id)
            .map(|(_, task)| task)
    }

    fn abort_changes(&self) {
        for document in &self.documents {
            if let Some(change) = &document.change {
                change.abort();
            }
        }
    }

    fn assert_open(&self) -> SessionResult<()> {
        if self.sealed {
            return Err(SessionError::error("Transaction has settled"));
        }
        Ok(())
    }
}

struct TxInner {
    host: Arc<dyn TransactionHost>,
    context: Context,
    scope: TransactionScope,
    state: Mutex<TxState>,
    /// Number of tracked operations still running.
    pending: watch::Sender<usize>,
}

/// Transaction surface of one Session commit callback: an owned, cloneable
/// handle sealed when the callback settles. Later use fails with
/// `Transaction has settled`.
///
/// Table reads and creation results are trusted immutable values and may be
/// shared with internal commit state.
#[derive(Clone)]
pub struct Tx {
    inner: Arc<TxInner>,
}

impl std::fmt::Debug for Tx {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_struct("Tx").finish_non_exhaustive()
    }
}

/// A result future of one transaction operation.
pub type TxFuture<T> = BoxFuture<'static, SessionResult<T>>;

fn rejected<T: Send + 'static>(error: SessionError) -> TxFuture<T> {
    futures::future::ready(Err(error)).boxed()
}

impl Tx {
    pub(crate) fn new(
        host: Arc<dyn TransactionHost>,
        context: Context,
        scope: TransactionScope,
    ) -> Self {
        let (pending, _) = watch::channel(0);
        Self {
            inner: Arc::new(TxInner {
                host,
                context,
                scope,
                state: Mutex::new(TxState::default()),
                pending,
            }),
        }
    }

    fn lock(&self) -> MutexGuard<'_, TxState> {
        self.inner
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    fn storage(&self) -> Arc<dyn Storage> {
        Arc::clone(self.inner.host.storage())
    }

    fn context(&self) -> &Context {
        &self.inner.context
    }

    fn assert_open(&self) -> SessionResult<()> {
        self.lock().assert_open()
    }

    /// Register an operation so callback settlement can reject and drain it.
    /// The operation starts now, like a JS promise.
    fn track<T: Send + 'static>(
        &self,
        operation: impl Future<Output = SessionResult<T>> + Send + 'static,
    ) -> TxFuture<T> {
        self.inner.pending.send_modify(|count| *count += 1);
        let inner = Arc::clone(&self.inner);
        let handle = tokio::spawn(async move {
            let result = operation.await;
            inner.pending.send_modify(|count| *count -= 1);
            result
        });
        async move { join(handle).await }.boxed()
    }

    async fn drain_pending(&self) {
        let mut receiver = self.inner.pending.subscribe();
        // The sender lives in `self.inner`, so the channel stays open.
        let _ = receiver.wait_for(|count| *count == 0).await;
    }

    fn read<T: Send + 'static>(
        &self,
        method: &'static str,
        read: impl Future<Output = SessionResult<T>> + Send + 'static,
    ) -> TxFuture<T> {
        {
            let state = self.lock();
            if let Err(error) = state.assert_open() {
                return rejected(error);
            }
            if state.has_table_write {
                return rejected(ReadAfterWrite::new(method).into());
            }
        }
        self.track(read)
    }

    fn write<T: Send + 'static>(
        &self,
        write: impl Future<Output = SessionResult<T>> + Send + 'static,
    ) -> TxFuture<T> {
        {
            let mut state = self.lock();
            if let Err(error) = state.assert_open() {
                return rejected(error);
            }
            state.has_table_write = true;
        }
        self.track(write)
    }

    // ─── Table reads ────────────────────────────────────────────────────────

    #[must_use]
    pub fn conversation(&self, id: ConversationId) -> TxFuture<Option<ConversationRecord>> {
        let (storage, cx) = (self.storage(), self.context().clone());
        self.read("conversation", async move {
            Ok(storage.conversation(id, &cx).await?)
        })
    }

    #[must_use]
    pub fn entry(&self, id: EntryId) -> TxFuture<Option<EntryRecord>> {
        let (storage, cx) = (self.storage(), self.context().clone());
        self.read("entry", async move {
            Ok(storage.entry(id, &cx).await?.map(|stored| stored.entry))
        })
    }

    /// `None` when the entry is absent or has another kind than `token`'s.
    #[must_use]
    pub fn typed_entry<D>(&self, token: &Entry<D>, id: EntryId) -> TxFuture<Option<TypedEntry<D>>>
    where
        D: EntryData + Send + 'static,
    {
        let (storage, cx, token) = (self.storage(), self.context().clone(), *token);
        self.read("entry", async move {
            match storage.entry(id, &cx).await? {
                None => Ok(None),
                Some(stored) => Ok(token.narrow(stored.entry)?),
            }
        })
    }

    #[must_use]
    pub fn task(&self, id: TaskId) -> TxFuture<Option<AnyTaskRecord>> {
        let tx = self.clone();
        self.read("task", async move { tx.committed_task(id).await })
    }

    #[must_use]
    pub fn scan_conversations(
        &self,
        query: ConversationQuery,
        limit: usize,
        cursor: Option<Cursor>,
    ) -> TxFuture<Page<ConversationRecord>> {
        let (storage, cx) = (self.storage(), self.context().clone());
        self.read("scanConversations", async move {
            Ok(storage
                .scan_conversations(&query, limit, cursor.as_ref(), &cx)
                .await?)
        })
    }

    #[must_use]
    pub fn scan_entries(
        &self,
        query: EntryQuery,
        limit: usize,
        cursor: Option<Cursor>,
    ) -> TxFuture<Page<EntryRecord>> {
        let (storage, cx) = (self.storage(), self.context().clone());
        self.read("scanEntries", async move {
            Ok(storage
                .scan_entries(&query, limit, cursor.as_ref(), &cx)
                .await?)
        })
    }

    /// Newest visible entry of the conversation that carries a `head`.
    #[must_use]
    pub fn latest_head_marker(
        &self,
        conversation_id: ConversationId,
    ) -> TxFuture<Option<EntryRecord>> {
        let (storage, cx) = (self.storage(), self.context().clone());
        self.read("latestHeadMarker", async move {
            Ok(storage
                .find_latest_head_marker(conversation_id, None, &cx)
                .await?)
        })
    }

    #[must_use]
    pub fn scan_tasks(
        &self,
        query: TaskQuery,
        limit: usize,
        cursor: Option<Cursor>,
    ) -> TxFuture<Page<AnyTaskRecord>> {
        let (storage, cx) = (self.storage(), self.context().clone());
        self.read("scanTasks", async move {
            Ok(storage
                .scan_tasks(&query, limit, cursor.as_ref(), &cx)
                .await?)
        })
    }

    /// Internal: committed submission record.
    #[must_use]
    pub fn submission(&self, id: SubmissionId) -> TxFuture<Option<SubmissionRecord>> {
        let (storage, cx) = (self.storage(), self.context().clone());
        self.read("submission", async move {
            Ok(storage.submission(id, &cx).await?)
        })
    }

    /// Committed submission with a conversation-scoped request ID.
    #[must_use]
    pub fn submission_by_request(
        &self,
        conversation_id: ConversationId,
        request_id: String,
    ) -> TxFuture<Option<SubmissionRecord>> {
        let (storage, cx) = (self.storage(), self.context().clone());
        self.read("submissionByRequest", async move {
            Ok(storage
                .submission_by_request(conversation_id, &request_id, &cx)
                .await?)
        })
    }

    // ─── Table writes ───────────────────────────────────────────────────────

    /// Create a conversation with explicitly selected ownership.
    #[must_use]
    pub fn create_conversation(
        &self,
        ownership: ConversationOwnership,
    ) -> TxFuture<ConversationRecord> {
        let tx = self.clone();
        self.write(async move { tx.stage_conversation(None, ownership, None).await })
    }

    /// Internal final-form bootstrap path for the reserved root identity.
    #[must_use]
    pub fn create_root_conversation(&self) -> TxFuture<ConversationRecord> {
        let tx = self.clone();
        self.write(async move {
            tx.stage_conversation(
                None,
                ConversationOwnership::Ownerless,
                Some(ROOT_CONVERSATION_ID),
            )
            .await
        })
    }

    /// Create a history fork at one concrete visible entry with explicitly
    /// selected ownership.
    #[must_use]
    pub fn fork_conversation(
        &self,
        parent_conversation_id: ConversationId,
        at: EntryId,
        ownership: ConversationOwnership,
    ) -> TxFuture<ConversationRecord> {
        let tx = self.clone();
        self.write(async move {
            tx.stage_conversation(
                Some(ConversationParent {
                    conversation_id: parent_conversation_id,
                    at,
                }),
                ownership,
                None,
            )
            .await
        })
    }

    async fn stage_conversation(
        &self,
        parent: Option<ConversationParent>,
        ownership: ConversationOwnership,
        reserved_id: Option<ConversationId>,
    ) -> SessionResult<ConversationRecord> {
        let owner_task_id = match ownership {
            ConversationOwnership::Ownerless => None,
            ConversationOwnership::Task { task_id } => Some(task_id),
        };
        let storage = self.storage();
        let id = match reserved_id {
            Some(id) => id,
            None => ConversationId::from_number(storage.mint_id().await?),
        };
        self.assert_open()?;
        let mut owner = None;
        if let Some(owner_task_id) = owner_task_id {
            let task = self.current_task(owner_task_id).await?;
            self.assert_open()?;
            let Some(task) = task else {
                return Err(SessionError::error(format!(
                    "Conversation owner task {owner_task_id} does not exist"
                )));
            };
            owner = Some(ConversationOwner {
                conversation_id: task.conversation_id,
                task_id: owner_task_id,
            });
        }
        let record = ConversationRecord { id, parent, owner };
        let copies = match parent {
            None => Vec::new(),
            Some(parent) => {
                prepare_fork_document_copies(
                    storage.as_ref(),
                    parent.conversation_id,
                    parent.at,
                    id,
                    self.context(),
                )
                .await?
            }
        };
        {
            let mut state = self.lock();
            state.assert_open()?;
            for copy in copies {
                state.fork_source_document_ids.insert(copy.source.id);
                let address = record_address(&copy.record);
                let entry = DocumentEntry {
                    address_id: address_id(&address),
                    address,
                    definition: None,
                    draft: None,
                    target: Some(DocumentTarget::ForkCopy {
                        record: copy.record,
                        source: copy.source,
                    }),
                    change: None,
                    prepared: None,
                    retire_on_commit: false,
                };
                let key = entry.address_id.clone();
                state.documents.push(entry);
                let index = state.documents.len() - 1;
                state.latest_document_by_address.insert(key, index);
            }
            if let Some(parent) = parent {
                state
                    .fork_source_conversation_ids
                    .insert(parent.conversation_id);
            }
            state.created_conversation_ids.insert(id);
            state
                .writes
                .push(StorageWrite::Conversation { value: record });
        }
        self.inner
            .host
            .conversation_created(self.clone(), record)
            .await?;
        self.assert_open()?;
        Ok(record)
    }

    /// Append one entry. Returned records are Session-owned immutable values
    /// and may be shared with commit listeners.
    #[must_use]
    pub fn append_entry(
        &self,
        conversation_id: ConversationId,
        value: EntryDraft,
    ) -> TxFuture<EntryRecord> {
        let tx = self.clone();
        self.write(async move {
            tx.require_conversation(conversation_id).await?;
            tx.assert_open()?;
            let id = EntryId::from_number(tx.storage().mint_id().await?);
            tx.assert_open()?;
            let EntryDraft {
                kind,
                model,
                data,
                head,
                edits,
            } = value;
            let record = EntryRecord {
                model,
                data,
                edits,
                kind,
                id,
                conversation_id,
                head: head.map(|head| match head {
                    EntryHead::SelfEntry => id,
                    EntryHead::Entry(entry) => entry,
                }),
                by_task_id: tx.inner.scope.task_id,
            };
            tx.lock().writes.push(StorageWrite::Entry {
                value: record.clone(),
            });
            Ok(record)
        })
    }

    /// Append an entry of `token`'s kind; the token supplies `kind` and types `data`.
    #[must_use]
    pub fn append_typed_entry<D>(
        &self,
        token: &Entry<D>,
        conversation_id: ConversationId,
        value: TypedEntryDraft<D>,
    ) -> TxFuture<TypedEntry<D>>
    where
        D: EntryData + Send + 'static,
    {
        let draft = match token.draft(&value) {
            Ok(draft) => draft,
            Err(error) => return rejected(error.into()),
        };
        let appended = self.append_entry(conversation_id, draft);
        async move { Ok(TypedEntry::new(appended.await?, value.data)) }.boxed()
    }

    /// Create a durable task of `task` with `input`.
    #[must_use]
    pub fn create_task(
        &self,
        task: Arc<dyn TaskDefinitionRef>,
        input: JsonValue,
        options: TaskOptions,
    ) -> TxFuture<TaskId> {
        let tx = self.clone();
        self.write(async move {
            let mut owner: Option<AnyTaskRecord> = None;
            if let TaskOwnership::Task { task_id } = options.ownership {
                // Validated again against the owner's final candidate during assembly.
                owner = tx.current_task(task_id).await?;
                tx.assert_open()?;
                let Some(owner) = &owner else {
                    return Err(SessionError::error(format!(
                        "Task owner {task_id} does not exist"
                    )));
                };
                if options.background == Some(true) {
                    return Err(SessionError::type_error(
                        "A child task cannot be background",
                    ));
                }
                if let Some(conversation_id) = options.conversation_id {
                    if conversation_id != owner.conversation_id {
                        return Err(SessionError::error(format!(
                            "A child task lives in its owner's conversation {}",
                            owner.conversation_id
                        )));
                    }
                }
            }
            let conversation_id = owner
                .as_ref()
                .map(|owner| owner.conversation_id)
                .or(options.conversation_id)
                .or(tx.inner.scope.conversation_id);
            let Some(conversation_id) = conversation_id else {
                return Err(SessionError::type_error(
                    "Tx.createTask() requires options.conversationId",
                ));
            };
            tx.require_conversation(conversation_id).await?;
            tx.assert_open()?;
            let checkpoint = task.initial(&input)?;
            let id = TaskId::from_number(tx.storage().mint_id().await?);
            tx.assert_open()?;
            let record = AnyTaskRecord {
                id,
                conversation_id,
                kind: task.name().to_owned(),
                version: task.version(),
                input,
                owner: owner.as_ref().map(|owner| owner.id),
                background: options.background.unwrap_or(false),
                abort_requested: false,
                abort_reason: None,
                abandon_on_restart: options.abandon_on_restart == Some(true),
                state: TaskState::Pending { checkpoint },
                memos: None,
                started_at: None,
                ended_at: None,
            };
            tx.lock().task_entry(id).write = Some((TaskWriteKind::Create, record));
            Ok(id)
        })
    }

    /// Create a raw submission record with a fresh ID. No admission rules
    /// apply: no busy check, no inbox queueing, no placement.
    #[must_use]
    pub fn create_submission(&self, create: SubmissionCreate) -> TxFuture<SubmissionRecord> {
        let tx = self.clone();
        self.write(async move {
            tx.require_conversation(create.conversation_id).await?;
            tx.assert_open()?;
            let id = SubmissionId::from_number(tx.storage().mint_id().await?);
            tx.assert_open()?;
            let record = SubmissionRecord::from_create(create, id);
            tx.lock().submissions.push((id, record.clone()));
            Ok(record)
        })
    }

    /// Settle a queued or placed submission; only a placed input can be
    /// answered, and a settled submission stays unchanged. Resolved during
    /// assembly against this transaction's latest record of the submission,
    /// falling back to committed state, so it works after table writes.
    ///
    /// # Errors
    ///
    /// `Transaction has settled` after the callback settled.
    pub fn settle_submission(
        &self,
        id: SubmissionId,
        settlement: SubmissionSettlement,
    ) -> SessionResult<()> {
        let mut state = self.lock();
        state.assert_open()?;
        state.has_table_write = true;
        state
            .submission_changes
            .push((id, SubmissionChange::Settle(settlement)));
        Ok(())
    }

    /// Place a queued submission at `entry`: an input becomes `placed`, a write
    /// `done`. Resolved during assembly like [`Tx::settle_submission`].
    ///
    /// # Errors
    ///
    /// `Transaction has settled` after the callback settled.
    pub fn place_submission(&self, id: SubmissionId, entry: EntryId) -> SessionResult<()> {
        let mut state = self.lock();
        state.assert_open()?;
        state.has_table_write = true;
        state
            .submission_changes
            .push((id, SubmissionChange::Placed(entry)));
        Ok(())
    }

    /// Internal: replace one task record completely. Tasks change their own
    /// state through their runtime.
    ///
    /// # Errors
    ///
    /// The transaction settled, the task already has a terminal candidate, or
    /// the record moves the task to another conversation.
    pub fn set_task(&self, value: AnyTaskRecord) -> SessionResult<()> {
        let mut state = self.lock();
        state.assert_open()?;
        state.has_table_write = true;
        let host = Arc::clone(&self.inner.host);
        let task = state.task_entry(value.id);
        let candidate = task.write.as_ref().map(|(_, record)| record);
        if candidate.is_some_and(|candidate| candidate.state.status() == TaskStatus::Terminal) {
            return Err(SessionError::error(format!(
                "Task {} already has a terminal candidate",
                value.id
            )));
        }
        if candidate.is_some_and(|candidate| candidate.conversation_id != value.conversation_id) {
            return Err(SessionError::error(format!(
                "Task {} cannot change conversations",
                value.id
            )));
        }
        let kind = match &task.write {
            Some((TaskWriteKind::Create, _)) => TaskWriteKind::Create,
            Some((TaskWriteKind::Replace, _)) | None => TaskWriteKind::Replace,
        };
        let value = stamp_times(value, candidate, || host.now());
        task.write = Some((kind, value));
        Ok(())
    }

    /// Internal: candidate records of the tasks this transaction created or
    /// replaced so far.
    #[must_use]
    pub fn staged_tasks(&self) -> Vec<AnyTaskRecord> {
        self.lock()
            .tasks
            .iter()
            .filter_map(|(_, task)| task.write.as_ref().map(|(_, record)| record.clone()))
            .collect()
    }

    /// Internal: conversations this transaction created or forked so far.
    #[must_use]
    pub fn staged_conversations(&self) -> Vec<ConversationRecord> {
        self.lock()
            .writes
            .iter()
            .filter_map(|write| match write {
                StorageWrite::Conversation { value } => Some(*value),
                _ => None,
            })
            .collect()
    }

    // ─── Documents ──────────────────────────────────────────────────────────

    /// Acquire the draft of a singleton document, creating it from its
    /// definition when absent. Repeated acquisition returns the same draft.
    #[must_use]
    pub fn doc<D: SingletonDocToken>(&self, token: &D, locator: D::Locator<'_>) -> TxFuture<Draft> {
        let resolved = resolve_token_address(token, locator);
        self.doc_at(&erase(token), resolved, None)
    }

    /// Acquire the draft of a family member, creating it from `seed` when
    /// absent; the first seed of a transaction wins and existing members
    /// ignore it.
    #[must_use]
    pub fn doc_member<D: FamilyDocToken>(
        &self,
        token: &D,
        locator: D::Locator<'_>,
        seed: &D::Seed,
    ) -> TxFuture<Draft> {
        let resolved = resolve_token_address(token, locator);
        match token.encode_seed(seed) {
            Ok(seed) => self.doc_at(&erase(token), resolved, seed),
            Err(error) => rejected(error.into()),
        }
    }

    /// Retire the current incarnation at `token`'s address in this commit. A
    /// later acquisition in the same commit creates a new incarnation.
    #[must_use]
    pub fn retire_doc<D: DocToken>(&self, token: &D, locator: D::Locator<'_>) -> TxFuture<()> {
        let resolved = resolve_token_address(token, locator);
        self.retire_doc_at(&erase(token), resolved)
    }

    /// Acquire the draft of the document at `resolved`, creating it from its
    /// definition (and family `seed`) when absent. Repeated acquisition of the
    /// same address returns the memoized draft.
    pub(crate) fn doc_at(
        &self,
        definition: &Definition,
        resolved: ResolvedAddress,
        seed: Option<JsonValue>,
    ) -> TxFuture<Draft> {
        let mut state = self.lock();
        if let Err(error) = state.assert_open() {
            return rejected(error);
        }
        if let DocumentScope::Task { task_id } = resolved.address.scope {
            if state
                .task(task_id)
                .and_then(|task| task.write.as_ref())
                .is_some_and(|(_, record)| record.state.status() == TaskStatus::Terminal)
            {
                return rejected(SessionError::error(format!("Task {task_id} is terminal")));
            }
        }
        let latest = state.latest_document_by_address.get(&resolved.id).copied();
        let mut skip_load = false;
        if let Some(index) = latest {
            let entry = &state.documents[index];
            if entry.retire_on_commit {
                skip_load = true;
            } else {
                if let Some(draft) = &entry.draft {
                    return draft.clone().boxed();
                }
                if let Some(DocumentTarget::ForkCopy { record, source }) = entry.target.clone() {
                    let tx = self.clone();
                    let definition = definition.clone();
                    let draft = self
                        .track(async move {
                            tx.acquire_fork_copy(index, definition, record, source)
                                .await
                        })
                        .shared();
                    state.documents[index].draft = Some(draft.clone());
                    return draft.boxed();
                }
            }
        }
        let seed = if definition.is_family() { seed } else { None };
        state.documents.push(DocumentEntry {
            address_id: resolved.id.clone(),
            address: resolved.address,
            definition: Some(definition.clone()),
            draft: None,
            target: None,
            change: None,
            prepared: None,
            retire_on_commit: false,
        });
        let index = state.documents.len() - 1;
        state.latest_document_by_address.insert(resolved.id, index);
        // Capture retirement before awaiting so a pending old acquisition and
        // its replacement stay distinct.
        let tx = self.clone();
        let draft = self
            .track(async move { tx.acquire(index, seed, skip_load).await })
            .shared();
        state.documents[index].draft = Some(draft.clone());
        draft.boxed()
    }

    /// Retire the document at `resolved` in this commit.
    pub(crate) fn retire_doc_at(
        &self,
        definition: &Definition,
        resolved: ResolvedAddress,
    ) -> TxFuture<()> {
        let mut state = self.lock();
        if let Err(error) = state.assert_open() {
            return rejected(error);
        }
        if let Some(index) = state.latest_document_by_address.get(&resolved.id).copied() {
            let entry = &mut state.documents[index];
            if entry.retire_on_commit {
                return futures::future::ready(Ok(())).boxed();
            }
            if let Some(DocumentTarget::ForkCopy { record, .. }) = &entry.target {
                if let Err(error) = check_record_scope(definition.as_ref(), record) {
                    return rejected(error.into());
                }
                entry.retire_on_commit = true;
                return futures::future::ready(Ok(())).boxed();
            }
            if let Some(draft) = entry.draft.clone() {
                // Retirement of an acquired draft persists its final content
                // before retirement.
                entry.retire_on_commit = true;
                drop(state);
                return self.track(async move { draft.await.map(|_| ()) });
            }
        }
        state.documents.push(DocumentEntry {
            address_id: resolved.id.clone(),
            address: resolved.address,
            definition: Some(definition.clone()),
            draft: None,
            target: None,
            change: None,
            prepared: None,
            retire_on_commit: true,
        });
        let index = state.documents.len() - 1;
        state.latest_document_by_address.insert(resolved.id, index);
        drop(state);
        let tx = self.clone();
        self.track(async move { tx.find_retirement(index).await })
    }

    fn entry_parts(&self, index: usize) -> (Definition, String, DocumentAddress) {
        let state = self.lock();
        let entry = &state.documents[index];
        (
            entry
                .definition
                .clone()
                .expect("acquired entries carry their definition"),
            entry.address_id.clone(),
            entry.address.clone(),
        )
    }

    async fn acquire(
        &self,
        index: usize,
        seed: Option<JsonValue>,
        skip_load: bool,
    ) -> SessionResult<Draft> {
        let (definition, address_id, address) = self.entry_parts(index);
        let loaded = if skip_load {
            None
        } else {
            self.inner
                .host
                .load(
                    definition.clone(),
                    address_id,
                    address.clone(),
                    self.context().clone(),
                )
                .await?
        };
        if let Some(loaded) = loaded {
            let mut state = self.lock();
            state.assert_open()?;
            check_record_scope(definition.as_ref(), &loaded.record)?;
            check_record_version(definition.as_ref(), &loaded.record, loaded.stored_version())?;
            let change = loaded.tracker.begin_change();
            let entry = &mut state.documents[index];
            entry.target = Some(DocumentTarget::Loaded(loaded));
            entry.change = Some(change.clone());
            return Ok(change.state()?);
        }
        self.assert_open()?;
        match address.scope {
            DocumentScope::Session => {}
            DocumentScope::Conversation { conversation_id } => {
                self.require_conversation(conversation_id).await?;
            }
            DocumentScope::Task { task_id } => {
                let task = self.current_task(task_id).await?;
                let Some(task) = task else {
                    return Err(SessionError::error(format!(
                        "Task {task_id} does not exist"
                    )));
                };
                if task.state.status() == TaskStatus::Terminal {
                    return Err(SessionError::error(format!("Task {task_id} is terminal")));
                }
            }
        }
        self.assert_open()?;
        let value = definition.initial(seed.as_ref())?;
        let id = DocumentId::from_number(self.storage().mint_id().await?);
        let mut state = self.lock();
        state.assert_open()?;
        let record = document_create(definition.as_ref(), &address, id)?;
        let tracker = track(JsonValue::Object(value))?;
        let change = tracker.begin_change();
        let entry = &mut state.documents[index];
        entry.target = Some(DocumentTarget::Created {
            record,
            version: definition.version(),
            tracker,
        });
        entry.change = Some(change.clone());
        Ok(change.state()?)
    }

    async fn acquire_fork_copy(
        &self,
        index: usize,
        definition: Definition,
        record: DocumentCreate,
        source: DocumentCopySource,
    ) -> SessionResult<Draft> {
        let stored = self
            .storage()
            .document(source.id, source.at, self.context())
            .await?;
        self.assert_open()?;
        let Some(stored) = stored else {
            return Err(SessionError::error(format!(
                "Fork source document {} cannot be read",
                source.id
            )));
        };
        let matches = matches!(
            stored.record.scope,
            DocumentRecordScope::Conversation { .. }
        ) && stored.record.kind == record.kind
            && stored.record.key == record.key
            && stored.record.scope.history() == record.scope.history()
            && stored.record.scope.fork() == record.scope.fork();
        if !matches {
            return Err(SessionError::error(format!(
                "Fork source document {} does not match the copied record",
                source.id
            )));
        }
        let value = materialize_document_value(
            definition.as_ref(),
            &record,
            stored.version,
            &stored.value,
        )?;
        let tracker = track(JsonValue::Object(value))?;
        let mut state = self.lock();
        state.assert_open()?;
        let change = tracker.begin_change();
        let version = definition.version();
        let entry = &mut state.documents[index];
        entry.definition = Some(definition);
        entry.target = Some(DocumentTarget::Created {
            record,
            version,
            tracker,
        });
        entry.change = Some(change.clone());
        Ok(change.state()?)
    }

    async fn find_retirement(&self, index: usize) -> SessionResult<()> {
        let (definition, address_id, address) = self.entry_parts(index);
        let record = match self.inner.host.cached(&address_id) {
            Some(loaded) => Some(loaded.record.clone()),
            None => {
                self.storage()
                    .find_document(&address, DocumentPoint::Current, self.context())
                    .await?
            }
        };
        let mut state = self.lock();
        state.assert_open()?;
        let Some(record) = record else {
            return Ok(());
        };
        check_record_scope(definition.as_ref(), &record)?;
        state.documents[index].target = Some(DocumentTarget::RetireOnly(record));
        Ok(())
    }

    // ─── Settlement ─────────────────────────────────────────────────────────

    /// Seal after callback failure: abort every change and observe every
    /// pending operation.
    pub(crate) async fn settle_failure(&self) {
        {
            let mut state = self.lock();
            state.sealed = true;
            state.abort_changes();
        }
        self.drain_pending().await;
    }

    /// Seal after callback success, prepare every open change, and assemble
    /// the atomic batch. Any failure aborts every change before Storage
    /// admission.
    pub(crate) async fn settle_success(&self) -> SessionResult<Vec<StorageWrite>> {
        let pending = {
            let mut state = self.lock();
            state.sealed = true;
            *self.inner.pending.borrow() > 0
        };
        if pending {
            self.lock().abort_changes();
            self.drain_pending().await;
            return Err(SessionError::error(
                "Session commit callback settled before its pending Tx operations",
            ));
        }
        let result = self.prepare_and_assemble().await;
        if result.is_err() {
            self.lock().abort_changes();
        }
        result
    }

    async fn prepare_and_assemble(&self) -> SessionResult<Vec<StorageWrite>> {
        {
            // Prepare every open change; this revokes every draft.
            let mut state = self.lock();
            for document in &mut state.documents {
                if let Some(change) = &document.change {
                    document.prepared = Some(change.prepare()?);
                }
            }
        }
        self.assemble().await
    }

    /// Abort every prepared change after Storage failure or when no write is
    /// required.
    pub(crate) fn discard(&self) {
        self.lock().abort_changes();
    }

    /// Adopt every prepared change by pointer swap after Storage success and
    /// describe the publication.
    pub(crate) fn adopt(&self, seq: Seq) -> SessionResult<Vec<DocumentCommitChange>> {
        let state = self.lock();
        let mut publications = Vec::new();
        for plan in &state.plans {
            let committed = matches!(plan.record, PlanRecord::Committed(_));
            let mut record = match &plan.record {
                PlanRecord::Committed(record) => record.clone(),
                PlanRecord::New(record) => DocumentRecord::from_create(record.clone(), seq),
            };
            if plan.retire {
                record.retired_at = Some(seq);
            }
            if let Some(change) = &plan.change {
                // A new incarnation is adopted unless it retires in the same
                // commit; a loaded one only when it changed.
                let adopt = match &change.loaded {
                    None => !plan.retire,
                    Some(_) => !change.ops.is_empty(),
                };
                if adopt {
                    change.tracker.adopt(&change.prepared)?;
                } else {
                    change.prepared.abort();
                }
                if let Some(loaded) = &change.loaded {
                    if loaded.stored_version() < change.version {
                        loaded
                            .stored_version
                            .store(change.version, Ordering::Relaxed);
                    }
                    if let Some(StorageWrite::DocumentChange { content, .. }) = &plan.content {
                        match content {
                            DocumentContent::Base(_) => {
                                loaded.deltas_since_base.store(0, Ordering::Relaxed);
                            }
                            DocumentContent::Delta(_) => {
                                loaded.deltas_since_base.fetch_add(1, Ordering::Relaxed);
                            }
                        }
                    }
                } else if !plan.retire {
                    self.inner.host.install(LoadedDocument::new(
                        plan.address_id.clone(),
                        record.clone(),
                        change.version,
                        change.version,
                        0,
                        change.tracker.clone(),
                    ));
                }
            }
            let conversation_id = plan.conversation_id;
            if plan.retire {
                if committed {
                    self.inner.host.evict(&plan.address_id, record.id);
                }
                publications.push(DocumentCommitChange::Document {
                    record,
                    conversation_id,
                    version: None,
                    value: None,
                    ops: empty_operations(),
                });
            } else if let (
                Some(StorageWrite::DocumentCopy { source, .. }),
                DocumentRecordScope::Conversation {
                    conversation_id, ..
                },
            ) = (&plan.content, record.scope)
            {
                publications.push(DocumentCommitChange::Copy {
                    record,
                    conversation_id,
                    source: *source,
                });
            } else if let Some(change) = plan.change.as_ref().filter(|_| publishes(plan)) {
                let ops = if change.loaded.is_none() {
                    empty_operations()
                } else {
                    Arc::clone(&change.ops)
                };
                publications.push(DocumentCommitChange::Document {
                    record,
                    conversation_id,
                    version: Some(change.version),
                    value: Some(object_value(change.prepared.value())),
                    ops,
                });
            }
        }
        Ok(publications)
    }

    async fn assemble(&self) -> SessionResult<Vec<StorageWrite>> {
        let mut plans = {
            let state = self.lock();
            state
                .documents
                .iter()
                .filter_map(plan_document)
                .collect::<Vec<_>>()
        };
        self.reject_fork_source_writes(&plans)?;
        self.validate_owners().await?;
        let replaced: Vec<(TaskId, ConversationId)> = self
            .lock()
            .tasks
            .iter()
            .filter_map(|(id, task)| match &task.write {
                Some((TaskWriteKind::Replace, record)) => Some((*id, record.conversation_id)),
                Some((TaskWriteKind::Create, _)) | None => None,
            })
            .collect();
        for (id, conversation_id) in replaced {
            let Some(committed) = self.committed_task(id).await? else {
                return Err(SessionError::error(format!("Task {id} does not exist")));
            };
            if committed.state.status() == TaskStatus::Terminal {
                return Err(SessionError::error(format!(
                    "Task {id} is already terminal"
                )));
            }
            if committed.conversation_id != conversation_id {
                return Err(SessionError::error(format!(
                    "Task {id} cannot change conversations"
                )));
            }
        }

        self.retire_terminal_task_documents(&mut plans).await?;
        self.resolve_publication_conversations(&mut plans).await?;
        self.resolve_submission_changes().await?;

        let mut state = self.lock();
        let mut writes = std::mem::take(&mut state.writes);
        for (_, value) in &state.submissions {
            writes.push(StorageWrite::Submission {
                value: value.clone(),
            });
        }
        for (_, task) in &state.tasks {
            if let Some((_, record)) = &task.write {
                writes.push(StorageWrite::Task {
                    value: record.clone(),
                });
            }
        }
        for plan in &mut plans {
            // Checkpoint predicates run last, after every validation.
            if let (
                Some(StorageWrite::DocumentChange {
                    id,
                    content: DocumentContent::Delta(_),
                }),
                Some(change),
            ) = (&plan.content, &plan.change)
            {
                if let Some(loaded) = &change.loaded {
                    let info = CheckpointInfo {
                        deltas_since_base: loaded.deltas_since_base(),
                    };
                    let value = object_value(change.prepared.value());
                    let checkpoint = change.definition.as_ref().is_some_and(|definition| {
                        definition.checkpoint_when(&value, &change.ops, info)
                    });
                    if checkpoint {
                        plan.content = Some(StorageWrite::DocumentChange {
                            id: *id,
                            content: DocumentContent::Base(DocumentBase {
                                version: change.version,
                                value,
                            }),
                        });
                    }
                }
            }
            if let Some(content) = &plan.content {
                writes.push(content.clone());
            }
            if plan.retire {
                writes.push(StorageWrite::DocumentRetire {
                    id: plan.record.id(),
                });
            }
        }
        state.plans = plans;
        Ok(writes)
    }

    // ─── Helpers ────────────────────────────────────────────────────────────

    /// Terminal settlement retires every task document, including ones
    /// created by this transaction.
    async fn retire_terminal_task_documents(
        &self,
        plans: &mut Vec<DocumentPlan>,
    ) -> SessionResult<()> {
        let storage = self.storage();
        let terminal_tasks: Vec<(TaskId, TaskWriteKind)> = self
            .lock()
            .tasks
            .iter()
            .filter_map(|(_, task)| {
                task.write.as_ref().and_then(|(kind, record)| {
                    (record.state.status() == TaskStatus::Terminal).then_some((record.id, *kind))
                })
            })
            .collect();
        if !terminal_tasks.is_empty() {
            let mut retiring = HashSet::new();
            for plan in plans.iter_mut() {
                let DocumentRecordScope::Task { task_id } = plan.record.scope() else {
                    continue;
                };
                if !terminal_tasks.iter().any(|(id, _)| *id == task_id) {
                    continue;
                }
                plan.retire = true;
                retiring.insert(plan.record.id());
            }
            for (task_id, kind) in &terminal_tasks {
                if *kind == TaskWriteKind::Create {
                    continue;
                }
                let mut cursor: Option<Cursor> = None;
                loop {
                    let query = DocumentQuery {
                        scope: DocumentScope::Task { task_id: *task_id },
                        at: DocumentPoint::Current,
                        kind: None,
                    };
                    let page = storage
                        .scan_documents(
                            &query,
                            INTERNAL_SCAN_PAGE_SIZE,
                            cursor.as_ref(),
                            self.context(),
                        )
                        .await?;
                    for record in page.items {
                        if !retiring.insert(record.id) {
                            continue;
                        }
                        plans.push(DocumentPlan {
                            address_id: address_id(&record_address(&record)),
                            record: PlanRecord::Committed(record),
                            retire: true,
                            content: None,
                            change: None,
                            conversation_id: None,
                        });
                    }
                    cursor = page.next;
                    if cursor.is_none() {
                        break;
                    }
                }
            }
        }

        Ok(())
    }

    /// Resolve publication ownership before Storage admission so adoption
    /// remains synchronous.
    async fn resolve_publication_conversations(
        &self,
        plans: &mut [DocumentPlan],
    ) -> SessionResult<()> {
        for plan in plans.iter_mut() {
            if !publishes(plan) {
                continue;
            }
            match plan.record.scope() {
                DocumentRecordScope::Session => {}
                DocumentRecordScope::Conversation {
                    conversation_id, ..
                } => {
                    plan.conversation_id = Some(conversation_id);
                }
                DocumentRecordScope::Task { task_id } => {
                    let known = self.lock().task_entry(task_id).publication_conversation_id;
                    let resolved = if known.is_some() {
                        known
                    } else {
                        let current = self.current_task(task_id).await?;
                        let resolved = current.map(|task| task.conversation_id);
                        self.lock().task_entry(task_id).publication_conversation_id = resolved;
                        resolved
                    };
                    plan.conversation_id = resolved;
                }
            }
        }

        Ok(())
    }

    /// Apply staged submission settlements and placements to the latest
    /// candidate records, falling back to committed state.
    async fn resolve_submission_changes(&self) -> SessionResult<()> {
        let storage = self.storage();
        let changes = std::mem::take(&mut self.lock().submission_changes);
        for (id, change) in &changes {
            let staged = self
                .lock()
                .submissions
                .iter()
                .find(|(submission_id, _)| submission_id == id)
                .map(|(_, record)| record.clone());
            let current = if let Some(record) = staged {
                Some(record)
            } else {
                storage.submission(*id, self.context()).await?
            };
            let Some(current) = current else {
                return Err(SessionError::error(format!(
                    "Submission {id} does not exist"
                )));
            };
            if let Some(next) = apply_submission_change(&current, change)? {
                let mut state = self.lock();
                match state
                    .submissions
                    .iter_mut()
                    .find(|(submission_id, _)| submission_id == id)
                {
                    Some((_, record)) => *record = next,
                    None => state.submissions.push((*id, next)),
                }
            }
        }

        Ok(())
    }

    /// New owned work needs a live owner, judged on the owner's final
    /// candidate: not `completing`, terminal, or abort-marked. A task
    /// therefore cannot create owned work in the commit that finishes it.
    async fn validate_owners(&self) -> SessionResult<()> {
        let owners: Vec<(&'static str, TaskId)> = {
            let state = self.lock();
            let mut owners = Vec::new();
            for write in &state.writes {
                if let StorageWrite::Conversation {
                    value:
                        ConversationRecord {
                            owner: Some(owner), ..
                        },
                } = write
                {
                    owners.push(("Conversation owner task", owner.task_id));
                }
            }
            for (_, task) in &state.tasks {
                if let Some((TaskWriteKind::Create, record)) = &task.write {
                    if let Some(owner) = record.owner {
                        owners.push(("Task owner", owner));
                    }
                }
            }
            owners
        };
        for (what, task_id) in owners {
            let Some(task) = self.current_task(task_id).await? else {
                return Err(SessionError::error(format!(
                    "{what} {task_id} does not exist"
                )));
            };
            let status = match task.state.status() {
                TaskStatus::Terminal => Some("terminal"),
                TaskStatus::Completing => Some("completing"),
                TaskStatus::Pending | TaskStatus::Running | TaskStatus::Waiting => None,
            };
            if let Some(status) = status {
                return Err(SessionError::error(format!("{what} {task_id} is {status}")));
            }
            if task.abort_requested {
                return Err(SessionError::error(format!(
                    "{what} {task_id} is abort-marked"
                )));
            }
        }
        Ok(())
    }

    fn reject_fork_source_writes(&self, plans: &[DocumentPlan]) -> SessionResult<()> {
        let state = self.lock();
        for plan in plans {
            if plan.content.is_none() && !plan.retire {
                continue;
            }
            let id = plan.record.id();
            if state.fork_source_document_ids.contains(&id) {
                return Err(SessionError::error(format!(
                    "Cannot change fork source document {id} in the fork transaction"
                )));
            }
            if let DocumentRecordScope::Conversation {
                conversation_id,
                semantics,
            } = plan.record.scope()
            {
                if state
                    .fork_source_conversation_ids
                    .contains(&conversation_id)
                    && semantics.fork() == DocumentFork::Current
                {
                    return Err(SessionError::error(format!(
                        "Cannot fork conversation {conversation_id} while changing its current-policy documents"
                    )));
                }
            }
        }
        Ok(())
    }

    async fn require_conversation(&self, id: ConversationId) -> SessionResult<()> {
        if self.lock().created_conversation_ids.contains(&id) {
            return Ok(());
        }
        if self
            .storage()
            .conversation(id, self.context())
            .await?
            .is_none()
        {
            return Err(SessionError::error(format!(
                "Conversation {id} does not exist"
            )));
        }
        Ok(())
    }

    /// Latest candidate task record, falling back to committed state; not a
    /// caller table read.
    async fn current_task(&self, id: TaskId) -> SessionResult<Option<AnyTaskRecord>> {
        let candidate = self
            .lock()
            .task(id)
            .and_then(|task| task.write.as_ref())
            .map(|(_, record)| record.clone());
        match candidate {
            Some(record) => Ok(Some(record)),
            None => self.committed_task(id).await,
        }
    }

    fn committed_task(&self, id: TaskId) -> TaskRead {
        let mut state = self.lock();
        let task = state.task_entry(id);
        task.committed_read
            .get_or_insert_with(|| {
                let (storage, cx) = (self.storage(), self.context().clone());
                async move { Ok(storage.task(id, &cx).await?) }
                    .boxed()
                    .shared()
            })
            .clone()
    }
}

/// The erased definition of a typed token.
pub(crate) fn erase<D: DocToken>(token: &D) -> Definition {
    Arc::new(*token)
}

/// Await a spawned operation, resuming its panic.
pub(crate) async fn join<T>(handle: tokio::task::JoinHandle<SessionResult<T>>) -> SessionResult<T> {
    match handle.await {
        Ok(result) => result,
        Err(error) => match error.try_into_panic() {
            Ok(panic) => std::panic::resume_unwind(panic),
            Err(_) => Err(SessionError::error(
                "Session operation was cancelled by runtime shutdown",
            )),
        },
    }
}

/// Lifecycle times: `started_at` on the first change to `running`, `ended_at`
/// on the change to `terminal`. Once set, they carry over from the replaced
/// record; records written before they existed lack them.
fn stamp_times(
    mut value: AnyTaskRecord,
    candidate: Option<&AnyTaskRecord>,
    now: impl Fn() -> f64,
) -> AnyTaskRecord {
    let status = value.state.status();
    let started_at = candidate
        .and_then(|candidate| candidate.started_at)
        .or(value.started_at)
        .or_else(|| (status == TaskStatus::Running).then(&now));
    let ended_at = candidate
        .and_then(|candidate| candidate.ended_at)
        .or(value.ended_at)
        .or_else(|| (status == TaskStatus::Terminal).then(&now));
    value.started_at = started_at;
    value.ended_at = ended_at;
    value
}
