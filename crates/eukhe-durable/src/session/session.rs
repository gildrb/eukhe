//! Session kernel: one mutation line, the loaded document tracker cache, and
//! committed publication.
//!
//! Only committed state is observable. Every commit callback, preparation,
//! Storage settlement, adoption, and publication enqueue runs while the line is
//! held; listeners run later.

use std::collections::HashMap;
use std::future::Future;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};

use eukhe_chord::context::{await_with_context, without_abort_signal, AbortSignal, Context};
use eukhe_chord::delta::{track, Op};
use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_chord::{
    replicated_state_from_source, AttachedReplicatedState, ReplicatedStateSourceOptions,
};
use futures::future::{BoxFuture, FutureExt, Shared};
use tokio::sync::oneshot;

use crate::documents::{
    check_record_scope, check_record_version, materialize_document, resolve_token_address,
    DocToken, ResolvedAddress, RewindableDocToken,
};
use crate::types::{
    CommitChange, CommitPublication, ConversationRecord, DocumentAddress, DocumentCommitChange,
    DocumentId, DocumentPoint, DocumentRecord, DocumentScope, EntryId, Seq, Storage, StorageWrite,
};

use super::error::{SessionError, SessionResult};
use super::observation::{
    CommittedStateSource, CommittedWatch, DocumentWatch, ObservedDocumentValue, Ops,
    RETIREMENT_OPERATIONS,
};
use super::transaction::{
    erase, join, Definition, LoadedDocument, TransactionHost, TransactionScope, Tx,
};

/// Synchronous post-adoption listener. It must not block or call Session
/// operations.
pub type CommitListener = Arc<dyn Fn(&CommitPublication, &Context) + Send + Sync>;

/// Listener called synchronously when close begins. It must not block or call
/// Session operations.
pub type CloseListener = Arc<dyn Fn() + Send + Sync>;

/// Disposable, read-only Chord state bound to one committed document
/// incarnation; its value is the object, or `null` once retired.
pub type DocumentState = AttachedReplicatedState;

/// Protected hooks a Harness installs on its Session (TS protected methods
/// `conversationCreated` and `beforeClose`).
///
/// A plain Session uses [`NoSessionHooks`].
pub trait SessionHooks: Send + Sync {
    /// Runs inside every transaction that creates or forks a conversation,
    /// after the conversation record is staged. A plain Session stages
    /// nothing; a Harness stages its built-in documents. An error fails the
    /// creating operation.
    fn conversation_created(
        &self,
        tx: Tx,
        record: ConversationRecord,
    ) -> BoxFuture<'static, SessionResult<()>>;

    /// Runs after close seals admission and before the line closes Storage;
    /// must not fail.
    fn before_close(&self) -> BoxFuture<'static, ()>;
}

/// Hooks of a plain Session: stage nothing, do nothing before close.
#[derive(Clone, Copy, Debug, Default)]
pub struct NoSessionHooks;

impl SessionHooks for NoSessionHooks {
    fn conversation_created(
        &self,
        _tx: Tx,
        _record: ConversationRecord,
    ) -> BoxFuture<'static, SessionResult<()>> {
        futures::future::ready(Ok(())).boxed()
    }

    fn before_close(&self) -> BoxFuture<'static, ()> {
        futures::future::ready(()).boxed()
    }
}

/// Handle returned by a subscription; calling it removes the listener.
#[must_use = "dropping the handle keeps the listener registered"]
pub struct Unsubscribe {
    remove: Box<dyn Fn() -> bool + Send + Sync>,
}

impl Unsubscribe {
    /// A handle whose call runs `remove`.
    #[allow(dead_code, reason = "used by the harness registry, ported separately")]
    pub(crate) fn new(remove: impl Fn() -> bool + Send + Sync + 'static) -> Self {
        Self {
            remove: Box::new(remove),
        }
    }

    /// Remove the listener; `true` when it was still registered.
    #[expect(
        clippy::must_use_candidate,
        reason = "the TS function returns `Set.delete`'s result, usually ignored"
    )]
    pub fn unsubscribe(&self) -> bool {
        (self.remove)()
    }
}

impl std::fmt::Debug for Unsubscribe {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Unsubscribe")
            .finish_non_exhaustive()
    }
}

type Closing = Shared<BoxFuture<'static, SessionResult<()>>>;

#[derive(Default)]
struct SessionState {
    documents: HashMap<String, Arc<LoadedDocument>>,
    commit_listeners: Vec<(u64, CommitListener)>,
    close_listeners: Vec<(u64, CloseListener)>,
    next_listener: u64,
    tail: Option<oneshot::Receiver<()>>,
    closing: Option<Closing>,
    poison: Option<Arc<SessionError>>,
}

struct SessionInner {
    storage: Arc<dyn Storage>,
    hooks: Arc<dyn SessionHooks>,
    state: Mutex<SessionState>,
    this: Weak<SessionInner>,
}

/// Owner of one mutation line, its records, and its tracked documents (TS
/// `SessionImpl`). Clones share the Session.
#[derive(Clone)]
pub struct Session {
    inner: Arc<SessionInner>,
}

impl std::fmt::Debug for Session {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_struct("Session").finish_non_exhaustive()
    }
}

/// Open a Session kernel over one storage backend.
#[must_use]
pub fn create_session(storage: Arc<dyn Storage>) -> Session {
    Session::new(storage)
}

fn ready<T: Send + 'static>(result: SessionResult<T>) -> BoxFuture<'static, SessionResult<T>> {
    futures::future::ready(result).boxed()
}

impl Session {
    /// A plain Session over `storage`.
    #[must_use]
    pub fn new(storage: Arc<dyn Storage>) -> Self {
        Self::with_hooks(storage, Arc::new(NoSessionHooks))
    }

    /// A Session whose protected hooks are `hooks`.
    #[must_use]
    pub fn with_hooks(storage: Arc<dyn Storage>, hooks: Arc<dyn SessionHooks>) -> Self {
        Self {
            inner: Arc::new_cyclic(|this| SessionInner {
                storage,
                hooks,
                state: Mutex::new(SessionState::default()),
                this: this.clone(),
            }),
        }
    }

    /// The Session's storage backend.
    #[must_use]
    pub fn storage(&self) -> &Arc<dyn Storage> {
        &self.inner.storage
    }

    /// Run one atomic transaction on the Session mutation line. The commit is
    /// enqueued now; the returned future only awaits it.
    pub fn commit<T, F, Fut>(
        &self,
        change: F,
        cx: &Context,
    ) -> impl Future<Output = SessionResult<T>> + Send + 'static
    where
        T: Send + 'static,
        F: FnOnce(Tx) -> Fut + Send + 'static,
        Fut: Future<Output = SessionResult<T>> + Send + 'static,
    {
        self.commit_with(change, cx, TransactionScope::default())
    }

    /// Internal commit binding `scope`: the default `tx.create_task()`
    /// conversation and the task attributed to appended entries.
    pub fn commit_with<T, F, Fut>(
        &self,
        change: F,
        cx: &Context,
        scope: TransactionScope,
    ) -> impl Future<Output = SessionResult<T>> + Send + 'static
    where
        T: Send + 'static,
        F: FnOnce(Tx) -> Fut + Send + 'static,
        Fut: Future<Output = SessionResult<T>> + Send + 'static,
    {
        if let Err(error) = self.inner.assert_usable() {
            return ready(Err(error));
        }
        let inner = Arc::clone(&self.inner);
        let cx = cx.clone();
        self.inner
            .enqueue(async move { inner.run_commit(change, cx, scope).await })
            .boxed()
    }

    /// Internal: run a read-only job on the mutation line so multi-read
    /// derivations observe one committed state.
    pub fn read_on_line<T, Fut>(
        &self,
        job: Fut,
    ) -> impl Future<Output = SessionResult<T>> + Send + 'static
    where
        T: Send + 'static,
        Fut: Future<Output = SessionResult<T>> + Send + 'static,
    {
        if let Err(error) = self.inner.assert_usable() {
            return ready(Err(error));
        }
        let inner = Arc::clone(&self.inner);
        self.inner
            .enqueue(async move {
                inner.assert_healthy()?;
                job.await
            })
            .boxed()
    }

    /// Internal: a conversation document's current incarnation and value, for
    /// a job already running on the line (see [`Session::read_on_line`]).
    /// Absent documents are `None`.
    ///
    /// # Errors
    ///
    /// Storage failures and definition mismatches.
    pub async fn conversation_document_on_line<D: DocToken>(
        &self,
        token: &D,
        conversation_id: D::Locator<'_>,
        cx: &Context,
    ) -> SessionResult<Option<OnLineDocument>> {
        let resolved = resolve_token_address(token, conversation_id);
        let definition = &erase(token);
        let Some(loaded) = self
            .inner
            .load_document(
                definition.clone(),
                resolved.id,
                resolved.address,
                cx.clone(),
            )
            .await?
        else {
            return Ok(None);
        };
        check_record_scope(definition.as_ref(), &loaded.record)?;
        check_record_version(definition.as_ref(), &loaded.record, loaded.stored_version())?;
        Ok(Some(OnLineDocument {
            record: loaded.record.clone(),
            version: loaded.value_version,
            value: loaded.value(),
        }))
    }

    /// Committed immutable value of a document; `None` when absent. A cached
    /// tracker answers without the line; a cold load runs on the line.
    pub fn snapshot<D: DocToken>(
        &self,
        token: &D,
        locator: D::Locator<'_>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        let resolved = resolve_token_address(token, locator);
        self.snapshot_at(&erase(token), resolved, cx)
    }

    /// Disposable, read-only Chord state bound to the document's current
    /// committed incarnation; `None` when absent. Never creates a document.
    pub fn document_state<D: DocToken>(
        &self,
        token: &D,
        locator: D::Locator<'_>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentState>>> {
        let resolved = resolve_token_address(token, locator);
        self.document_state_at(&erase(token), resolved, cx)
    }

    /// Serialized exact-frame watch of the document's current committed
    /// incarnation; `None` when absent. Never creates a document. Cancelling
    /// `cx` cancels the watch.
    pub fn watch_doc<D: DocToken>(
        &self,
        token: &D,
        locator: D::Locator<'_>,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentWatch>>> {
        let resolved = resolve_token_address(token, locator);
        self.watch_doc_at(&erase(token), resolved, cx)
    }

    /// Value of a rewindable conversation document as of the visible entry
    /// `at`; `None` when it did not exist then.
    pub fn snapshot_as_of<D: RewindableDocToken>(
        &self,
        token: &D,
        locator: D::Locator<'_>,
        at: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        let resolved = resolve_token_address(token, locator);
        self.snapshot_as_of_at(&erase(token), resolved, at, cx)
    }

    /// Committed value of the document at `resolved`; `None` when absent.
    pub(crate) fn snapshot_at(
        &self,
        definition: &Definition,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        if let Err(error) = self.inner.assert_usable() {
            return ready(Err(error));
        }
        let definition = definition.clone();
        let cached = self
            .inner
            .lock()
            .documents
            .get(&resolved.id)
            .filter(|cached| cached.value_version == definition.version())
            .cloned();
        let loaded = if let Some(cached) = cached {
            ready(Ok(Some(cached)))
        } else {
            let inner = Arc::clone(&self.inner);
            let (definition, cx) = (definition.clone(), cx.clone());
            self.inner
                .enqueue(async move {
                    inner.assert_healthy()?;
                    inner
                        .load_document(definition, resolved.id, resolved.address, cx)
                        .await
                })
                .boxed()
        };
        async move {
            let Some(loaded) = loaded.await? else {
                return Ok(None);
            };
            check_record_scope(definition.as_ref(), &loaded.record)?;
            check_record_version(definition.as_ref(), &loaded.record, loaded.stored_version())?;
            Ok(Some(loaded.value()))
        }
        .boxed()
    }

    /// Attached read-only replicated state of the document at `resolved`,
    /// hydrated in O(1) from the cached tracker; `None` when absent.
    pub(crate) fn document_state_at(
        &self,
        definition: &Definition,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentState>>> {
        if let Err(error) = self.inner.assert_usable() {
            return ready(Err(error));
        }
        let inner = Arc::clone(&self.inner);
        let (definition, cx) = (definition.clone(), cx.clone());
        self.inner
            .enqueue(async move {
                inner.assert_healthy()?;
                let Some(loaded) = inner
                    .load_document(definition.clone(), resolved.id, resolved.address, cx)
                    .await?
                else {
                    return Ok(None);
                };
                let (source, detach) =
                    inner.attach_document(&definition, &loaded, |value, release| {
                        Observer::State(CommittedStateSource::new(&value, release))
                    })?;
                let Observer::State(source) = source else {
                    unreachable!("the factory creates a state source")
                };
                match replicated_state_from_source(&source, ReplicatedStateSourceOptions::default())
                {
                    Ok(state) => Ok(Some(state)),
                    Err(error) => {
                        detach();
                        Err(SessionError::other(error))
                    }
                }
            })
            .boxed()
    }

    /// Serialized exact-frame watch of the document at `resolved`; `None` when
    /// absent. Cancelling `cx` cancels the watch.
    pub(crate) fn watch_doc_at(
        &self,
        definition: &Definition,
        resolved: ResolvedAddress,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentWatch>>> {
        if let Err(error) = self.inner.assert_usable() {
            return ready(Err(error));
        }
        let signal = cx.abort_signal();
        let inner = Arc::clone(&self.inner);
        let (definition, job_cx) = (definition.clone(), cx.clone());
        let job_signal = signal.clone();
        let watch = self.inner.enqueue(async move {
            inner.assert_healthy()?;
            check_cancelled(job_signal.as_ref())?;
            let loaded = inner
                .load_document(definition.clone(), resolved.id, resolved.address, job_cx)
                .await?;
            check_cancelled(job_signal.as_ref())?;
            let Some(loaded) = loaded else {
                return Ok(None);
            };
            let (watch, _) = inner.attach_document(&definition, &loaded, |value, release| {
                Observer::Watch(CommittedWatch::new(value, release, None))
            })?;
            let Observer::Watch(watch) = watch else {
                unreachable!("the factory creates a watch")
            };
            Ok(Some(watch))
        });
        async move {
            let Some(watch) = watch.await? else {
                return Ok(None);
            };
            if let Some(signal) = &signal {
                if let Some(reason) = signal.reason() {
                    watch.cancel();
                    return Err(SessionError::Aborted(reason));
                }
                watch.observe_cancellation(signal)?;
            }
            Ok(Some(watch))
        }
        .boxed()
    }

    /// Value of a rewindable conversation document as of the visible entry `at`.
    pub(crate) fn snapshot_as_of_at(
        &self,
        definition: &Definition,
        resolved: ResolvedAddress,
        at: EntryId,
        cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        if let Err(error) = self.inner.assert_usable() {
            return ready(Err(error));
        }
        let DocumentScope::Conversation { conversation_id } = resolved.address.scope else {
            return ready(Err(SessionError::type_error(
                "Session.snapshotAsOf() requires a conversation document",
            )));
        };
        let inner = Arc::clone(&self.inner);
        let (definition, cx) = (definition.clone(), cx.clone());
        self.inner
            .enqueue(async move {
                inner.assert_healthy()?;
                let storage = &inner.storage;
                let Some(stored_entry) = storage.entry_in(conversation_id, at, &cx).await? else {
                    return Err(SessionError::error(format!(
                        "Entry {at} is not visible from conversation {conversation_id}"
                    )));
                };
                let address = DocumentAddress {
                    scope: DocumentScope::Conversation {
                        conversation_id: stored_entry.entry.conversation_id,
                    },
                    ..resolved.address
                };
                let point = DocumentPoint::At(stored_entry.commit_seq);
                let Some(record) = storage.find_document(&address, point, &cx).await? else {
                    return Ok(None);
                };
                let Some(stored) = storage.document(record.id, point, &cx).await? else {
                    return Err(SessionError::error(format!(
                        "Historical document {} ({}) cannot be read",
                        record.id, record.kind
                    )));
                };
                Ok(Some(materialize_document(definition.as_ref(), &stored)?))
            })
            .boxed()
    }

    /// Seal admission, settle admitted commits, then close storage.
    ///
    /// # Errors
    ///
    /// The Storage close failure, or `cx`'s abort reason when the caller stops
    /// waiting; closing continues either way.
    pub fn close(&self, cx: &Context) -> impl Future<Output = SessionResult<()>> + Send + 'static {
        let (closing, listeners) = {
            let mut state = self.inner.lock();
            if let Some(closing) = &state.closing {
                (closing.clone(), Vec::new())
            } else {
                let cleanup = without_abort_signal(cx);
                let inner = Arc::clone(&self.inner);
                // Seal admission before anything else runs, then stop
                // observers; admitted work settles before Storage closes.
                let handle = tokio::spawn(async move {
                    inner.hooks.before_close().await;
                    let line = Arc::clone(&inner);
                    inner
                        .enqueue(async move {
                            {
                                let mut state = line.lock();
                                state.commit_listeners.clear();
                                state.documents.clear();
                            }
                            Ok(line.storage.close(&cleanup).await?)
                        })
                        .await
                });
                let closing: Closing = join(handle).boxed().shared();
                state.closing = Some(closing.clone());
                let listeners = std::mem::take(&mut state.close_listeners);
                (closing, listeners)
            }
        };
        for (_, listener) in listeners {
            listener();
        }
        let cx = cx.clone();
        async move {
            match await_with_context(closing, &cx).await {
                Ok(result) => result,
                Err(reason) => Err(SessionError::Aborted(reason)),
            }
        }
    }

    /// Register a synchronous post-adoption listener. It must not block or
    /// call Session operations.
    ///
    /// # Errors
    ///
    /// The Session is closed or poisoned.
    pub fn subscribe_commits(&self, listener: CommitListener) -> SessionResult<Unsubscribe> {
        self.inner.subscribe_commits(listener)
    }

    /// Register a listener called synchronously when close begins. It must not
    /// block or call Session operations.
    ///
    /// # Errors
    ///
    /// The Session is closed or poisoned.
    pub fn subscribe_close(&self, listener: CloseListener) -> SessionResult<Unsubscribe> {
        self.inner.subscribe_close(listener)
    }

    /// Drop every loaded tracker on the mutation line; later access cold-loads
    /// from Storage.
    pub fn unload_documents(&self) -> impl Future<Output = SessionResult<()>> + Send + 'static {
        let inner = Arc::clone(&self.inner);
        self.inner.enqueue(async move {
            inner.lock().documents.clear();
            Ok(())
        })
    }
}

/// A conversation document's current incarnation and value, read on the line.
#[derive(Clone, Debug)]
pub struct OnLineDocument {
    pub record: DocumentRecord,
    pub version: u64,
    pub value: Arc<JsonObject>,
}

fn check_cancelled(signal: Option<&AbortSignal>) -> SessionResult<()> {
    match signal.and_then(AbortSignal::reason) {
        Some(reason) => Err(SessionError::Aborted(reason)),
        None => Ok(()),
    }
}

/// An observer attached to one committed incarnation.
#[derive(Clone)]
enum Observer {
    State(CommittedStateSource),
    Watch(DocumentWatch),
}

impl Observer {
    fn advance(&self, value: ObservedDocumentValue, ops: Ops, cx: &Context) {
        match self {
            // A document state's frames carry no caller cancellation; a watch
            // observes its own cancellation.
            Self::State(source) => source.advance(&value, ops, without_abort_signal(cx)),
            Self::Watch(watch) => watch.advance(value, ops, cx.clone()),
        }
    }

    fn close_session(&self) {
        match self {
            Self::State(source) => source.close_session(),
            Self::Watch(watch) => watch.close_session(),
        }
    }
}

impl SessionInner {
    fn lock(&self) -> MutexGuard<'_, SessionState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn arc(&self) -> Arc<SessionInner> {
        self.this
            .upgrade()
            .expect("a live Session reference exists while its methods run")
    }

    /// Enqueue `job` on the mutation line now. It runs after every earlier
    /// job settles, even if the returned future is dropped.
    fn enqueue<T: Send + 'static>(
        &self,
        job: impl Future<Output = SessionResult<T>> + Send + 'static,
    ) -> impl Future<Output = SessionResult<T>> + Send + 'static {
        let (done, next) = oneshot::channel::<()>();
        let previous = self.lock().tail.replace(next);
        let handle = tokio::spawn(async move {
            if let Some(previous) = previous {
                // Completion or a dropped sender (a panicked job) both release the line.
                let _ = previous.await;
            }
            let result = job.await;
            drop(done);
            result
        });
        join(handle)
    }

    fn assert_usable(&self) -> SessionResult<()> {
        let state = self.lock();
        if state.closing.is_some() {
            return Err(SessionError::error("Session is closed"));
        }
        Self::healthy(&state)
    }

    fn assert_healthy(&self) -> SessionResult<()> {
        Self::healthy(&self.lock())
    }

    fn healthy(state: &SessionState) -> SessionResult<()> {
        match &state.poison {
            Some(cause) => Err(SessionError::Poisoned {
                cause: Arc::clone(cause),
            }),
            None => Ok(()),
        }
    }

    fn poison(&self, error: &SessionError) {
        self.lock().poison = Some(Arc::new(error.clone()));
    }

    fn subscribe_commits(&self, listener: CommitListener) -> SessionResult<Unsubscribe> {
        self.assert_usable()?;
        let mut state = self.lock();
        let id = state.next_listener;
        state.next_listener += 1;
        state.commit_listeners.push((id, listener));
        let this = self.this.clone();
        Ok(Unsubscribe {
            remove: Box::new(move || {
                let Some(inner) = this.upgrade() else {
                    return false;
                };
                let mut state = inner.lock();
                let before = state.commit_listeners.len();
                state.commit_listeners.retain(|(other, _)| *other != id);
                state.commit_listeners.len() != before
            }),
        })
    }

    fn subscribe_close(&self, listener: CloseListener) -> SessionResult<Unsubscribe> {
        self.assert_usable()?;
        let mut state = self.lock();
        let id = state.next_listener;
        state.next_listener += 1;
        state.close_listeners.push((id, listener));
        let this = self.this.clone();
        Ok(Unsubscribe {
            remove: Box::new(move || {
                let Some(inner) = this.upgrade() else {
                    return false;
                };
                let mut state = inner.lock();
                let before = state.close_listeners.len();
                state.close_listeners.retain(|(other, _)| *other != id);
                state.close_listeners.len() != before
            }),
        })
    }

    async fn run_commit<T, F, Fut>(
        self: Arc<Self>,
        change: F,
        cx: Context,
        scope: TransactionScope,
    ) -> SessionResult<T>
    where
        F: FnOnce(Tx) -> Fut,
        Fut: Future<Output = SessionResult<T>>,
    {
        self.assert_healthy()?;
        check_cancelled(cx.abort_signal().as_ref())?;
        let host: Arc<dyn TransactionHost> = Arc::clone(&self) as Arc<dyn TransactionHost>;
        let tx = Tx::new(host, cx.clone(), scope);
        let result = match change(tx.clone()).await {
            Ok(result) => result,
            Err(error) => {
                tx.settle_failure().await;
                return Err(error);
            }
        };
        let writes = tx.settle_success().await?;
        if writes.is_empty() {
            tx.discard();
            return Ok(result);
        }
        // Once admitted, caller cancellation does not interrupt Storage settlement.
        let seq = match self
            .storage
            .commit(&writes, &without_abort_signal(&cx))
            .await
        {
            Ok(seq) => seq,
            Err(error) => {
                tx.discard();
                let error = SessionError::from(error);
                // Callback errors never reach this branch; StorageRejected
                // alone guarantees that no batch effect committed.
                if !matches!(&error, SessionError::Storage(storage) if storage.is_rejected()) {
                    self.poison(&error);
                }
                return Err(error);
            }
        };
        let documents = match tx.adopt(seq) {
            Ok(documents) => documents,
            Err(error) => {
                // Storage already committed; a failed adoption leaves memory
                // behind durable state.
                self.poison(&error);
                return Err(error);
            }
        };
        self.publish(seq, writes, documents, &cx);
        Ok(result)
    }

    fn publish(
        &self,
        seq: Seq,
        writes: Vec<StorageWrite>,
        documents: Vec<DocumentCommitChange>,
        cx: &Context,
    ) {
        let listeners: Vec<CommitListener> = {
            let state = self.lock();
            if state.commit_listeners.is_empty() {
                return;
            }
            state
                .commit_listeners
                .iter()
                .map(|(_, listener)| Arc::clone(listener))
                .collect()
        };
        let mut changes: Vec<CommitChange> = writes
            .into_iter()
            .filter_map(|write| match write {
                StorageWrite::Conversation { value } => Some(CommitChange::Conversation(value)),
                StorageWrite::Entry { value } => Some(CommitChange::Entry(value)),
                StorageWrite::Task { value } => Some(CommitChange::Task(value)),
                StorageWrite::Submission { value } => Some(CommitChange::Submission(value)),
                StorageWrite::DocumentCreate { .. }
                | StorageWrite::DocumentCopy { .. }
                | StorageWrite::DocumentChange { .. }
                | StorageWrite::DocumentRetire { .. } => None,
            })
            .collect();
        changes.extend(documents.into_iter().map(CommitChange::Document));
        let publication = CommitPublication { seq, changes };
        for listener in listeners {
            listener(&publication, cx);
        }
    }

    /// Attach an observer to one committed incarnation: check the definition,
    /// then forward this incarnation's committed changes and close. The
    /// returned detach removes both subscriptions.
    fn attach_document(
        &self,
        definition: &Definition,
        loaded: &Arc<LoadedDocument>,
        create: impl FnOnce(ObservedDocumentValue, Box<dyn FnOnce() + Send>) -> Observer,
    ) -> SessionResult<(Observer, Arc<dyn Fn() + Send + Sync>)> {
        check_record_scope(definition.as_ref(), &loaded.record)?;
        check_record_version(definition.as_ref(), &loaded.record, loaded.stored_version())?;
        let subscriptions: Arc<Mutex<Vec<Unsubscribe>>> = Arc::default();
        let detach: Arc<dyn Fn() + Send + Sync> = {
            let subscriptions = Arc::clone(&subscriptions);
            Arc::new(move || {
                let taken = std::mem::take(
                    &mut *subscriptions.lock().unwrap_or_else(PoisonError::into_inner),
                );
                for subscription in taken {
                    subscription.unsubscribe();
                }
            })
        };
        let release = Arc::clone(&detach);
        let observer = create(Some(loaded.value()), Box::new(move || release()));
        let observed_version = Arc::new(Mutex::new(loaded.value_version));
        let record_id = loaded.record.id;
        let commit = {
            let observer = observer.clone();
            self.subscribe_commits(Arc::new(move |publication, cx| {
                for change in &publication.changes {
                    let CommitChange::Document(DocumentCommitChange::Document {
                        record,
                        version,
                        value,
                        ops,
                        ..
                    }) = change
                    else {
                        continue;
                    };
                    if record.id != record_id {
                        continue;
                    }
                    let ops = observed_operations(&observed_version, *version, value, ops);
                    // A migration-only base changes nothing for an observer of
                    // the new version.
                    if ops.is_empty() {
                        continue;
                    }
                    observer.advance(value.clone(), ops, cx);
                }
            }))?
        };
        let close = {
            let observer = observer.clone();
            self.subscribe_close(Arc::new(move || observer.close_session()))
        };
        let close = match close {
            Ok(close) => close,
            Err(error) => {
                commit.unsubscribe();
                return Err(error);
            }
        };
        subscriptions
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .extend([commit, close]);
        Ok((observer, detach))
    }

    async fn load_document(
        &self,
        definition: Definition,
        address_id: String,
        address: DocumentAddress,
        cx: Context,
    ) -> SessionResult<Option<Arc<LoadedDocument>>> {
        {
            let mut state = self.lock();
            if let Some(cached) = state.documents.get(&address_id) {
                // A tracker serves only tokens of the version its value was
                // materialized for; others reload from Storage.
                if cached.value_version == definition.version() {
                    return Ok(Some(Arc::clone(cached)));
                }
                state.documents.remove(&address_id);
            }
        }
        let Some(record) = self
            .storage
            .find_document(&address, DocumentPoint::Current, &cx)
            .await?
        else {
            return Ok(None);
        };
        let Some(stored) = self
            .storage
            .document(record.id, DocumentPoint::Current, &cx)
            .await?
        else {
            return Err(SessionError::error(format!(
                "Current document {} ({}) cannot be read",
                record.id, record.kind
            )));
        };
        let stored_version = stored.version;
        let deltas_since_base = stored.deltas_since_base;
        let stored_record = stored.record.clone();
        let value = materialize_document(definition.as_ref(), &stored)?;
        let loaded = Arc::new(LoadedDocument::new(
            address_id.clone(),
            stored_record,
            stored_version,
            definition.version(),
            deltas_since_base,
            track(JsonValue::Object(value))?,
        ));
        self.lock()
            .documents
            .insert(address_id, Arc::clone(&loaded));
        Ok(Some(loaded))
    }
}

impl TransactionHost for SessionInner {
    fn storage(&self) -> &Arc<dyn Storage> {
        &self.storage
    }

    fn cached(&self, address_id: &str) -> Option<Arc<LoadedDocument>> {
        self.lock().documents.get(address_id).cloned()
    }

    fn load(
        &self,
        definition: Definition,
        address_id: String,
        address: DocumentAddress,
        cx: Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<LoadedDocument>>>> {
        let inner = self.arc();
        async move {
            inner
                .load_document(definition, address_id, address, cx)
                .await
        }
        .boxed()
    }

    fn install(&self, document: LoadedDocument) {
        self.lock()
            .documents
            .insert(document.address_id.clone(), Arc::new(document));
    }

    fn evict(&self, address_id: &str, record_id: DocumentId) {
        let mut state = self.lock();
        if state
            .documents
            .get(address_id)
            .is_some_and(|cached| cached.record.id == record_id)
        {
            state.documents.remove(address_id);
        }
    }

    fn conversation_created(
        &self,
        tx: Tx,
        record: ConversationRecord,
    ) -> BoxFuture<'static, SessionResult<()>> {
        self.hooks.conversation_created(tx, record)
    }
}

/// Operations an observer applies for one committed change. An observer
/// hydrated under another definition version holds a differently shaped
/// value, so it receives the new value as a root replacement instead of
/// operations for that shape.
fn observed_operations(
    observed: &Mutex<u64>,
    version: Option<u64>,
    value: &ObservedDocumentValue,
    ops: &Ops,
) -> Ops {
    let Some(value) = value else {
        return Arc::clone(&RETIREMENT_OPERATIONS);
    };
    let version = version.expect("a published document value carries its version");
    let mut observed = observed.lock().unwrap_or_else(PoisonError::into_inner);
    if version == *observed {
        return Arc::clone(ops);
    }
    *observed = version;
    Arc::from(vec![Op::Replace(JsonValue::Object(Arc::clone(value)))])
}
