//! Session kernel: one mutation line, the loaded document tracker cache, and
//! committed publication.
//!
//! Only committed state is observable. Every commit callback, preparation,
//! Storage settlement, adoption, and publication enqueue runs while the line is
//! held; listeners run later.

use std::collections::HashMap;
use std::future::Future;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};

use eukhe_chord::context::{
    await_with_context, without_abort_signal, AbortSignal, Context, BACKGROUND_CONTEXT,
};
use eukhe_chord::delta::{track, Op};
use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_chord::{
    replicated_state_from_source, AttachedReplicatedState, ReplicatedStateSourceOptions,
};
use futures::future::{BoxFuture, FutureExt, Shared};
use tokio::sync::{oneshot, watch};

use crate::documents::{
    check_record_scope, check_record_version, materialize_document, resolve_token_address,
    DocToken, ResolvedAddress, RewindableDocToken,
};
use crate::types::{
    CommitChange, CommitPublication, ConversationRecord, DocumentAddress, DocumentCommitChange,
    DocumentId, DocumentPoint, DocumentRecord, DocumentScope, EntryId, Seq, Storage, StorageWrite,
};

use super::error::{SessionError, SessionResult};
use super::guarded::{FailureLatch, GuardedStorage};
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

/// A Session component's own commit listener (see
/// [`Session::observe_commits`]): its state follows each commit, so a failure
/// fails the Session.
pub type InternalCommitListener =
    Arc<dyn Fn(&CommitPublication, &Context) -> SessionResult<()> + Send + Sync>;

/// The Session's wall clock for task lifecycle times, in milliseconds (TS
/// `() => number`).
pub type SessionClock = Arc<dyn Fn() -> f64 + Send + Sync>;

/// Why a Session ended: `close()`, or a failed Storage call, whose error it
/// carries.
#[derive(Clone, Debug)]
pub enum SessionEnd {
    /// `close()` closed it.
    Closed,
    /// The first error that failed it.
    Failed {
        /// What failed the Session, usually a storage error.
        error: Arc<SessionError>,
    },
}

/// Options of [`create_session`].
#[derive(Clone, Default)]
pub struct SessionOptions {
    /// The wall clock for task times; default `Date.now`.
    pub now: Option<SessionClock>,
}

impl std::fmt::Debug for SessionOptions {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("SessionOptions")
            .field("now", &self.now.is_some())
            .finish()
    }
}

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

    /// The Session's failure, and errors of listeners, which never fail what
    /// ran them (TS `report()`). A plain Session drops them.
    fn report(&self, _error: SessionError) {}
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
    /// The Session's own listeners, such as its scheduler's: they keep memory
    /// in step with storage, so a failure fails it.
    internal_listeners: Vec<(u64, InternalCommitListener)>,
    close_listeners: Vec<(u64, CloseListener)>,
    next_listener: u64,
    tail: Option<oneshot::Receiver<()>>,
    closing: Option<Closing>,
    failure: Option<Arc<SessionError>>,
}

struct SessionInner {
    /// The Storage behind the failure guard; every component reads and
    /// writes through it.
    storage: Arc<dyn Storage>,
    hooks: Arc<dyn SessionHooks>,
    now: SessionClock,
    state: Mutex<SessionState>,
    /// Set the moment the Session fails, before work underway has ended.
    failed: watch::Sender<Option<Arc<SessionError>>>,
    /// Set once the Session has closed, Storage included.
    closed: watch::Sender<Option<SessionEnd>>,
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

/// Open a Session kernel over one storage backend. `options.now` is the wall
/// clock for task times; default `Date.now`. The first error a Storage method
/// returns fails the Session (`SessionFailed`); see [`Session`].
#[must_use]
pub fn create_session(storage: Arc<dyn Storage>, options: SessionOptions) -> Session {
    Session::with_hooks(storage, Arc::new(NoSessionHooks), options.now)
}

/// `Date.now()`: wall-clock milliseconds since the Unix epoch.
#[must_use]
pub fn system_now() -> f64 {
    let elapsed = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default();
    #[expect(
        clippy::cast_precision_loss,
        reason = "epoch milliseconds stay below 2^53"
    )]
    let millis = elapsed.as_millis() as f64;
    millis
}

fn ready<T: Send + 'static>(result: SessionResult<T>) -> BoxFuture<'static, SessionResult<T>> {
    futures::future::ready(result).boxed()
}

impl Session {
    /// A plain Session over `storage` with the system clock.
    #[must_use]
    pub fn new(storage: Arc<dyn Storage>) -> Self {
        Self::with_hooks(storage, Arc::new(NoSessionHooks), None)
    }

    /// A Session whose protected hooks are `hooks`; `now` is the wall clock
    /// for task lifecycle times, by default `Date.now`.
    #[must_use]
    pub fn with_hooks(
        storage: Arc<dyn Storage>,
        hooks: Arc<dyn SessionHooks>,
        now: Option<SessionClock>,
    ) -> Self {
        Self {
            inner: Arc::new_cyclic(|this: &Weak<SessionInner>| {
                let latch: Weak<dyn FailureLatch> = this.clone();
                SessionInner {
                    storage: Arc::new(GuardedStorage::new(storage, latch)),
                    hooks,
                    now: now.unwrap_or_else(|| Arc::new(system_now)),
                    state: Mutex::new(SessionState::default()),
                    failed: watch::channel(None).0,
                    closed: watch::channel(None).0,
                    this: this.clone(),
                }
            }),
        }
    }

    /// The Storage behind the Session's failure guard; every component reads
    /// and writes through it.
    #[must_use]
    pub fn storage(&self) -> &Arc<dyn Storage> {
        &self.inner.storage
    }

    /// Settles once the Session has closed, Storage included: after
    /// `close()`, or after the first failed Storage call, which closes the
    /// Session itself. A failed Session is reopened from Storage; nothing else
    /// is left to clean up.
    pub fn closed(&self) -> impl Future<Output = SessionEnd> + Send + 'static {
        let mut closed = self.inner.closed.subscribe();
        async move {
            match closed.wait_for(Option::is_some).await {
                Ok(end) => end.clone().unwrap_or(SessionEnd::Closed),
                // The sender lives as long as the Session.
                Err(_) => SessionEnd::Closed,
            }
        }
    }

    /// Internal: the error that failed the Session, if one did.
    #[must_use]
    pub fn failure(&self) -> Option<Arc<SessionError>> {
        self.inner.lock().failure.clone()
    }

    /// Internal: resolves with `SessionFailed` the moment the Session fails,
    /// before work underway has ended; never resolves otherwise.
    pub fn failed(&self) -> impl Future<Output = SessionError> + Send + 'static {
        let mut failed = self.inner.failed.subscribe();
        async move {
            let cause = failed
                .wait_for(Option::is_some)
                .await
                .ok()
                .and_then(|failure| failure.clone());
            match cause {
                Some(cause) => SessionError::session_failed(cause),
                // The sender lives as long as the Session.
                None => std::future::pending().await,
            }
        }
    }

    /// Internal: fail the Session with `error`, the first wins, and report it
    /// once. Admission ends, and close listeners run now; they read the error
    /// from [`Session::failure`]. The Storage guard calls this; the Harness
    /// also calls it for a failure in its scheduler's own commits.
    pub fn fail(&self, error: SessionError) {
        self.inner.fail(error);
    }

    /// Internal: the Session's failure, and errors of listeners, which never
    /// fail what ran them.
    pub fn report(&self, error: SessionError) {
        self.inner.hooks.report(error);
    }

    /// Internal: [`Session::report`] as a value, for observers that outlive
    /// the call.
    #[must_use]
    pub fn reporter(&self) -> Arc<dyn Fn(SessionError) + Send + Sync> {
        self.inner.reporter()
    }

    /// Internal: `SessionFailed` when failed, else `Session is closed` when
    /// closing.
    ///
    /// # Errors
    ///
    /// As described.
    pub fn assert_usable(&self) -> SessionResult<()> {
        self.inner.assert_usable()
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
                let reporter = inner.reporter();
                let options = ReplicatedStateSourceOptions {
                    on_error: Some(Arc::new(move |error| reporter(SessionError::other(error)))),
                };
                match replicated_state_from_source(&source, options) {
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
            let report = inner.reporter();
            let (watch, _) = inner.attach_document(&definition, &loaded, |value, release| {
                Observer::Watch(CommittedWatch::new(value, release, report, None))
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
        self.inner.close(cx)
    }

    /// Register a synchronous post-adoption listener. It must not block or
    /// call Session operations. A Rust listener cannot throw; TS reports a
    /// throwing one.
    ///
    /// # Errors
    ///
    /// The Session is closed or failed.
    pub fn subscribe_commits(&self, listener: CommitListener) -> SessionResult<Unsubscribe> {
        self.inner.subscribe_commits(listener)
    }

    /// Internal: [`Session::subscribe_commits`] for the Session's own
    /// components, whose state follows each commit. A failure leaves that
    /// state behind storage, so it fails the Session instead of being
    /// reported. They run before host listeners.
    ///
    /// # Errors
    ///
    /// The Session is closed or failed.
    pub fn observe_commits(&self, listener: InternalCommitListener) -> SessionResult<Unsubscribe> {
        self.inner.observe_commits(listener)
    }

    /// Register a listener called synchronously when close begins, also when
    /// a failure closes the Session ([`Session::failure`] is then set). It
    /// must not block or call Session operations.
    ///
    /// # Errors
    ///
    /// The Session is closed or failed.
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

    fn close_session(&self, failure: Option<Arc<SessionError>>) {
        match self {
            Self::State(source) => source.close_session(),
            Self::Watch(watch) => watch.close_session(failure),
        }
    }
}

impl SessionInner {
    fn lock(&self) -> MutexGuard<'_, SessionState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// `report()` as a value, for observers that outlive the call.
    fn reporter(&self) -> Arc<dyn Fn(SessionError) + Send + Sync> {
        let this = self.this.clone();
        Arc::new(move |error| {
            if let Some(inner) = this.upgrade() {
                inner.hooks.report(error);
            }
        })
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
        join(tokio::spawn(self.line_turn(job)))
    }

    /// Take the next turn on the mutation line now; the returned future waits
    /// for every earlier job, runs `job`, then frees the line. Dropping it
    /// frees the line, also mid-job, so only a task that runs to completion
    /// awaits it directly.
    fn line_turn<T: Send + 'static>(
        &self,
        job: impl Future<Output = SessionResult<T>> + Send + 'static,
    ) -> impl Future<Output = SessionResult<T>> + Send + 'static {
        let (done, next) = oneshot::channel::<()>();
        let previous = self.lock().tail.replace(next);
        async move {
            if let Some(previous) = previous {
                // Completion or a dropped sender (a panicked job) both release the line.
                let _ = previous.await;
            }
            let result = job.await;
            drop(done);
            result
        }
    }

    /// `SessionFailed` when failed, else `Session is closed` when closing.
    fn assert_usable(&self) -> SessionResult<()> {
        let state = self.lock();
        Self::healthy(&state)?;
        if state.closing.is_some() {
            return Err(SessionError::error("Session is closed"));
        }
        Ok(())
    }

    fn assert_healthy(&self) -> SessionResult<()> {
        Self::healthy(&self.lock())
    }

    fn healthy(state: &SessionState) -> SessionResult<()> {
        match &state.failure {
            Some(cause) => Err(SessionError::session_failed(Arc::clone(cause))),
            None => Ok(()),
        }
    }

    /// Fail the Session with `error`; the first wins. Admission ends, close
    /// listeners run now, the Session then closes itself in the background,
    /// and the error is reported once.
    fn fail(&self, error: SessionError) {
        let error = Arc::new(error);
        {
            let mut state = self.lock();
            if state.failure.is_some() {
                return;
            }
            state.failure = Some(Arc::clone(&error));
        }
        self.failed.send_replace(Some(Arc::clone(&error)));
        // Seal first, so a report handler that calls back finds the Session
        // failed. Closing runs the close listeners synchronously; a failing
        // backend close is the caller's to see, and here nobody waits.
        let closing = self.arc().close(&BACKGROUND_CONTEXT);
        tokio::spawn(async move {
            let _ = closing.await;
        });
        self.hooks.report((*error).clone());
    }

    /// Seal admission, settle admitted commits, then close storage.
    fn close(
        self: &Arc<Self>,
        cx: &Context,
    ) -> impl Future<Output = SessionResult<()>> + Send + 'static {
        let (closing, listeners) = {
            let mut state = self.lock();
            if let Some(closing) = &state.closing {
                (closing.clone(), Vec::new())
            } else {
                let cleanup = without_abort_signal(cx);
                let inner = Arc::clone(self);
                // Seal admission before anything else runs, then stop
                // observers; admitted work settles before Storage closes.
                let handle = tokio::spawn(async move {
                    inner.hooks.before_close().await;
                    let line = Arc::clone(&inner);
                    // On the line from this task, without spawning another:
                    // as TS chains the job, Storage starts closing, refusing
                    // new calls, before work woken meanwhile runs on.
                    let result = inner
                        .line_turn(async move {
                            {
                                let mut state = line.lock();
                                state.commit_listeners.clear();
                                state.internal_listeners.clear();
                                state.documents.clear();
                            }
                            match line.storage.close(&cleanup).await {
                                Ok(()) => Ok(()),
                                Err(error) => {
                                    let error = SessionError::from(error);
                                    // A Storage that cannot close is a failed
                                    // one; an earlier failure stays the cause.
                                    let first = {
                                        let mut state = line.lock();
                                        if state.failure.is_none() {
                                            state.failure = Some(Arc::new(error.clone()));
                                            true
                                        } else {
                                            false
                                        }
                                    };
                                    if first {
                                        line.failed.send_replace(Some(Arc::new(error.clone())));
                                        line.hooks.report(error.clone());
                                    }
                                    Err(error)
                                }
                            }
                        })
                        .await;
                    let end = match inner.lock().failure.clone() {
                        Some(error) => SessionEnd::Failed { error },
                        None => SessionEnd::Closed,
                    };
                    inner.closed.send_replace(Some(end));
                    result
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

    fn observe_commits(&self, listener: InternalCommitListener) -> SessionResult<Unsubscribe> {
        self.assert_usable()?;
        let mut state = self.lock();
        let id = state.next_listener;
        state.next_listener += 1;
        state.internal_listeners.push((id, listener));
        let this = self.this.clone();
        Ok(Unsubscribe {
            remove: Box::new(move || {
                let Some(inner) = this.upgrade() else {
                    return false;
                };
                let mut state = inner.lock();
                let before = state.internal_listeners.len();
                state.internal_listeners.retain(|(other, _)| *other != id);
                state.internal_listeners.len() != before
            }),
        })
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
        // A callback that caught a failed read must not commit, nor succeed
        // as if it had.
        let result = match change(tx.clone())
            .await
            .and_then(|result| self.assert_healthy().map(|()| result))
        {
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
                // The guard has failed the Session.
                tx.discard();
                return Err(SessionError::from(error));
            }
        };
        let documents = match tx.adopt(seq) {
            Ok(documents) => documents,
            Err(error) => {
                // Storage already committed; a failed adoption leaves memory
                // behind durable state.
                self.fail(error.clone());
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
        let (internal, listeners): (Vec<InternalCommitListener>, Vec<CommitListener>) = {
            let state = self.lock();
            if state.commit_listeners.is_empty() && state.internal_listeners.is_empty() {
                return;
            }
            (
                state
                    .internal_listeners
                    .iter()
                    .map(|(_, listener)| Arc::clone(listener))
                    .collect(),
                state
                    .commit_listeners
                    .iter()
                    .map(|(_, listener)| Arc::clone(listener))
                    .collect(),
            )
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
        // The commit is durable: a failing listener neither fails the commit
        // nor skips the others.
        for listener in internal {
            if let Err(error) = listener(&publication, cx) {
                self.fail(error);
            }
        }
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
            self.observe_commits(Arc::new(move |publication, cx| {
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
                Ok(())
            }))?
        };
        let close = {
            let observer = observer.clone();
            let session = self.this.clone();
            self.subscribe_close(Arc::new(move || {
                let failure = session
                    .upgrade()
                    .and_then(|inner| inner.lock().failure.clone());
                observer.close_session(failure);
            }))
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

impl FailureLatch for SessionInner {
    fn failure(&self) -> Option<Arc<SessionError>> {
        self.lock().failure.clone()
    }

    fn fail(&self, error: SessionError) {
        SessionInner::fail(self, error);
    }
}

impl TransactionHost for SessionInner {
    fn storage(&self) -> &Arc<dyn Storage> {
        &self.storage
    }

    fn now(&self) -> f64 {
        (self.now)()
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
