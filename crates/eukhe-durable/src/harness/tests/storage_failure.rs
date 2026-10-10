//! Port of `test/harness-storage-failure.test.ts`.
//!
//! Tests with no Rust counterpart, skipped:
//! - "reports a listener or onReport whose promise rejects, without an
//!   unhandled rejection": Rust commit/close listeners and `on_report` are
//!   synchronous and cannot reject; there are no unhandled rejections.
//! - "reports a throwing commit or close listener and runs the others; the
//!   commit stands": Rust commit and close listeners return `()` and cannot
//!   throw.
//! - "keeps feeding the other observers of a view when one throws": a Rust
//!   `ViewObserver::publication` returns `()` and cannot throw.
//! - "contains a fulfilled thenable that calls only its fulfillment handler"
//!   and "contains a rejected promise from another realm": JS-only
//!   (`contained` over thenables and `node:vm` realms).
//! - "faults only the task, and ends only the watch, for a thrown value that
//!   cannot be formatted": JS-only (a thrown non-`Error` value); Rust errors
//!   always format.
//! - "reports a throwing clock once, also when the report handler reads the
//!   clock again" and "keeps working when onReport throws, and falls back to
//!   Date.now when the clock throws": Rust host callbacks (`now`,
//!   `on_report`) cannot throw.

use std::collections::HashSet;
use std::future::Future;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::{with_abort_signal, AbortController, Context};
use eukhe_chord::json::JsonValue;
use futures::future::BoxFuture;
use futures::FutureExt;

use super::support::{context, create_models, create_registry};
use super::task_support::{
    aborted, deferred, eventually, flush, open_tasks, settled, Deferred, OpenTasksOptions, Reports,
};
use crate::documents::resolve_token_address;
use crate::errors::StorageError;
use crate::harness::define::define_extension;
use crate::harness::events::watch_events;
use crate::harness::live::LIVE_DOC;
use crate::harness::types::{
    ContextOptions, ConversationCreateOptions, Extension, HarnessOptions, InputSubmissionDraft,
};
use crate::harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
use crate::session::erase;
use crate::session::tests::support::{json, object, ControlledStorage};
use crate::session::{SessionEnd, SessionError, SessionResult, WatchEnd};
use crate::tasks::{define_task, NextTaskState, Task, TaskDefinition};
use crate::types::{
    AnyTaskRecord, ConversationId, ConversationOwnership, ConversationQuery, ConversationRecord,
    Cursor, DocumentAddress, DocumentId, DocumentObserverExt, DocumentPoint, DocumentQuery,
    DocumentRecord, EntryDraft, EntryId, EntryQuery, EntryRecord, Page, ScanOrder, Seq, Storage,
    StorageWrite, StoredDocument, StoredEntry, SubmissionId, SubmissionQuery, SubmissionRecord,
    TaskId, TaskOptions, TaskOutcome, TaskOwnership, TaskQuery, TaskStatus,
};

type StepTask = Task<JsonValue, JsonValue, JsonValue, ()>;

/// Await `future` within the 30 s deadline [`eventually`] uses, so a call
/// that never settles fails the test instead of hanging the suite.
async fn within<T>(future: impl Future<Output = T>) -> T {
    tokio::time::timeout(std::time::Duration::from_secs(30), future)
        .await
        .expect("settled before the deadline")
}

/// A test failure with a fixed message.
#[derive(Debug, thiserror::Error)]
#[error("{0}")]
struct TestFailure(&'static str);

fn failure(message: &'static str) -> StorageError {
    StorageError::failed(TestFailure(message))
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// TS `rejects.toBe(error)` for a storage error: the call gets it itself.
#[track_caller]
fn assert_storage<T: std::fmt::Debug>(result: SessionResult<T>, message: &str) {
    match result {
        Err(SessionError::Storage(error)) => assert_eq!(error.to_string(), message),
        other => panic!("expected the storage error {message:?}, got {other:?}"),
    }
}

/// TS `rejects.toMatchObject({ name: "SessionFailed", cause })`.
#[track_caller]
fn assert_failed<T: std::fmt::Debug>(result: SessionResult<T>, message: &str) {
    match result {
        Err(SessionError::Failed(failed)) => assert_eq!(failed.cause().to_string(), message),
        other => panic!("expected SessionFailed by {message:?}, got {other:?}"),
    }
}

/// TS `expect(await harness.closed).toEqual({ reason: "failed", error })`.
#[track_caller]
fn assert_ended_failed(end: &SessionEnd, message: &str) {
    assert!(
        matches!(end, SessionEnd::Failed { error } if error.to_string() == message),
        "{end:?}"
    );
}

/// The messages of the reports so far.
fn reported(reports: &Reports) -> Vec<String> {
    reports.all().iter().map(ToString::to_string).collect()
}

fn conversation_task() -> TaskOptions {
    TaskOptions {
        ownership: TaskOwnership::Conversation,
        conversation_id: None,
        background: None,
        abandon_on_restart: None,
    }
}

fn aborted_state() -> NextTaskState<JsonValue, JsonValue> {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Aborted {
            reason: None,
            result: None,
        },
    }
}

/// `tx.appendEntry(root.id, { kind: "note" })` in its own commit.
fn note(root: &Conversation) -> BoxFuture<'static, SessionResult<EntryId>> {
    let id = root.id();
    root.commit(
        move |tx| async move { Ok(tx.append_entry(id, EntryDraft::new("note")).await?.id) },
        context(),
    )
}

async fn start(root: &Conversation, task: &StepTask) -> TaskId {
    let definition = task.as_definition_ref();
    root.commit(
        move |tx| async move {
            tx.create_task(definition, JsonValue::Null, conversation_task())
                .await
        },
        context(),
    )
    .await
    .unwrap()
}

type Signals = Arc<Mutex<Vec<&'static str>>>;

/// The wait a reentrant report started.
type Reentered = Arc<Mutex<Option<BoxFuture<'static, SessionResult<()>>>>>;

/// Waits for its signal, records that it saw it, and ends `aborted` through
/// its abort handler.
fn waiting_task(signals: &Signals) -> StepTask {
    let signals = Arc::clone(signals);
    define_task(
        TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
            "test.waiting",
            1,
            |_: &JsonValue| Ok(json(r#"{"phase":"work"}"#)),
            |_task, runtime, cx| async move {
                runtime
                    .commit(|_tx, _current| async { Ok(Some(aborted_state())) }, &cx)
                    .await
            },
        )
        .phase("work", move |_task, runtime, _cx| {
            let signals = Arc::clone(&signals);
            async move {
                aborted(&runtime.signal()).await;
                lock(&signals).push("aborted");
                Ok(())
            }
        }),
    )
}

/// Hook before a scan of entries: `(limit, cursor, context)`.
type ScanHook = Arc<
    dyn Fn(usize, Option<&Cursor>, &Context) -> BoxFuture<'static, Result<(), StorageError>>
        + Send
        + Sync,
>;
/// Hook before (or, for close, after) a Storage call.
type CallHook = Arc<dyn Fn() -> Result<(), StorageError> + Send + Sync>;

/// [`ControlledStorage`] with hooks on the calls these tests intercept (TS
/// subclasses overriding single methods).
#[derive(Default)]
struct Hooks {
    task: Option<CallHook>,
    scan_entries: Option<ScanHook>,
    mint_id: Option<CallHook>,
    close: Option<CallHook>,
}

struct Hooked {
    inner: Arc<ControlledStorage>,
    hooks: Hooks,
}

impl Hooked {
    fn new(inner: &Arc<ControlledStorage>, hooks: Hooks) -> Arc<Self> {
        Arc::new(Self {
            inner: Arc::clone(inner),
            hooks,
        })
    }
}

impl Storage for Hooked {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        self.inner.commit(writes, cx)
    }

    fn mint_id(&self) -> BoxFuture<'_, Result<u64, StorageError>> {
        if let Some(hook) = &self.hooks.mint_id {
            if let Err(error) = hook() {
                return futures::future::ready(Err(error)).boxed();
            }
        }
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
        let before = self
            .hooks
            .scan_entries
            .as_ref()
            .map(|hook| hook(limit, cursor, cx));
        async move {
            if let Some(before) = before {
                before.await?;
            }
            self.inner.scan_entries(query, limit, cursor, cx).await
        }
        .boxed()
    }

    fn task<'a>(
        &'a self,
        id: TaskId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<AnyTaskRecord>, StorageError>> {
        if let Some(hook) = &self.hooks.task {
            if let Err(error) = hook() {
                return futures::future::ready(Err(error)).boxed();
            }
        }
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
        self.inner.find_document(address, at, cx)
    }

    fn document<'a>(
        &'a self,
        id: DocumentId,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredDocument>, StorageError>> {
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
        async move {
            self.inner.close(cx).await?;
            match &self.hooks.close {
                Some(hook) => hook(),
                None => Ok(()),
            }
        }
        .boxed()
    }
}

/// A held range scan: `entered` resolves when it arrives, `release` lets it go on.
#[derive(Clone)]
struct HeldRange {
    entered: Deferred,
    release: Deferred,
}

/// Fails each Storage method named in `failing` once with `disk gone`. A
/// scan of entries with a limit above 1 is the context read's scan of its
/// range, off the Session line; `held_range` holds it until released.
#[derive(Clone, Default)]
struct FailingCalls {
    failing: Arc<Mutex<HashSet<&'static str>>>,
    held_range: Arc<Mutex<Option<HeldRange>>>,
}

impl FailingCalls {
    fn fail(&self, method: &'static str) {
        lock(&self.failing).insert(method);
    }

    fn check(failing: &Mutex<HashSet<&'static str>>, method: &str) -> Result<(), StorageError> {
        if lock(failing).remove(method) {
            return Err(failure("disk gone"));
        }
        Ok(())
    }

    fn storage(&self, inner: &Arc<ControlledStorage>) -> Arc<Hooked> {
        let (task, mint) = (Arc::clone(&self.failing), Arc::clone(&self.failing));
        let (scan, held) = (Arc::clone(&self.failing), Arc::clone(&self.held_range));
        Hooked::new(
            inner,
            Hooks {
                task: Some(Arc::new(move || Self::check(&task, "task"))),
                mint_id: Some(Arc::new(move || Self::check(&mint, "mintId"))),
                scan_entries: Some(Arc::new(move |limit, _cursor, _cx| {
                    if limit <= 1 {
                        return futures::future::ready(Ok(())).boxed();
                    }
                    let held = lock(&held).clone();
                    let failing = Arc::clone(&scan);
                    async move {
                        if let Some(held) = held {
                            held.entered.resolve(());
                            held.release.wait().await;
                        }
                        Self::check(&failing, "scanRange")
                    }
                    .boxed()
                })),
                close: None,
            },
        )
    }
}

struct Started {
    harness: Harness,
    root: Conversation,
    reports: Reports,
    signals: Signals,
    waiting: StepTask,
}

async fn started(storage: Arc<dyn Storage>) -> Started {
    let signals = Signals::default();
    let waiting = waiting_task(&signals);
    let opened = open_tasks(storage, &[waiting.erase()], OpenTasksOptions::default()).await;
    let root = opened
        .harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    Started {
        harness: opened.harness,
        root,
        reports: opened.reports,
        signals,
        waiting,
    }
}

async fn running(harness: &Harness, id: TaskId) {
    eventually(|| async move {
        harness
            .get_task(id, context())
            .await
            .unwrap()
            .is_some_and(|task| task.state.status() == TaskStatus::Running)
    })
    .await;
}

#[tokio::test]
async fn ends_everything_with_the_first_error_the_call_later_calls_waits_watches_streams_running_tasks(
) {
    let storage = ControlledStorage::new();
    let Started {
        harness,
        root,
        reports,
        signals,
        waiting,
    } = started(storage.clone()).await;
    let id = start(&root, &waiting).await;
    harness.resume().unwrap();
    running(&harness, id).await;
    let task = tokio::spawn(harness.wait_for_task(id, context()));
    let idle = tokio::spawn(harness.wait_for_idle(context()));
    let watch = harness
        .watch_doc(&LIVE_DOC, root.id(), context())
        .await
        .unwrap()
        .unwrap();
    let stream = watch_events(&harness, root.id(), context()).await.unwrap();
    stream
        .start(Arc::new(|_, _| async { Ok(()) }.boxed()))
        .unwrap();
    flush().await;

    storage.fail_next_commit(failure("disk gone"));
    // The call that hit it gets the storage error itself.
    assert_storage(note(&root).await, "disk gone");

    assert_failed(task.await.unwrap(), "disk gone");
    assert_failed(idle.await.unwrap(), "disk gone");
    let disk_gone = Arc::new(SessionError::Storage(failure("disk gone")));
    assert_eq!(
        watch.closed().await,
        WatchEnd::SessionFailed(Arc::clone(&disk_gone))
    );
    assert_eq!(stream.closed().await, WatchEnd::SessionFailed(disk_gone));
    // Every later call, and a wait that starts now.
    assert_failed(harness.get_task(id, context()).await, "disk gone");
    assert_failed(harness.wait_for_idle(context()).await, "disk gone");
    assert_failed(
        root.submit(InputSubmissionDraft::new("x"), context()).await,
        "disk gone",
    );
    assert_ended_failed(&harness.closed().await, "disk gone");
    assert_eq!(*lock(&signals), ["aborted"]);
    assert_eq!(reported(&reports), ["disk gone"]);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_it_from_a_read_off_the_session_line_as_a_context_read_makes() {
    let calls = FailingCalls::default();
    let Started {
        harness,
        root,
        reports,
        ..
    } = started(calls.storage(&ControlledStorage::new())).await;
    note(&root).await.unwrap();
    calls.fail("scanRange");
    assert_storage(
        root.context(context(), ContextOptions::default()).await,
        "disk gone",
    );
    assert_ended_failed(&harness.closed().await, "disk gone");
    assert_eq!(reported(&reports), ["disk gone"]);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn ends_storage_calls_underway_with_session_failed_and_closes_once_they_have_settled() {
    let calls = FailingCalls::default();
    let Started { harness, root, .. } = started(calls.storage(&ControlledStorage::new())).await;
    let release = deferred::<()>();
    note(&root).await.unwrap();
    let held = HeldRange {
        entered: deferred(),
        release: release.clone(),
    };
    *lock(&calls.held_range) = Some(held.clone());
    let reading = tokio::spawn(root.context(context(), ContextOptions::default()));
    held.entered.wait().await;
    // Another call fails the Session while the context read is underway.
    calls.fail("mintId");
    assert_storage(note(&root).await, "disk gone");
    let closed = tokio::spawn(harness.closed());
    assert!(!settled(&closed).await);
    // The read succeeds at the backend, yet its caller gets the failure: nothing it read is used.
    release.resolve(());
    assert_failed(reading.await.unwrap(), "disk gone");
    assert_ended_failed(&closed.await.unwrap(), "disk gone");
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn closes_the_backend_only_after_a_paged_read_underway_which_cannot_start_another_page() {
    let pages: Signals = Arc::default();
    let first_page = deferred::<()>();
    let release_first = deferred::<()>();
    let scanned = Arc::clone(&pages);
    let (entered, release) = (first_page.clone(), release_first.clone());
    let closed = Arc::clone(&pages);
    let storage = Hooked::new(
        &ControlledStorage::new(),
        Hooks {
            scan_entries: Some(Arc::new(move |limit, cursor, _cx| {
                if limit <= 1 {
                    return futures::future::ready(Ok(())).boxed();
                }
                lock(&scanned).push(if cursor.is_none() { "first" } else { "next" });
                if cursor.is_some() {
                    return futures::future::ready(Ok(())).boxed();
                }
                entered.resolve(());
                let release = release.wait();
                async move {
                    release.await;
                    Ok(())
                }
                .boxed()
            })),
            // TS pushes before `super.close()`; the order against the backend's close is unobservable here.
            close: Some(Arc::new(move || {
                lock(&closed).push("close");
                Ok(())
            })),
            ..Hooks::default()
        },
    );
    let Started { harness, root, .. } = started(storage).await;
    // More entries than one page of the context read.
    let id = root.id();
    root.commit(
        move |tx| async move {
            for _ in 0..300 {
                tx.append_entry(id, EntryDraft::new("note")).await?;
            }
            Ok(())
        },
        context(),
    )
    .await
    .unwrap();
    let reading = tokio::spawn(root.context(context(), ContextOptions::default()));
    first_page.wait().await;
    let closing = tokio::spawn(harness.close(context()));
    release_first.resolve(());
    let error = reading.await.unwrap().unwrap_err();
    assert!(error.to_string().contains("is closed"), "{error}");
    closing.await.unwrap().unwrap();
    assert_eq!(*lock(&pages), ["first", "close"]);
    assert!(matches!(harness.closed().await, SessionEnd::Closed));
}

#[tokio::test]
async fn fails_it_when_storage_cannot_close_an_earlier_failure_stays_the_cause() {
    let failing_close = |inner: &Arc<ControlledStorage>| {
        Hooked::new(
            inner,
            Hooks {
                close: Some(Arc::new(|| Err(failure("close failed")))),
                ..Hooks::default()
            },
        )
    };
    let healthy = started(failing_close(&ControlledStorage::new())).await;
    assert_storage(healthy.harness.close(context()).await, "close failed");
    assert_ended_failed(&healthy.harness.closed().await, "close failed");
    assert_eq!(reported(&healthy.reports), ["close failed"]);

    let storage = ControlledStorage::new();
    let failed = started(failing_close(&storage)).await;
    storage.fail_next_commit(failure("disk gone"));
    assert_storage(note(&failed.root).await, "disk gone");
    assert_ended_failed(&failed.harness.closed().await, "disk gone");
    assert_eq!(reported(&failed.reports), ["disk gone"]);
}

#[tokio::test]
async fn rejects_the_harnesss_own_calls_with_session_failed_after_a_failure() {
    let storage = ControlledStorage::new();
    let Started { harness, root, .. } = started(storage.clone()).await;
    storage.fail_next_commit(failure("disk gone"));
    assert_storage(note(&root).await, "disk gone");
    assert_failed(harness.resume(), "disk gone");
    assert_failed(
        harness.root(RootOptions::default(), context()).await,
        "disk gone",
    );
    assert_failed(
        harness.conversation(root.id(), context()).await,
        "disk gone",
    );
    assert_failed(
        harness
            .create_conversation(
                ConversationCreateOptions::new(ConversationOwnership::Ownerless),
                context(),
            )
            .await,
        "disk gone",
    );
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn ends_what_a_task_holds_with_session_failed_not_as_cancelled_by_its_signal() {
    type Ends = Arc<Mutex<Option<(WatchEnd, SessionResult<()>)>>>;
    let ends: Ends = Arc::default();
    let watching = deferred::<()>();
    let (sink, reached) = (Arc::clone(&ends), watching.clone());
    let watcher: StepTask = define_task(
        TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
            "test.watcher",
            1,
            |_: &JsonValue| Ok(json(r#"{"phase":"work"}"#)),
            |_task, _runtime, _cx| async { Ok(()) },
        )
        .phase("work", move |_task, runtime, cx| {
            let (sink, reached) = (Arc::clone(&sink), reached.clone());
            async move {
                let id = runtime.conversation_id();
                let doc = runtime
                    .watch_doc(&LIVE_DOC, id, &cx)
                    .await?
                    .expect("pi.live exists");
                let handle = runtime
                    .conversation(id, &cx)
                    .await?
                    .expect("the conversation exists");
                let idle = tokio::spawn(handle.wait_for_idle(&cx));
                reached.resolve(());
                let end = doc.closed().await;
                let idle = idle.await.expect("the wait settles");
                *lock(&sink) = Some((end, idle));
                Ok(())
            }
        }),
    );
    let storage = ControlledStorage::new();
    let opened = open_tasks(
        storage.clone(),
        &[watcher.erase()],
        OpenTasksOptions::default(),
    )
    .await;
    let root = opened
        .harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    start(&root, &watcher).await;
    opened.harness.resume().unwrap();
    watching.wait().await;
    storage.fail_next_commit(failure("disk gone"));
    assert_storage(note(&root).await, "disk gone");
    opened.harness.closed().await;
    let (end, idle) = lock(&ends).take().expect("the task recorded its ends");
    assert_eq!(
        end,
        WatchEnd::SessionFailed(Arc::new(SessionError::Storage(failure("disk gone"))))
    );
    assert!(matches!(idle, Err(SessionError::Failed(_))), "{idle:?}");
    opened.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_it_from_a_failed_id_mint() {
    let calls = FailingCalls::default();
    let Started { harness, root, .. } = started(calls.storage(&ControlledStorage::new())).await;
    calls.fail("mintId");
    assert_storage(note(&root).await, "disk gone");
    assert_ended_failed(&harness.closed().await, "disk gone");
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn does_not_commit_what_a_callback_did_after_it_caught_a_failed_read() {
    let calls = FailingCalls::default();
    let storage = ControlledStorage::new();
    let Started { harness, root, .. } = started(calls.storage(&storage)).await;
    let written = storage.admitted_commits().len();
    calls.fail("task");
    let id = root.id();
    assert_failed(
        root.commit(
            move |tx| async move {
                let _ = tx.task(TaskId::from_number(1)).await;
                tx.append_entry(id, EntryDraft::new("note")).await?;
                Ok(())
            },
            context(),
        )
        .await,
        "disk gone",
    );
    assert_eq!(storage.admitted_commits().len(), written);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_it_for_a_storage_request_error_from_a_commit_whose_effect_is_unknown() {
    let storage = ControlledStorage::new();
    let Started { harness, root, .. } = started(storage.clone()).await;
    storage.fail_next_commit(StorageError::request("bad batch"));
    match note(&root).await {
        Err(SessionError::Storage(StorageError::Request(error))) => {
            assert_eq!(error.to_string(), "bad batch");
        }
        other => panic!("expected the StorageRequestError, got {other:?}"),
    }
    assert_ended_failed(&harness.closed().await, "bad batch");
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_only_the_call_for_an_invalid_request() {
    // TS opens over a plain `MemoryStorage`; `ControlledStorage` with no
    // injected failure is one.
    let Started {
        harness,
        root,
        reports,
        ..
    } = started(ControlledStorage::new()).await;
    let entry = note(&root).await.unwrap();
    let invalid = Cursor::from(object(r#"{"after":"x"}"#));
    let results: Vec<SessionResult<()>> = vec![
        root.entries(
            ConversationEntryQuery::default(),
            10,
            Some(invalid),
            context(),
        )
        .await
        .map(drop),
        async {
            let page = root
                .entries(
                    ConversationEntryQuery {
                        order: Some(ScanOrder::Ascending),
                        ..ConversationEntryQuery::default()
                    },
                    1,
                    None,
                    context(),
                )
                .await?;
            let cursor = page
                .next
                .unwrap_or_else(|| Cursor::from(object(r#"{"after":1,"order":"ascending"}"#)));
            root.entries(
                ConversationEntryQuery {
                    order: Some(ScanOrder::Descending),
                    ..ConversationEntryQuery::default()
                },
                1,
                Some(cursor),
                context(),
            )
            .await
            .map(drop)
        }
        .await,
        root.commit(
            |tx| async move {
                tx.scan_entries(
                    EntryQuery::new(ConversationId::from_number(999_999)),
                    10,
                    None,
                )
                .await
                .map(drop)
            },
            context(),
        )
        .await,
        // `pi.live` keeps no history. TS casts `LiveDoc` past the
        // rewindable type check; Rust calls the erased read under it.
        harness
            .snapshot_as_of_at(
                &erase(&LIVE_DOC),
                resolve_token_address(&LIVE_DOC, root.id()),
                entry,
                context(),
            )
            .await
            .map(drop),
    ];
    for result in results {
        assert!(
            matches!(result, Err(SessionError::Storage(StorageError::Request(_)))),
            "{result:?}"
        );
    }
    note(&root).await.unwrap();
    let ended = tokio::spawn(harness.closed());
    assert!(!settled(&ended).await);
    assert!(reports.all().is_empty());
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_it_for_a_throw_in_its_own_commit_listeners_which_would_leave_memory_behind_storage()
{
    let Started {
        harness,
        root,
        reports,
        ..
    } = started(ControlledStorage::new()).await;
    // Rust: the listener returns its failure instead of throwing it.
    let subscription = harness
        .observe_commits(Arc::new(|_, _| Err(SessionError::error("listener bug"))))
        .unwrap();
    // The commit itself is durable and resolves; the Session fails behind it.
    note(&root).await.unwrap();
    assert_ended_failed(&harness.closed().await, "listener bug");
    assert_eq!(reported(&reports), ["listener bug"]);
    drop(subscription);
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn fails_it_for_a_storage_error_during_a_host_close_before_the_backend_closes() {
    let storage = ControlledStorage::new();
    let Started {
        harness,
        root,
        reports,
        ..
    } = started(storage.clone()).await;
    let held = storage.hold_commits();
    storage.fail_next_commit(failure("disk gone"));
    let committing = tokio::spawn(note(&root));
    held.entered().await;
    let closing = tokio::spawn(harness.close(context()));
    held.release();
    assert_storage(committing.await.unwrap(), "disk gone");
    let _ = closing.await.unwrap();
    assert_ended_failed(&harness.closed().await, "disk gone");
    assert_eq!(reported(&reports), ["disk gone"]);
}

#[tokio::test]
async fn ends_an_abort_that_joins_a_run_ignoring_its_signal_and_a_reentrant_report_finds_the_session_failed(
) {
    let release = deferred::<()>();
    let entered = deferred::<()>();
    let (gate, reached) = (release.clone(), entered.clone());
    let stubborn: StepTask = define_task(
        TaskDefinition::<JsonValue, JsonValue, JsonValue, ()>::new(
            "test.stubborn",
            1,
            |_: &JsonValue| Ok(json(r#"{"phase":"work"}"#)),
            |_task, _runtime, _cx| async { Ok(()) },
        )
        .phase("work", move |_task, _runtime, _cx| {
            let (gate, reached) = (gate.clone(), reached.clone());
            async move {
                reached.resolve(());
                gate.wait().await;
                Ok(())
            }
        }),
    );
    let storage = ControlledStorage::new();
    let registry = create_registry();
    registry
        .install(define_extension(Extension {
            name: "tasks".to_owned(),
            tasks: vec![stubborn.erase()],
            ..Extension::default()
        }))
        .unwrap();
    // The handler reaches the Harness through a slot filled after open (TS
    // closes over the `harness` binding).
    let slot: Arc<Mutex<Option<Harness>>> = Arc::default();
    let reentered: Reentered = Arc::default();
    let mut options = HarnessOptions::new(create_models(), Arc::new(registry));
    options.on_report = Some({
        let (slot, reentered) = (Arc::clone(&slot), Arc::clone(&reentered));
        Arc::new(move |_| {
            let mut reentered = lock(&reentered);
            if reentered.is_none() {
                if let Some(harness) = lock(&slot).as_ref() {
                    *reentered = Some(harness.wait_for_idle(context()));
                }
            }
        })
    });
    let harness = Harness::open(storage.clone(), options, context())
        .await
        .unwrap();
    *lock(&slot) = Some(harness.clone());
    let root = harness
        .root(RootOptions::default(), context())
        .await
        .unwrap();
    let id = start(&root, &stubborn).await;
    harness.resume().unwrap();
    entered.wait().await;
    let held = storage.hold_commits();
    let aborting = tokio::spawn(harness.abort_task(id, context()));
    held.entered().await;
    held.release();
    // The abort mark commits and the abort joins the run, which ignores its
    // signal; then the Session fails. TS waits 5 ms; this waits for the mark.
    let marked = &harness;
    eventually(|| async move {
        marked
            .get_task(id, context())
            .await
            .unwrap()
            .is_some_and(|task| task.abort_requested)
    })
    .await;
    flush().await;
    storage.fail_next_commit(failure("disk gone"));
    assert_storage(note(&root).await, "disk gone");
    assert_failed(within(aborting).await.unwrap(), "disk gone");
    let reentered = lock(&reentered).take().expect("a report reentered");
    assert_failed(within(reentered).await, "disk gone");
    release.resolve(());
    lock(&slot).take();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn does_not_fail_it_for_a_read_its_caller_cancelled() {
    let controller = AbortController::new();
    let signal = controller.signal();
    let aborting = controller.clone();
    // TS overrides `MemoryStorage`; `ControlledStorage` with no injected failure is one.
    let storage = Hooked::new(
        &ControlledStorage::new(),
        Hooks {
            scan_entries: Some(Arc::new(move |_limit, _cursor, cx| {
                if cx.abort_signal().is_some_and(|own| own.same(&signal)) {
                    aborting.abort(Some(Arc::new(TestFailure("caller gave up"))));
                    return futures::future::ready(Err(failure("caller gave up"))).boxed();
                }
                futures::future::ready(Ok(())).boxed()
            })),
            ..Hooks::default()
        },
    );
    let Started { harness, root, .. } = started(storage).await;
    let cancelling = with_abort_signal(&controller.signal(), context());
    let error = root
        .context(&cancelling, ContextOptions::default())
        .await
        .unwrap_err();
    assert_eq!(error.to_string(), "caller gave up");
    note(&root).await.unwrap();
    harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn reports_a_throwing_watch_listener_which_ends_that_watch() {
    let Started {
        harness,
        root,
        reports,
        ..
    } = started(ControlledStorage::new()).await;
    let watch = harness
        .watch_doc(&LIVE_DOC, root.id(), context())
        .await
        .unwrap()
        .unwrap();
    watch
        .start(Arc::new(|_, _, _| {
            async { Err(Arc::new(TestFailure("listener broke")) as _) }.boxed()
        }))
        .unwrap();
    let id = root.id();
    root.commit(
        move |tx| async move {
            tx.doc(&LIVE_DOC, id)
                .await?
                .set("compactions", json("[]"))?;
            Ok(())
        },
        context(),
    )
    .await
    .unwrap();
    assert_eq!(
        watch.closed().await,
        WatchEnd::ListenerError(Arc::new(TestFailure("listener broke")))
    );
    assert_eq!(reported(&reports), ["listener broke"]);
    harness.close(context()).await.unwrap();
}
