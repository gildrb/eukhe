//! The storage conformance suite against the SQLite and JSONL backends
//! (TS: `registerStorageConformance` in sqlite-storage and jsonl-storage
//! tests), on a fresh store and through [`ReopeningStorage`], which closes
//! and reopens the backend from its files after every commit.

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::errors::StorageError;
use eukhe_durable::storage::jsonl::{open_native_jsonl_storage, JsonlStorageOptions};
use eukhe_durable::storage::sqlite::{open_native_sqlite_storage, NativeSqliteStorageOptions};
use eukhe_durable::testing::{run_storage_conformance, StorageConformanceOptions, StorageTest};
use eukhe_durable::types::{
    AnyTaskRecord, ConversationId, ConversationQuery, ConversationRecord, Cursor, DocumentAddress,
    DocumentId, DocumentPoint, DocumentQuery, DocumentRecord, EntryId, EntryQuery, EntryRecord,
    Page, Seq, Storage, StorageWrite, StoredDocument, StoredEntry, SubmissionId, SubmissionQuery,
    SubmissionRecord, TaskId, TaskQuery,
};
use futures::future::BoxFuture;

async fn jsonl(directory: &Path, fsync: bool) -> Arc<dyn Storage> {
    let directory = directory.to_str().unwrap();
    Arc::new(
        open_native_jsonl_storage(
            directory,
            &BACKGROUND_CONTEXT,
            JsonlStorageOptions { fsync },
        )
        .await
        .unwrap(),
    )
}

async fn sqlite(path: &Path) -> Arc<dyn Storage> {
    Arc::new(
        open_native_sqlite_storage(path, NativeSqliteStorageOptions::default())
            .await
            .unwrap(),
    )
}

async fn jsonl_owned(directory: PathBuf, fsync: bool) -> Arc<dyn Storage> {
    jsonl(&directory, fsync).await
}

async fn sqlite_owned(path: PathBuf) -> Arc<dyn Storage> {
    sqlite(&path).await
}

type Opener = Arc<dyn Fn() -> BoxFuture<'static, Arc<dyn Storage>> + Send + Sync>;

/// Delegates to a backend that is closed and reopened after every commit, so
/// every read after a commit observes recovered state. Minted IDs are not
/// persisted until committed, so it keeps minting past IDs it already handed
/// out.
struct ReopeningStorage {
    open: Opener,
    current: Mutex<Arc<dyn Storage>>,
    minted: Mutex<u64>,
}

impl ReopeningStorage {
    async fn open(open: Opener) -> Arc<dyn Storage> {
        let current = open().await;
        Arc::new(Self {
            open,
            current: Mutex::new(current),
            minted: Mutex::new(0),
        })
    }

    fn current(&self) -> Arc<dyn Storage> {
        Arc::clone(&self.current.lock().unwrap_or_else(PoisonError::into_inner))
    }
}

impl Storage for ReopeningStorage {
    fn commit<'a>(
        &'a self,
        writes: &'a [StorageWrite],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Seq, StorageError>> {
        Box::pin(async move {
            let storage = self.current();
            let seq = storage.commit(writes, cx).await?;
            storage.close(cx).await?;
            *self.current.lock().unwrap_or_else(PoisonError::into_inner) = (self.open)().await;
            Ok(seq)
        })
    }

    fn mint_id(&self) -> BoxFuture<'_, Result<u64, StorageError>> {
        Box::pin(async move {
            let storage = self.current();
            loop {
                let id = storage.mint_id().await?;
                let mut minted = self.minted.lock().unwrap_or_else(PoisonError::into_inner);
                if id > *minted {
                    *minted = id;
                    return Ok(id);
                }
            }
        })
    }

    fn conversation<'a>(
        &'a self,
        id: ConversationId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<ConversationRecord>, StorageError>> {
        Box::pin(async move { self.current().conversation(id, cx).await })
    }

    fn scan_conversations<'a>(
        &'a self,
        query: &'a ConversationQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<ConversationRecord>, StorageError>> {
        Box::pin(async move {
            self.current()
                .scan_conversations(query, limit, cursor, cx)
                .await
        })
    }

    fn entry<'a>(
        &'a self,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        Box::pin(async move { self.current().entry(id, cx).await })
    }

    fn entry_in<'a>(
        &'a self,
        conversation_id: ConversationId,
        id: EntryId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredEntry>, StorageError>> {
        Box::pin(async move { self.current().entry_in(conversation_id, id, cx).await })
    }

    fn find_latest_head_marker<'a>(
        &'a self,
        conversation_id: ConversationId,
        at_or_before_entry_id: Option<EntryId>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<EntryRecord>, StorageError>> {
        Box::pin(async move {
            self.current()
                .find_latest_head_marker(conversation_id, at_or_before_entry_id, cx)
                .await
        })
    }

    fn scan_entries<'a>(
        &'a self,
        query: &'a EntryQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<EntryRecord>, StorageError>> {
        Box::pin(async move { self.current().scan_entries(query, limit, cursor, cx).await })
    }

    fn task<'a>(
        &'a self,
        id: TaskId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<AnyTaskRecord>, StorageError>> {
        Box::pin(async move { self.current().task(id, cx).await })
    }

    fn scan_tasks<'a>(
        &'a self,
        query: &'a TaskQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<AnyTaskRecord>, StorageError>> {
        Box::pin(async move { self.current().scan_tasks(query, limit, cursor, cx).await })
    }

    fn submission<'a>(
        &'a self,
        id: SubmissionId,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        Box::pin(async move { self.current().submission(id, cx).await })
    }

    fn scan_submissions<'a>(
        &'a self,
        query: &'a SubmissionQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<SubmissionRecord>, StorageError>> {
        Box::pin(async move {
            self.current()
                .scan_submissions(query, limit, cursor, cx)
                .await
        })
    }

    fn submission_by_request<'a>(
        &'a self,
        conversation_id: ConversationId,
        request_id: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<SubmissionRecord>, StorageError>> {
        Box::pin(async move {
            self.current()
                .submission_by_request(conversation_id, request_id, cx)
                .await
        })
    }

    fn find_document<'a>(
        &'a self,
        address: &'a DocumentAddress,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<DocumentRecord>, StorageError>> {
        Box::pin(async move { self.current().find_document(address, at, cx).await })
    }

    fn document<'a>(
        &'a self,
        id: DocumentId,
        at: DocumentPoint,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Option<StoredDocument>, StorageError>> {
        Box::pin(async move { self.current().document(id, at, cx).await })
    }

    fn scan_documents<'a>(
        &'a self,
        query: &'a DocumentQuery,
        limit: usize,
        cursor: Option<&'a Cursor>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Page<DocumentRecord>, StorageError>> {
        Box::pin(async move {
            self.current()
                .scan_documents(query, limit, cursor, cx)
                .await
        })
    }

    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<(), StorageError>> {
        Box::pin(async move { self.current().close(cx).await })
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn jsonl_storage_conformance() {
    run_storage_conformance(
        "JsonlStorage",
        StorageConformanceOptions {
            with_storage: Arc::new(|test: StorageTest| {
                Box::pin(async move {
                    let temp = tempfile::tempdir().unwrap();
                    let storage = jsonl(temp.path(), false).await;
                    test(Arc::clone(&storage)).await;
                    storage.close(&BACKGROUND_CONTEXT).await.unwrap();
                })
            }),
        },
    )
    .await;
}

#[tokio::test(flavor = "multi_thread")]
async fn jsonl_storage_conformance_with_fsync_after_reopen() {
    run_storage_conformance(
        "JsonlStorage (fsync, reopened)",
        StorageConformanceOptions {
            with_storage: Arc::new(|test: StorageTest| {
                Box::pin(async move {
                    let temp = tempfile::tempdir().unwrap();
                    let path = temp.path().to_owned();
                    let storage = ReopeningStorage::open(Arc::new(move || {
                        Box::pin(jsonl_owned(path.clone(), true))
                    }))
                    .await;
                    test(Arc::clone(&storage)).await;
                    storage.close(&BACKGROUND_CONTEXT).await.unwrap();
                })
            }),
        },
    )
    .await;
}

#[tokio::test(flavor = "multi_thread")]
async fn sqlite_storage_conformance() {
    run_storage_conformance(
        "SqliteStorage",
        StorageConformanceOptions {
            with_storage: Arc::new(|test: StorageTest| {
                Box::pin(async move {
                    let temp = tempfile::tempdir().unwrap();
                    let storage = sqlite(&temp.path().join("durable.sqlite")).await;
                    test(Arc::clone(&storage)).await;
                    storage.close(&BACKGROUND_CONTEXT).await.unwrap();
                })
            }),
        },
    )
    .await;
}

#[tokio::test(flavor = "multi_thread")]
async fn sqlite_storage_conformance_after_reopen() {
    run_storage_conformance(
        "SqliteStorage (reopened)",
        StorageConformanceOptions {
            with_storage: Arc::new(|test: StorageTest| {
                Box::pin(async move {
                    let temp = tempfile::tempdir().unwrap();
                    let path = temp.path().join("durable.sqlite");
                    let storage = ReopeningStorage::open(Arc::new(move || {
                        Box::pin(sqlite_owned(path.clone()))
                    }))
                    .await;
                    test(Arc::clone(&storage)).await;
                    storage.close(&BACKGROUND_CONTEXT).await.unwrap();
                })
            }),
        },
    )
    .await;
}
