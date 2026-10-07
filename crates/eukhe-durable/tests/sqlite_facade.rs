//! Port of `test/sqlite-facade.test.ts`: portable SQLite facade settlement.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_durable::errors::{StorageError, StorageRejected};
use eukhe_durable::ids::mint;
use eukhe_durable::storage::sqlite::{
    open_native_sqlite_database, NativeSqliteDatabase, NativeSqliteStorageOptions, SqliteDatabase,
    SqliteDatabaseExt, SqliteError, SqliteExecutor, SqliteRow, SqliteStorage, SqliteTransaction,
    SqliteValue, TransactionCallback, TransactionFailure,
};
use eukhe_durable::types::{
    ConversationRecord, DocumentBase, DocumentContent, DocumentCreate, DocumentId, DocumentPoint,
    DocumentRecordScope, EntryId, EntryQuery, EntryRecord, Storage, StorageWrite,
    ROOT_CONVERSATION_ID,
};
use futures::channel::oneshot;
use futures::future::BoxFuture;
use std::borrow::Cow;

/// Error type of the test transaction callbacks.
#[derive(Debug, thiserror::Error)]
enum TestError {
    #[error(transparent)]
    Sqlite(#[from] SqliteError),
    #[error("{0}")]
    Message(&'static str),
}

/// The error a controlled settlement injects.
#[derive(Debug, thiserror::Error)]
#[error("controlled settlement rejection")]
struct ControlledRejection;

#[derive(Clone, Copy, PartialEq, Eq)]
enum SettlementMode {
    Immediate,
    Delay,
    Reject,
}

struct ControlState {
    mode: SettlementMode,
    pending_settlement: Option<oneshot::Sender<()>>,
    inner_settled: Option<oneshot::Sender<()>>,
}

/// Delays the settlement of the next transaction until `settle` (TS
/// `ControlledSettlementDatabase`). The delegate transaction runs to completion first.
#[derive(Clone)]
struct ControlledSettlementDatabase {
    delegate: NativeSqliteDatabase,
    state: Arc<Mutex<ControlState>>,
}

impl ControlledSettlementDatabase {
    fn new(delegate: NativeSqliteDatabase) -> Self {
        Self {
            delegate,
            state: Arc::new(Mutex::new(ControlState {
                mode: SettlementMode::Immediate,
                pending_settlement: None,
                inner_settled: None,
            })),
        }
    }

    /// Returns a receiver that resolves once the delegate transaction settled.
    fn control_next_settlement(&self, mode: SettlementMode) -> oneshot::Receiver<()> {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        assert!(
            state.pending_settlement.is_none(),
            "A settlement is already pending"
        );
        state.mode = mode;
        let (sender, receiver) = oneshot::channel();
        state.inner_settled = Some(sender);
        receiver
    }

    fn settle(&self) {
        let settle = self
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .pending_settlement
            .take()
            .expect("No settlement is pending");
        settle.send(()).expect("settlement receiver");
    }
}

impl SqliteExecutor for ControlledSettlementDatabase {
    fn exec(&self, sql: Cow<'static, str>) -> BoxFuture<'static, Result<(), SqliteError>> {
        self.delegate.exec(sql)
    }

    fn run(
        &self,
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
    ) -> BoxFuture<'static, Result<(), SqliteError>> {
        self.delegate.run(sql, params)
    }

    fn get(
        &self,
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
    ) -> BoxFuture<'static, Result<Option<SqliteRow>, SqliteError>> {
        self.delegate.get(sql, params)
    }

    fn all(
        &self,
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
    ) -> BoxFuture<'static, Result<Vec<SqliteRow>, SqliteError>> {
        self.delegate.all(sql, params)
    }
}

impl SqliteDatabase for ControlledSettlementDatabase {
    fn transaction_dyn<'a>(
        &'a self,
        callback: TransactionCallback<'a>,
    ) -> BoxFuture<'a, Result<(), TransactionFailure>> {
        let mut state = self.state.lock().unwrap_or_else(PoisonError::into_inner);
        let mode = state.mode;
        state.mode = SettlementMode::Immediate;
        if mode == SettlementMode::Immediate {
            drop(state);
            return self.delegate.transaction_dyn(callback);
        }
        let (settle, settled) = oneshot::channel();
        state.pending_settlement = Some(settle);
        let inner_settled = state.inner_settled.take();
        drop(state);
        let settlement = self.delegate.transaction_dyn(Box::new(move |transaction| {
            Box::pin(async move {
                callback(transaction).await?;
                if mode == SettlementMode::Reject {
                    return Err(Box::new(ControlledRejection) as _);
                }
                Ok(())
            })
        }));
        Box::pin(async move {
            let result = settlement.await;
            if let Some(inner_settled) = inner_settled {
                // The test may stop waiting for the inner settlement.
                let _ignored = inner_settled.send(());
            }
            settled.await.expect("settle() was called");
            result
        })
    }

    fn close(&self) -> BoxFuture<'static, Result<(), SqliteError>> {
        self.delegate.close()
    }
}

fn row(columns: &[(&str, SqliteValue)]) -> SqliteRow {
    columns
        .iter()
        .map(|(name, value)| (*name, value.clone()))
        .collect()
}

fn value_row(value: i64) -> SqliteRow {
    row(&[("value", SqliteValue::Integer(value))])
}

fn entry(id: u64, kind: &str) -> EntryRecord {
    EntryRecord {
        model: None,
        data: None,
        edits: None,
        kind: kind.to_owned(),
        id: EntryId::from_number(id),
        conversation_id: ROOT_CONVERSATION_ID,
        head: None,
        by_task_id: None,
    }
}

fn root() -> StorageWrite {
    StorageWrite::Conversation {
        value: ConversationRecord {
            id: ROOT_CONVERSATION_ID,
            parent: None,
            owner: None,
        },
    }
}

async fn memory_database() -> NativeSqliteDatabase {
    open_native_sqlite_database(":memory:", NativeSqliteStorageOptions::default())
        .await
        .unwrap()
}

fn object(value: serde_json::Value) -> Arc<JsonObject> {
    match JsonValue::from(value) {
        JsonValue::Object(object) => object,
        other => panic!("not an object: {other}"),
    }
}

#[tokio::test]
async fn prepares_each_storage_statement_once_per_connection_and_reuses_it_across_transactions() {
    let counts: Arc<Mutex<HashMap<String, usize>>> = Arc::default();
    let observed = Arc::clone(&counts);
    let connection = rusqlite::Connection::open_in_memory().unwrap();
    let database = NativeSqliteDatabase::with_prepare_observer(connection, move |sql| {
        *observed
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .entry(sql.to_owned())
            .or_default() += 1;
    })
    .unwrap();
    let storage = SqliteStorage::open(database).await.unwrap();
    let cx = &*BACKGROUND_CONTEXT;
    storage.commit(&[root()], cx).await.unwrap();
    let entries: Vec<StorageWrite> = (0..100)
        .map(|index| StorageWrite::Entry {
            value: entry(index + 2, "cached"),
        })
        .collect();
    storage.commit(&entries, cx).await.unwrap();
    storage
        .commit(
            &[StorageWrite::Entry {
                value: entry(102, "cached-again"),
            }],
            cx,
        )
        .await
        .unwrap();
    assert_eq!(
        storage
            .entry(EntryId::from_number(2), cx)
            .await
            .unwrap()
            .unwrap()
            .entry
            .kind,
        "cached"
    );
    assert_eq!(
        storage
            .entry(EntryId::from_number(102), cx)
            .await
            .unwrap()
            .unwrap()
            .entry
            .kind,
        "cached-again"
    );
    let error = storage.commit(&[root()], cx).await.unwrap_err();
    assert!(error
        .to_string()
        .contains("ID 1 already belongs to conversation"));
    assert_eq!(
        storage
            .entry(EntryId::from_number(2), cx)
            .await
            .unwrap()
            .unwrap()
            .entry
            .kind,
        "cached"
    );
    let repeated: Vec<String> = counts
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .iter()
        .filter(|(_, count)| **count > 1)
        .map(|(sql, _)| sql.clone())
        .collect();
    assert_eq!(repeated, Vec::<String>::new());
    storage.close(cx).await.unwrap();
}

#[tokio::test]
async fn commits_work_done_through_the_transaction_handle_and_closes_idempotently() {
    let database = memory_database().await;
    database
        .transaction(|transaction: SqliteTransaction| async move {
            transaction
                .exec("CREATE TABLE async_probe (value INTEGER)".into())
                .await?;
            transaction
                .run(
                    "INSERT INTO async_probe (value) VALUES (?)".into(),
                    vec![1.into()],
                )
                .await?;
            Ok::<_, SqliteError>(())
        })
        .await
        .unwrap();
    assert_eq!(
        database
            .get("SELECT value FROM async_probe".into(), Vec::new())
            .await
            .unwrap(),
        Some(value_row(1))
    );
    database.close().await.unwrap();
    database.close().await.unwrap();
}

#[tokio::test]
async fn serializes_concurrent_transactions() {
    let database = memory_database().await;
    database
        .exec("CREATE TABLE transaction_queue (value INTEGER)".into())
        .await
        .unwrap();
    let (mark_first_started, first_started) = oneshot::channel::<()>();
    let (release_first, first_gate) = oneshot::channel::<()>();
    let first = tokio::spawn({
        let database = database.clone();
        async move {
            database
                .transaction(|transaction: SqliteTransaction| async move {
                    transaction
                        .exec("INSERT INTO transaction_queue (value) VALUES (1)".into())
                        .await?;
                    mark_first_started.send(()).unwrap();
                    first_gate.await.unwrap();
                    Ok::<_, SqliteError>(())
                })
                .await
        }
    });
    first_started.await.unwrap();

    let second_started = Arc::new(AtomicBool::new(false));
    let second = tokio::spawn({
        let database = database.clone();
        let second_started = Arc::clone(&second_started);
        async move {
            database
                .transaction(|transaction: SqliteTransaction| async move {
                    second_started.store(true, Ordering::SeqCst);
                    transaction
                        .exec("INSERT INTO transaction_queue (value) VALUES (2)".into())
                        .await?;
                    Ok::<_, SqliteError>(())
                })
                .await
        }
    });
    for _ in 0..8 {
        tokio::task::yield_now().await;
    }
    assert!(!second_started.load(Ordering::SeqCst));

    release_first.send(()).unwrap();
    first.await.unwrap().unwrap();
    second.await.unwrap().unwrap();
    assert_eq!(
        database
            .all(
                "SELECT value FROM transaction_queue ORDER BY value".into(),
                Vec::new()
            )
            .await
            .unwrap(),
        vec![value_row(1), value_row(2)]
    );
    database.close().await.unwrap();
}

#[tokio::test]
async fn runs_operations_in_call_order_whether_they_start_immediately_or_wait() {
    let database = memory_database().await;
    database
        .exec("CREATE TABLE call_order (value INTEGER)".into())
        .await
        .unwrap();
    // Operations called during a transaction must neither see its uncommitted rows nor join its rollback.
    let transaction = database.transaction(|handle: SqliteTransaction| async move {
        handle
            .run(
                "INSERT INTO call_order (value) VALUES (?)".into(),
                vec![1.into()],
            )
            .await?;
        tokio::task::yield_now().await;
        Err::<(), _>(TestError::Message("roll back"))
    });
    let before_write = database.all(
        "SELECT value FROM call_order ORDER BY value".into(),
        Vec::new(),
    );
    let write = database.run(
        "INSERT INTO call_order (value) VALUES (?)".into(),
        vec![2.into()],
    );
    let after_write = database.all(
        "SELECT value FROM call_order ORDER BY value".into(),
        Vec::new(),
    );
    assert_eq!(transaction.await.unwrap_err().to_string(), "roll back");
    write.await.unwrap();
    assert_eq!(before_write.await.unwrap(), Vec::new());
    assert_eq!(after_write.await.unwrap(), vec![value_row(2)]);

    let storage = SqliteStorage::open(database).await.unwrap();
    let cx = &*BACKGROUND_CONTEXT;
    let writes = [root()];
    let commit = storage.commit(&writes, cx);
    let read = storage.conversation(ROOT_CONVERSATION_ID, cx);
    commit.await.unwrap();
    assert_eq!(
        read.await.unwrap(),
        Some(ConversationRecord {
            id: ROOT_CONVERSATION_ID,
            parent: None,
            owner: None
        })
    );
    storage.close(cx).await.unwrap();
}

#[tokio::test]
async fn queues_ordinary_operations_behind_an_active_transaction() {
    let database = memory_database().await;
    database
        .exec("CREATE TABLE operation_queue (value INTEGER)".into())
        .await
        .unwrap();
    let (mark_transaction_started, transaction_started) = oneshot::channel::<()>();
    let (release_transaction, transaction_gate) = oneshot::channel::<()>();
    let pending = tokio::spawn({
        let database = database.clone();
        async move {
            database
                .transaction(|transaction: SqliteTransaction| async move {
                    transaction
                        .exec("INSERT INTO operation_queue (value) VALUES (1)".into())
                        .await?;
                    mark_transaction_started.send(()).unwrap();
                    transaction_gate.await.unwrap();
                    Ok::<_, SqliteError>(())
                })
                .await
        }
    });
    transaction_started.await.unwrap();

    let mut write = database.exec("INSERT INTO operation_queue (value) VALUES (2)".into());
    let mut read = database.all(
        "SELECT value FROM operation_queue ORDER BY value".into(),
        Vec::new(),
    );
    for _ in 0..8 {
        tokio::task::yield_now().await;
    }
    assert!(futures::poll!(&mut write).is_pending());
    assert!(futures::poll!(&mut read).is_pending());

    release_transaction.send(()).unwrap();
    pending.await.unwrap().unwrap();
    write.await.unwrap();
    assert_eq!(read.await.unwrap(), vec![value_row(1), value_row(2)]);
    database.close().await.unwrap();
}

/// A database call started inside a transaction callback.
type PendingRun = BoxFuture<'static, Result<(), SqliteError>>;

#[tokio::test]
async fn queues_database_calls_made_synchronously_by_a_transaction_that_started_immediately() {
    let database = memory_database().await;
    database
        .exec("CREATE TABLE barrier_probe (value INTEGER)".into())
        .await
        .unwrap();
    let outside: Arc<Mutex<Option<PendingRun>>> = Arc::default();
    let slot = Arc::clone(&outside);
    let outer = database.clone();
    let transaction = database.transaction(|handle: SqliteTransaction| async move {
        // Misuse: this call must wait for the transaction instead of joining it.
        *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(outer.run(
            "INSERT INTO barrier_probe (value) VALUES (?)".into(),
            vec![2.into()],
        ));
        handle
            .run(
                "INSERT INTO barrier_probe (value) VALUES (?)".into(),
                vec![1.into()],
            )
            .await?;
        tokio::task::yield_now().await;
        Err::<(), _>(TestError::Message("roll back"))
    });
    assert_eq!(transaction.await.unwrap_err().to_string(), "roll back");
    let outside = outside
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .unwrap();
    outside.await.unwrap();
    assert_eq!(
        database
            .all("SELECT value FROM barrier_probe".into(), Vec::new())
            .await
            .unwrap(),
        vec![value_row(2)]
    );
    database.close().await.unwrap();
}

#[tokio::test]
async fn lets_admitted_multi_query_reads_finish_before_storage_closes() {
    let storage = SqliteStorage::open(memory_database().await).await.unwrap();
    let cx = &*BACKGROUND_CONTEXT;
    let entry_id = EntryId::from_number(2);
    storage
        .commit(
            &[
                root(),
                StorageWrite::Entry {
                    value: entry(2, "probe"),
                },
            ],
            cx,
        )
        .await
        .unwrap();
    let query = EntryQuery::new(ROOT_CONVERSATION_ID);
    let scan = storage.scan_entries(&query, 10, None, cx);
    let read = storage.entry_in(ROOT_CONVERSATION_ID, entry_id, cx);
    let head = storage.find_latest_head_marker(ROOT_CONVERSATION_ID, None, cx);
    let closed = storage.close(cx);
    // A repeated close settles only when the database is closed.
    let closed_again = storage.close(cx);
    assert_eq!(
        scan.await
            .unwrap()
            .items
            .iter()
            .map(|item| item.id)
            .collect::<Vec<_>>(),
        vec![entry_id]
    );
    assert_eq!(read.await.unwrap().unwrap().entry.kind, "probe");
    assert_eq!(head.await.unwrap(), None);
    closed.await.unwrap();
    closed_again.await.unwrap();
    let error = storage
        .scan_entries(&query, 10, None, cx)
        .await
        .unwrap_err();
    assert!(error.to_string().contains("SqliteStorage is closed"));
}

#[tokio::test]
async fn rejects_a_transaction_handle_used_after_its_transaction_settles() {
    let database = memory_database().await;
    database
        .exec("CREATE TABLE stale_probe (value INTEGER)".into())
        .await
        .unwrap();
    let handle = database
        .transaction(|transaction: SqliteTransaction| async move {
            transaction
                .run(
                    "INSERT INTO stale_probe (value) VALUES (?)".into(),
                    vec![1.into()],
                )
                .await?;
            Ok::<_, SqliteError>(transaction)
        })
        .await
        .unwrap();
    let stale = "SQLite transaction handle is no longer active";
    assert_eq!(
        handle
            .exec("INSERT INTO stale_probe (value) VALUES (2)".into())
            .await
            .unwrap_err()
            .to_string(),
        stale
    );
    assert_eq!(
        handle
            .run(
                "INSERT INTO stale_probe (value) VALUES (?)".into(),
                vec![3.into()]
            )
            .await
            .unwrap_err()
            .to_string(),
        stale
    );
    assert_eq!(
        database
            .all("SELECT value FROM stale_probe".into(), Vec::new())
            .await
            .unwrap(),
        vec![value_row(1)]
    );
    database.close().await.unwrap();
}

#[tokio::test]
async fn does_not_preserve_a_guaranteed_rejection_when_rollback_itself_fails() {
    let database = memory_database().await;
    database
        .exec("CREATE TABLE rollback_probe (value INTEGER)".into())
        .await
        .unwrap();
    let error = database
        .transaction(|transaction: SqliteTransaction| async move {
            transaction
                .exec("INSERT INTO rollback_probe (value) VALUES (1)".into())
                .await?;
            transaction.exec("COMMIT".into()).await?;
            Err::<(), _>(StorageError::from(StorageRejected::new(
                "rejected after an escaped commit",
            )))
        })
        .await
        .unwrap_err();
    // TS `AggregateError`: not the callback's guaranteed rejection.
    assert!(!error.is_rejected());
    let StorageError::Failed(cause) = &error else {
        panic!("expected a failure, got {error:?}");
    };
    let Some(SqliteError::RollbackFailed {
        error,
        rollback_error,
    }) = cause.downcast_ref::<SqliteError>()
    else {
        panic!("expected a rollback failure, got {cause:?}");
    };
    assert_eq!(error.to_string(), "rejected after an escaped commit");
    assert_eq!(
        rollback_error.to_string(),
        "cannot rollback - no transaction is active"
    );
    assert_eq!(
        database
            .get("SELECT value FROM rollback_probe".into(), Vec::new())
            .await
            .unwrap(),
        Some(value_row(1))
    );
    database.close().await.unwrap();
}

#[tokio::test]
async fn awaits_async_transaction_settlement_and_adopts_ids_only_after_success() {
    let database = ControlledSettlementDatabase::new(memory_database().await);
    let inner_settled = database.control_next_settlement(SettlementMode::Delay);
    let opening = tokio::spawn(SqliteStorage::open(database.clone()));
    inner_settled.await.unwrap();
    assert!(!opening.is_finished());
    database.settle();
    let storage = Arc::new(opening.await.unwrap().unwrap());

    let inner_settled = database.control_next_settlement(SettlementMode::Delay);
    let committing = tokio::spawn({
        let storage = Arc::clone(&storage);
        async move {
            storage
                .commit(
                    &[StorageWrite::Entry {
                        value: entry(100, "settled"),
                    }],
                    &BACKGROUND_CONTEXT,
                )
                .await
        }
    });
    inner_settled.await.unwrap();
    assert!(!committing.is_finished());
    assert_eq!(mint::<EntryId, _>(&*storage).await.unwrap().get(), 2);
    database.settle();
    assert_eq!(committing.await.unwrap().unwrap().get(), 1);
    assert_eq!(mint::<EntryId, _>(&*storage).await.unwrap().get(), 101);

    let inner_settled = database.control_next_settlement(SettlementMode::Reject);
    let rejected = tokio::spawn({
        let storage = Arc::clone(&storage);
        async move {
            storage
                .commit(
                    &[StorageWrite::Entry {
                        value: entry(200, "rejected"),
                    }],
                    &BACKGROUND_CONTEXT,
                )
                .await
        }
    });
    assert_eq!(mint::<EntryId, _>(&*storage).await.unwrap().get(), 102);
    inner_settled.await.unwrap();
    database.settle();
    assert_eq!(
        rejected.await.unwrap().unwrap_err().to_string(),
        "controlled settlement rejection"
    );
    assert_eq!(mint::<EntryId, _>(&*storage).await.unwrap().get(), 103);
    assert_eq!(
        storage
            .entry(EntryId::from_number(200), &BACKGROUND_CONTEXT)
            .await
            .unwrap(),
        None
    );
    storage.close(&BACKGROUND_CONTEXT).await.unwrap();
}

#[tokio::test]
async fn reads_a_document_from_one_committed_state_while_a_commit_replaces_its_base() {
    let id = DocumentId::from_number(5);
    let cx = &*BACKGROUND_CONTEXT;
    // Each poll count starts the commit at a different point of the read's record and revision queries.
    for polls in 0..16 {
        let storage = SqliteStorage::open(memory_database().await).await.unwrap();
        storage
            .commit(
                &[StorageWrite::DocumentCreate {
                    record: DocumentCreate {
                        id,
                        kind: "replaced".to_owned(),
                        key: None,
                        scope: DocumentRecordScope::Session,
                    },
                    content: DocumentBase {
                        version: 1,
                        value: object(serde_json::json!({ "value": 1 })),
                    },
                }],
                cx,
            )
            .await
            .unwrap();
        let mut read = storage.document(id, DocumentPoint::Current, cx);
        for _ in 0..polls {
            let _ = futures::poll!(&mut read);
            tokio::task::yield_now().await;
        }
        let writes = [StorageWrite::DocumentChange {
            id,
            content: DocumentContent::Base(DocumentBase {
                version: 1,
                value: object(serde_json::json!({ "value": 2 })),
            }),
        }];
        let replace = storage.commit(&writes, cx);
        let (stored, replaced) = futures::join!(read, replace);
        replaced.unwrap();
        let value = stored.unwrap().unwrap().value;
        assert!(
            [
                object(serde_json::json!({ "value": 1 })),
                object(serde_json::json!({ "value": 2 }))
            ]
            .contains(&value),
            "{value:?}"
        );
        storage.close(cx).await.unwrap();
    }
}
