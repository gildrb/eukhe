//! [`SqliteDatabase`] adapter backed by a bundled SQLite (rusqlite). Port of
//! `storage/sqlite/node.ts`, where it is backed by Node's `node:sqlite`; `Node*` names become
//! `Native*`.
//!
//! One dedicated thread owns the connection and runs requests in call order, like the TS
//! `SerialOperationQueue`: a transaction holds the queue until it settles, so database calls
//! made meanwhile (including from inside its callback) wait for it. Values read back follow
//! `node:sqlite` defaults: integers outside the JS safe range are rejected, text is decoded
//! like a JS string.

use std::borrow::Cow;
use std::collections::HashMap;
use std::path::Path;
use std::sync::mpsc;
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

use futures::channel::oneshot;
use futures::future::{self, BoxFuture};
use rusqlite::types::{ToSqlOutput, ValueRef};
use rusqlite::{Connection, Statement, ToSql};

use super::database::{
    SqliteDatabase, SqliteError, SqliteExecutor, SqliteRow, SqliteTransaction, SqliteValue,
    TransactionCallback, TransactionFailure,
};
use super::storage::SqliteStorage;
use crate::errors::StorageError;

/// Native SQLite connection settings for a durable storage file.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct NativeSqliteStorageOptions {
    /// SQLite WAL auto-checkpoint threshold. SQLite and this adapter default to 1,000 pages;
    /// 0 disables it.
    pub wal_autocheckpoint_pages: Option<u32>,
    /// Time SQLite waits for a competing file lock. SQLite defaults to 0; this adapter
    /// defaults to 5,000 ms.
    pub busy_timeout_ms: Option<u64>,
}

const DEFAULT_WAL_AUTO_CHECKPOINT_PAGES: u32 = 1_000;
const DEFAULT_BUSY_TIMEOUT_MS: u64 = 5_000;

/// Largest integer a JS number holds exactly (`Number.MAX_SAFE_INTEGER`).
const MAX_SAFE_INTEGER: u64 = (1 << 53) - 1;

/// Errors raised by the native adapter, wrapped in [`SqliteError::Adapter`].
#[derive(Debug, thiserror::Error)]
pub enum NativeSqliteError {
    /// The database was closed (`node:sqlite` `ERR_INVALID_STATE`).
    #[error("database is not open")]
    NotOpen,
    /// An integer result outside the JS safe range (`node:sqlite` `ERR_OUT_OF_RANGE`).
    #[error("Value is too large to be represented as a JavaScript number: {0}")]
    UnsafeInteger(i64),
    /// The SQLite engine failed.
    #[error(transparent)]
    Sqlite(#[from] rusqlite::Error),
    /// Creating the database directory or the connection thread failed.
    #[error(transparent)]
    Io(#[from] std::io::Error),
}

impl From<NativeSqliteError> for SqliteError {
    fn from(error: NativeSqliteError) -> Self {
        Self::adapter(error)
    }
}

fn sqlite_error(error: rusqlite::Error) -> SqliteError {
    NativeSqliteError::Sqlite(error).into()
}

fn not_open() -> SqliteError {
    NativeSqliteError::NotOpen.into()
}

/// Called with the SQL text each time the adapter prepares a statement.
pub type PrepareObserver = Box<dyn FnMut(&str) + Send>;

type Reply<T> = oneshot::Sender<Result<T, SqliteError>>;

enum Operation {
    Exec {
        sql: Cow<'static, str>,
        reply: Reply<()>,
    },
    Run {
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
        reply: Reply<()>,
    },
    Get {
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
        reply: Reply<Option<SqliteRow>>,
    },
    All {
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
        reply: Reply<Vec<SqliteRow>>,
    },
}

enum Request {
    Operation(Operation),
    Transaction(Reply<mpsc::Sender<TransactionRequest>>),
    Close(Reply<()>),
}

enum TransactionRequest {
    Operation(Operation),
    Commit(Reply<()>),
    Rollback(Reply<()>),
}

/// Await a worker reply; a reply dropped unanswered means the worker closed first.
async fn reply<T>(result: oneshot::Receiver<Result<T, SqliteError>>) -> Result<T, SqliteError> {
    result
        .await
        .unwrap_or_else(|oneshot::Canceled| Err(not_open()))
}

fn answer<T>(reply: Reply<T>, result: Result<T, SqliteError>) {
    // The caller dropped its future; the operation still ran, like an un-awaited JS promise.
    drop(reply.send(result));
}

/// Build an operation and its result future.
fn operation<T: Send + 'static>(
    build: impl FnOnce(Reply<T>) -> Operation,
) -> (Operation, BoxFuture<'static, Result<T, SqliteError>>) {
    let (sender, receiver) = oneshot::channel();
    (build(sender), Box::pin(reply(receiver)))
}

/// Binds a facade value; `node:sqlite` binds JS values the same way.
struct Bind<'a>(&'a SqliteValue);

impl ToSql for Bind<'_> {
    fn to_sql(&self) -> rusqlite::Result<ToSqlOutput<'_>> {
        Ok(ToSqlOutput::Borrowed(match self.0 {
            SqliteValue::Null => ValueRef::Null,
            SqliteValue::Integer(value) => ValueRef::Integer(*value),
            SqliteValue::Real(value) => ValueRef::Real(*value),
            SqliteValue::Text(value) => ValueRef::Text(value.as_bytes()),
            SqliteValue::Blob(value) => ValueRef::Blob(value),
        }))
    }
}

fn read_value(value: ValueRef<'_>) -> Result<SqliteValue, SqliteError> {
    Ok(match value {
        ValueRef::Null => SqliteValue::Null,
        ValueRef::Integer(value) if value.unsigned_abs() > MAX_SAFE_INTEGER => {
            return Err(NativeSqliteError::UnsafeInteger(value).into());
        }
        ValueRef::Integer(value) => SqliteValue::Integer(value),
        ValueRef::Real(value) => SqliteValue::Real(value),
        // V8 decodes SQLite text like this, replacing invalid UTF-8.
        ValueRef::Text(text) => SqliteValue::Text(String::from_utf8_lossy(text).into_owned()),
        ValueRef::Blob(blob) => SqliteValue::Blob(blob.to_vec()),
    })
}

/// How many rows a query returns.
#[derive(Clone, Copy)]
enum Rows {
    First,
    All,
}

/// Connection-thread state. Prepared statements are cached per connection by SQL text, so
/// the database and its transaction handles share them across transactions.
struct Worker<'c> {
    connection: &'c Connection,
    statements: Vec<Statement<'c>>,
    statement_index: HashMap<String, usize>,
    observer: Option<PrepareObserver>,
}

impl<'c> Worker<'c> {
    fn perform(&mut self, operation: Operation) {
        match operation {
            Operation::Exec { sql, reply } => answer(reply, self.exec(&sql)),
            Operation::Run { sql, params, reply } => answer(reply, self.run(sql, &params)),
            Operation::Get { sql, params, reply } => answer(
                reply,
                self.query(sql, &params, Rows::First)
                    .map(|rows| rows.into_iter().next()),
            ),
            Operation::All { sql, params, reply } => {
                answer(reply, self.query(sql, &params, Rows::All));
            }
        }
    }

    fn exec(&self, sql: &str) -> Result<(), SqliteError> {
        self.connection.execute_batch(sql).map_err(sqlite_error)
    }

    fn statement(
        &mut self,
        sql: Cow<'static, str>,
        params: &[SqliteValue],
    ) -> Result<&mut Statement<'c>, SqliteError> {
        let index = if let Some(&index) = self.statement_index.get(sql.as_ref()) {
            index
        } else {
            if let Some(observer) = &mut self.observer {
                observer(&sql);
            }
            let statement = self.connection.prepare(&sql).map_err(sqlite_error)?;
            self.statements.push(statement);
            let index = self.statements.len() - 1;
            self.statement_index.insert(sql.into_owned(), index);
            index
        };
        let statement = &mut self.statements[index];
        statement.clear_bindings();
        for (index, param) in params.iter().enumerate() {
            statement
                .raw_bind_parameter(index + 1, Bind(param))
                .map_err(sqlite_error)?;
        }
        Ok(statement)
    }

    fn run(&mut self, sql: Cow<'static, str>, params: &[SqliteValue]) -> Result<(), SqliteError> {
        let statement = self.statement(sql, params)?;
        let mut rows = statement.raw_query();
        while rows.next().map_err(sqlite_error)?.is_some() {}
        Ok(())
    }

    fn query(
        &mut self,
        sql: Cow<'static, str>,
        params: &[SqliteValue],
        count: Rows,
    ) -> Result<Vec<SqliteRow>, SqliteError> {
        let statement = self.statement(sql, params)?;
        let columns: Vec<Arc<str>> = statement
            .column_names()
            .into_iter()
            .map(Arc::from)
            .collect();
        let mut rows = statement.raw_query();
        let mut values = Vec::new();
        while let Some(row) = rows.next().map_err(sqlite_error)? {
            let mut cells = Vec::with_capacity(columns.len());
            for (index, name) in columns.iter().enumerate() {
                let value = row.get_ref(index).map_err(sqlite_error)?;
                cells.push((Arc::clone(name), read_value(value)?));
            }
            values.push(SqliteRow::new(cells));
            if matches!(count, Rows::First) {
                break;
            }
        }
        Ok(values)
    }

    /// Run one transaction: `BEGIN IMMEDIATE`, then only requests from its handle until it
    /// commits or rolls back.
    fn transaction(&mut self, reply: Reply<mpsc::Sender<TransactionRequest>>) {
        if let Err(error) = self.exec("BEGIN IMMEDIATE") {
            answer(reply, Err(error));
            return;
        }
        let (sender, requests) = mpsc::channel();
        answer(reply, Ok(sender));
        loop {
            match requests.recv() {
                Ok(TransactionRequest::Operation(operation)) => self.perform(operation),
                Ok(TransactionRequest::Commit(reply)) => {
                    let committed = self.exec("COMMIT");
                    let settled = committed.is_ok();
                    answer(reply, committed);
                    // A failed COMMIT leaves the transaction open for the caller's rollback.
                    if settled {
                        return;
                    }
                }
                Ok(TransactionRequest::Rollback(reply)) => {
                    answer(reply, self.exec("ROLLBACK"));
                    return;
                }
                Err(mpsc::RecvError) => {
                    // The transaction future was dropped before it settled; nobody awaits a
                    // result. Roll back so the queue can continue. A rollback failure here
                    // surfaces as the next BEGIN failing.
                    drop(self.exec("ROLLBACK"));
                    return;
                }
            }
        }
    }
}

fn serve(
    connection: Connection,
    requests: &mpsc::Receiver<Request>,
    observer: Option<PrepareObserver>,
) {
    let close = {
        let mut worker = Worker {
            connection: &connection,
            statements: Vec::new(),
            statement_index: HashMap::new(),
            observer,
        };
        loop {
            match requests.recv() {
                Ok(Request::Operation(operation)) => worker.perform(operation),
                Ok(Request::Transaction(reply)) => worker.transaction(reply),
                Ok(Request::Close(reply)) => break Some(reply),
                // Every handle was dropped without closing: drop the connection.
                Err(mpsc::RecvError) => break None,
            }
        }
        // The worker drops here, finalizing every cached statement before the connection
        // closes (TS `statements.clear()`).
    };
    let Some(reply) = close else {
        return;
    };
    let checkpoint = connection
        .execute_batch("PRAGMA wal_checkpoint(TRUNCATE)")
        .map_err(sqlite_error);
    // `try { checkpoint } finally { close }`: a close failure replaces the checkpoint result.
    let result = match connection.close() {
        Ok(()) => checkpoint,
        Err((_, error)) => Err(sqlite_error(error)),
    };
    answer(reply, result);
    // Requests queued behind close are dropped unanswered and report "database is not open".
}

/// Executes SQL through an active transaction. Inactive once its transaction settles.
struct NativeSqliteTransaction {
    scope: Arc<Mutex<Option<mpsc::Sender<TransactionRequest>>>>,
}

impl NativeSqliteTransaction {
    fn submit<T: Send + 'static>(
        &self,
        build: impl FnOnce(Reply<T>) -> Operation,
    ) -> BoxFuture<'static, Result<T, SqliteError>> {
        let scope = self.scope.lock().unwrap_or_else(PoisonError::into_inner);
        let Some(sender) = scope.as_ref() else {
            return Box::pin(future::ready(Err(SqliteError::TransactionInactive)));
        };
        let (operation, result) = operation(build);
        // A send failure drops the reply, which reports "database is not open".
        drop(sender.send(TransactionRequest::Operation(operation)));
        result
    }
}

impl SqliteExecutor for NativeSqliteTransaction {
    fn exec(&self, sql: Cow<'static, str>) -> BoxFuture<'static, Result<(), SqliteError>> {
        self.submit(|reply| Operation::Exec { sql, reply })
    }

    fn run(
        &self,
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
    ) -> BoxFuture<'static, Result<(), SqliteError>> {
        self.submit(|reply| Operation::Run { sql, params, reply })
    }

    fn get(
        &self,
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
    ) -> BoxFuture<'static, Result<Option<SqliteRow>, SqliteError>> {
        self.submit(|reply| Operation::Get { sql, params, reply })
    }

    fn all(
        &self,
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
    ) -> BoxFuture<'static, Result<Vec<SqliteRow>, SqliteError>> {
        self.submit(|reply| Operation::All { sql, params, reply })
    }
}

/// Deactivates a transaction's handles when its driver settles or is dropped.
struct ScopeGuard(Arc<Mutex<Option<mpsc::Sender<TransactionRequest>>>>);

impl ScopeGuard {
    fn deactivate(&self) {
        self.0.lock().unwrap_or_else(PoisonError::into_inner).take();
    }
}

impl Drop for ScopeGuard {
    fn drop(&mut self) {
        self.deactivate();
    }
}

async fn settle(
    control: &mpsc::Sender<TransactionRequest>,
    request: impl FnOnce(Reply<()>) -> TransactionRequest,
) -> Result<(), SqliteError> {
    let (sender, receiver) = oneshot::channel();
    drop(control.send(request(sender)));
    reply(receiver).await
}

/// `SqliteDatabase` adapter backed by a bundled SQLite. Cloning shares the connection.
#[derive(Clone)]
pub struct NativeSqliteDatabase {
    requests: mpsc::Sender<Request>,
}

impl std::fmt::Debug for NativeSqliteDatabase {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("NativeSqliteDatabase")
            .finish_non_exhaustive()
    }
}

impl NativeSqliteDatabase {
    /// Adopt an open connection (TS `new NodeSqliteDatabase(database)`).
    ///
    /// # Errors
    /// The connection thread cannot be spawned.
    pub fn new(connection: Connection) -> Result<Self, SqliteError> {
        Self::spawn(connection, None)
    }

    /// Adopt an open connection and report every statement preparation to `observer`
    /// (the TS tests observe this by subclassing `DatabaseSync.prepare`).
    ///
    /// # Errors
    /// The connection thread cannot be spawned.
    pub fn with_prepare_observer(
        connection: Connection,
        observer: impl FnMut(&str) + Send + 'static,
    ) -> Result<Self, SqliteError> {
        Self::spawn(connection, Some(Box::new(observer)))
    }

    fn spawn(
        connection: Connection,
        observer: Option<PrepareObserver>,
    ) -> Result<Self, SqliteError> {
        let (requests, receiver) = mpsc::channel();
        std::thread::Builder::new()
            .name("eukhe-durable-sqlite".to_owned())
            .spawn(move || serve(connection, &receiver, observer))
            .map_err(NativeSqliteError::Io)?;
        Ok(Self { requests })
    }

    fn submit<T: Send + 'static>(
        &self,
        build: impl FnOnce(Reply<T>) -> Operation,
    ) -> BoxFuture<'static, Result<T, SqliteError>> {
        let (operation, result) = operation(build);
        // A send failure drops the reply, which reports "database is not open".
        drop(self.requests.send(Request::Operation(operation)));
        result
    }
}

impl SqliteExecutor for NativeSqliteDatabase {
    fn exec(&self, sql: Cow<'static, str>) -> BoxFuture<'static, Result<(), SqliteError>> {
        self.submit(|reply| Operation::Exec { sql, reply })
    }

    fn run(
        &self,
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
    ) -> BoxFuture<'static, Result<(), SqliteError>> {
        self.submit(|reply| Operation::Run { sql, params, reply })
    }

    fn get(
        &self,
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
    ) -> BoxFuture<'static, Result<Option<SqliteRow>, SqliteError>> {
        self.submit(|reply| Operation::Get { sql, params, reply })
    }

    fn all(
        &self,
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
    ) -> BoxFuture<'static, Result<Vec<SqliteRow>, SqliteError>> {
        self.submit(|reply| Operation::All { sql, params, reply })
    }
}

impl SqliteDatabase for NativeSqliteDatabase {
    fn transaction_dyn<'a>(
        &'a self,
        callback: TransactionCallback<'a>,
    ) -> BoxFuture<'a, Result<(), TransactionFailure>> {
        let (sender, begun) = oneshot::channel();
        // Queued now, in call order; a send failure reports "database is not open".
        drop(self.requests.send(Request::Transaction(sender)));
        Box::pin(async move {
            let control = reply(begun).await.map_err(TransactionFailure::Database)?;
            let scope = ScopeGuard(Arc::new(Mutex::new(Some(control.clone()))));
            let handle: SqliteTransaction = Arc::new(NativeSqliteTransaction {
                scope: Arc::clone(&scope.0),
            });
            let outcome = callback(handle).await;
            scope.deactivate();
            let error = match outcome {
                Ok(()) => match settle(&control, TransactionRequest::Commit).await {
                    Ok(()) => return Ok(()),
                    Err(error) => TransactionFailure::Database(error),
                },
                Err(error) => TransactionFailure::Callback(error),
            };
            match settle(&control, TransactionRequest::Rollback).await {
                Ok(()) => Err(error),
                Err(rollback_error) => {
                    Err(TransactionFailure::Database(SqliteError::RollbackFailed {
                        error: match error {
                            TransactionFailure::Callback(error) => Arc::from(error),
                            TransactionFailure::Database(error) => Arc::new(error),
                        },
                        rollback_error: Box::new(rollback_error),
                    }))
                }
            }
        })
    }

    fn close(&self) -> BoxFuture<'static, Result<(), SqliteError>> {
        let (sender, closed) = oneshot::channel();
        // Queued behind earlier operations. A closed database closes again as a no-op: its
        // worker is gone, so the reply drops unanswered.
        drop(self.requests.send(Request::Close(sender)));
        Box::pin(async move { closed.await.unwrap_or(Ok(())) })
    }
}

/// Open and configure a native SQLite database facade.
///
/// # Errors
/// The directory, connection, or configuration fails.
pub async fn open_native_sqlite_database(
    path: impl AsRef<Path>,
    options: NativeSqliteStorageOptions,
) -> Result<NativeSqliteDatabase, SqliteError> {
    let path = path.as_ref();
    let checkpoint_pages = options
        .wal_autocheckpoint_pages
        .unwrap_or(DEFAULT_WAL_AUTO_CHECKPOINT_PAGES);
    let timeout = options.busy_timeout_ms.unwrap_or(DEFAULT_BUSY_TIMEOUT_MS);
    if path != Path::new(":memory:") {
        if let Some(directory) = path.parent() {
            tokio::fs::create_dir_all(directory)
                .await
                .map_err(NativeSqliteError::Io)?;
        }
    }
    let connection = Connection::open(path).map_err(sqlite_error)?;
    connection
        .busy_timeout(Duration::from_millis(timeout))
        .map_err(sqlite_error)?;
    let adapter = NativeSqliteDatabase::new(connection)?;
    let configured = async {
        adapter.exec("PRAGMA journal_mode = WAL".into()).await?;
        adapter.exec("PRAGMA synchronous = NORMAL".into()).await?;
        adapter
            .exec(format!("PRAGMA wal_autocheckpoint = {checkpoint_pages}").into())
            .await
    }
    .await;
    match configured {
        Ok(()) => Ok(adapter),
        Err(error) => {
            // Preserve the configuration failure.
            drop(adapter.close().await);
            Err(error)
        }
    }
}

/// Open or create file-backed durable storage using a bundled SQLite.
///
/// # Errors
/// Opening the database or initializing the storage fails.
pub async fn open_native_sqlite_storage(
    path: impl AsRef<Path>,
    options: NativeSqliteStorageOptions,
) -> Result<SqliteStorage, StorageError> {
    let database = open_native_sqlite_database(path, options)
        .await
        .map_err(StorageError::failed)?;
    SqliteStorage::open(database).await
}
