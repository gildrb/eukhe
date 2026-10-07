//! Minimal asynchronous SQLite facade required by [`SqliteStorage`](super::SqliteStorage).
//!
//! Port of `storage/sqlite/database.ts`. The TS facade is structurally typed; here it is a
//! pair of object-safe traits ([`SqliteExecutor`], [`SqliteDatabase`]) plus the typed
//! transaction helper [`SqliteDatabaseExt::transaction`].

use std::borrow::Cow;
use std::error::Error;
use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};

use futures::future::BoxFuture;

/// Largest integer a JS number holds exactly (`Number.MAX_SAFE_INTEGER`).
const MAX_SAFE_INTEGER: u64 = (1 << 53) - 1;

/// Values supported by the portable SQLite storage core.
///
/// TS `null | number | bigint | string | Uint8Array`: a JS `number` is [`Integer`] or [`Real`]
/// by its SQLite storage class, `bigint` is [`Integer`], `Uint8Array` is [`Blob`].
///
/// Equality follows JS: [`Integer`] and [`Real`] are both numbers and compare numerically.
///
/// [`Integer`]: SqliteValue::Integer
/// [`Real`]: SqliteValue::Real
/// [`Blob`]: SqliteValue::Blob
#[derive(Debug, Clone)]
pub enum SqliteValue {
    Null,
    Integer(i64),
    Real(f64),
    Text(String),
    Blob(Vec<u8>),
}

impl SqliteValue {
    /// The value as a JS number, when it is one.
    #[must_use]
    pub fn as_number(&self) -> Option<f64> {
        match self {
            // JS numbers are doubles: an integer column value reads back as one.
            #[expect(clippy::cast_precision_loss, reason = "JS number semantics")]
            Self::Integer(value) => Some(*value as f64),
            Self::Real(value) => Some(*value),
            Self::Null | Self::Text(_) | Self::Blob(_) => None,
        }
    }
}

impl PartialEq for SqliteValue {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Null, Self::Null) => true,
            (Self::Integer(left), Self::Integer(right)) => left == right,
            (Self::Text(left), Self::Text(right)) => left == right,
            (Self::Blob(left), Self::Blob(right)) => left == right,
            (Self::Integer(_) | Self::Real(_), Self::Integer(_) | Self::Real(_)) => {
                self.as_number() == other.as_number()
            }
            (Self::Null | Self::Integer(_) | Self::Real(_) | Self::Text(_) | Self::Blob(_), _) => {
                false
            }
        }
    }
}

impl From<i64> for SqliteValue {
    fn from(value: i64) -> Self {
        Self::Integer(value)
    }
}

impl From<i32> for SqliteValue {
    fn from(value: i32) -> Self {
        Self::Integer(value.into())
    }
}

impl From<u32> for SqliteValue {
    fn from(value: u32) -> Self {
        Self::Integer(value.into())
    }
}

impl From<u64> for SqliteValue {
    /// A JS number: exact as an integer up to `Number.MAX_SAFE_INTEGER`, a double beyond
    /// (what binding the equivalent JS number would store).
    fn from(value: u64) -> Self {
        if value <= MAX_SAFE_INTEGER {
            // In range by the check above.
            Self::Integer(value.cast_signed())
        } else {
            #[expect(
                clippy::cast_precision_loss,
                reason = "JS number semantics beyond 2^53"
            )]
            Self::Real(value as f64)
        }
    }
}

impl From<f64> for SqliteValue {
    fn from(value: f64) -> Self {
        Self::Real(value)
    }
}

impl From<&str> for SqliteValue {
    fn from(value: &str) -> Self {
        Self::Text(value.to_owned())
    }
}

impl From<String> for SqliteValue {
    fn from(value: String) -> Self {
        Self::Text(value)
    }
}

impl From<Vec<u8>> for SqliteValue {
    fn from(value: Vec<u8>) -> Self {
        Self::Blob(value)
    }
}

impl<T: Into<SqliteValue>> From<Option<T>> for SqliteValue {
    fn from(value: Option<T>) -> Self {
        value.map_or(Self::Null, Into::into)
    }
}

/// One result row: column names to values, like the plain object `node:sqlite` returns.
///
/// Like a JS object built from a row, a repeated column name resolves to its last value.
/// Equality ignores column order (`toEqual`).
#[derive(Debug, Clone, Default)]
pub struct SqliteRow {
    columns: Vec<(Arc<str>, SqliteValue)>,
}

impl SqliteRow {
    /// Build a row from `(column, value)` pairs in result order.
    #[must_use]
    pub fn new(columns: Vec<(Arc<str>, SqliteValue)>) -> Self {
        Self { columns }
    }

    /// Columns in result order.
    pub fn columns(&self) -> impl Iterator<Item = (&str, &SqliteValue)> {
        self.columns
            .iter()
            .map(|(name, value)| (name.as_ref(), value))
    }

    /// The value of `column`, or `None` when the row has no such column.
    #[must_use]
    pub fn value(&self, column: &str) -> Option<&SqliteValue> {
        self.columns
            .iter()
            .rev()
            .find(|(name, _)| name.as_ref() == column)
            .map(|(_, value)| value)
    }

    /// The text value of `column`.
    ///
    /// # Errors
    /// [`SqliteError::MissingColumn`] or [`SqliteError::ColumnType`].
    pub fn text(&self, column: &str) -> Result<&str, SqliteError> {
        match self.required(column)? {
            SqliteValue::Text(text) => Ok(text),
            SqliteValue::Null
            | SqliteValue::Integer(_)
            | SqliteValue::Real(_)
            | SqliteValue::Blob(_) => Err(SqliteError::column_type(column, "text")),
        }
    }

    /// The integer value of `column`. A real that is an exact JS safe integer also qualifies,
    /// since JS cannot tell the two apart.
    ///
    /// # Errors
    /// [`SqliteError::MissingColumn`] or [`SqliteError::ColumnType`].
    pub fn integer(&self, column: &str) -> Result<i64, SqliteError> {
        match self.required(column)? {
            SqliteValue::Integer(value) => Ok(*value),
            #[expect(clippy::cast_possible_truncation, reason = "checked safe integer")]
            SqliteValue::Real(value) if is_safe_integer(*value) => Ok(*value as i64),
            SqliteValue::Real(_)
            | SqliteValue::Null
            | SqliteValue::Text(_)
            | SqliteValue::Blob(_) => Err(SqliteError::column_type(column, "an integer")),
        }
    }

    /// The numeric value of `column` as a JS number.
    ///
    /// # Errors
    /// [`SqliteError::MissingColumn`] or [`SqliteError::ColumnType`].
    pub fn number(&self, column: &str) -> Result<f64, SqliteError> {
        self.required(column)?
            .as_number()
            .ok_or_else(|| SqliteError::column_type(column, "a number"))
    }

    fn required(&self, column: &str) -> Result<&SqliteValue, SqliteError> {
        self.value(column)
            .ok_or_else(|| SqliteError::MissingColumn(column.to_owned()))
    }
}

impl<K: Into<Arc<str>>, V: Into<SqliteValue>> FromIterator<(K, V)> for SqliteRow {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        Self::new(
            iter.into_iter()
                .map(|(name, value)| (name.into(), value.into()))
                .collect(),
        )
    }
}

impl PartialEq for SqliteRow {
    fn eq(&self, other: &Self) -> bool {
        let covers = |left: &Self, right: &Self| {
            left.columns
                .iter()
                .all(|(name, _)| left.value(name) == right.value(name))
        };
        covers(self, other) && covers(other, self)
    }
}

fn is_safe_integer(value: f64) -> bool {
    #[expect(clippy::cast_precision_loss, reason = "2^53 - 1 is exact in f64")]
    let max = MAX_SAFE_INTEGER as f64;
    value.fract() == 0.0 && value.abs() <= max
}

/// Errors raised by the SQLite facade and its adapters.
#[derive(Debug, Clone, thiserror::Error)]
pub enum SqliteError {
    /// A transaction handle was used after its transaction settled.
    #[error("SQLite transaction handle is no longer active")]
    TransactionInactive,
    /// TS `AggregateError([error, rollbackError], …)`: the transaction failed and its rollback
    /// failed too, so the transaction is not guaranteed to be rolled back.
    #[error("SQLite transaction failed and rollback failed")]
    RollbackFailed {
        /// The callback or commit error that started the rollback.
        error: Arc<dyn Error + Send + Sync>,
        /// The rollback failure.
        rollback_error: Box<SqliteError>,
    },
    /// An adapter reported success without running the callback to completion.
    #[error("SQLite transaction settled without its callback result")]
    MissingTransactionResult,
    /// A row lacks a column a reader requires.
    #[error("SQLite row has no column {0}")]
    MissingColumn(String),
    /// A row column holds a value of another type than a reader requires.
    #[error("SQLite column {column} is not {expected}")]
    ColumnType {
        column: String,
        expected: &'static str,
    },
    /// An error raised by an adapter (the SQLite engine, the file system, or adapter logic).
    #[error(transparent)]
    Adapter(Arc<dyn Error + Send + Sync>),
}

impl SqliteError {
    /// Wrap an adapter error.
    pub fn adapter(error: impl Error + Send + Sync + 'static) -> Self {
        Self::Adapter(Arc::new(error))
    }

    fn column_type(column: &str, expected: &'static str) -> Self {
        Self::ColumnType {
            column: column.to_owned(),
            expected,
        }
    }
}

/// Asynchronous SQL operations shared by a database and its transaction handles.
///
/// `exec` runs SQL text without bindings and may contain several statements. `run`, `get`,
/// and `all` execute one statement with positional bindings. Adapters may cache prepared
/// statements by SQL text, so callers pass values as bindings instead of interpolating them.
///
/// Implementations start the operation when the method is called (JS promises run eagerly):
/// operations take effect in call order, and the returned future only reports the result.
/// Dropping the future does not cancel the operation.
pub trait SqliteExecutor: Send + Sync {
    /// Run SQL text without bindings.
    fn exec(&self, sql: Cow<'static, str>) -> BoxFuture<'static, Result<(), SqliteError>>;
    /// Run one statement to completion.
    fn run(
        &self,
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
    ) -> BoxFuture<'static, Result<(), SqliteError>>;
    /// Run one statement and return its first row.
    fn get(
        &self,
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
    ) -> BoxFuture<'static, Result<Option<SqliteRow>, SqliteError>>;
    /// Run one statement and return every row.
    fn all(
        &self,
        sql: Cow<'static, str>,
        params: Vec<SqliteValue>,
    ) -> BoxFuture<'static, Result<Vec<SqliteRow>, SqliteError>>;
}

/// Transaction handle passed to a transaction callback; valid only until the callback
/// settles. Later use fails with [`SqliteError::TransactionInactive`].
pub type SqliteTransaction = Arc<dyn SqliteExecutor>;

/// Type-erased error of a transaction callback.
pub type TransactionCallbackError = Box<dyn Error + Send + Sync>;

/// Type-erased transaction callback of [`SqliteDatabase::transaction_dyn`]. Its result value
/// travels out of band (see [`SqliteDatabaseExt::transaction`]); only its error is erased.
pub type TransactionCallback<'a> = Box<
    dyn FnOnce(SqliteTransaction) -> BoxFuture<'a, Result<(), TransactionCallbackError>>
        + Send
        + 'a,
>;

/// Why [`SqliteDatabase::transaction_dyn`] failed.
#[derive(Debug)]
pub enum TransactionFailure {
    /// The callback failed and the transaction was rolled back: exactly the callback's error.
    Callback(TransactionCallbackError),
    /// The database failed: `BEGIN` or `COMMIT` failed, or rollback failed
    /// ([`SqliteError::RollbackFailed`]).
    Database(SqliteError),
}

/// Minimal database facade required by `SqliteStorage`.
///
/// All operations are asynchronous so adapters may execute outside the harness runtime.
///
/// `transaction_dyn` passes the callback a transaction handle. All work in the transaction
/// must use that handle; the handle is invalid after the callback settles. Adapters must
/// queue unrelated operations and other transactions until the transaction finishes, in call
/// order (the transaction is queued when `transaction_dyn` is called). The returned future
/// settles after commit or rollback. Calling the database itself (including a transaction or
/// `close`) from inside a callback therefore waits for that transaction; awaiting such a call
/// inside the callback never settles.
///
/// When the callback fails, the adapter must roll the transaction back before failing with
/// that same error ([`TransactionFailure::Callback`]). If rollback fails, it must fail with
/// [`SqliteError::RollbackFailed`] so callers cannot mistake the callback error for a
/// guaranteed rollback. When `COMMIT` fails, the adapter rolls back and fails with the commit
/// error (or [`SqliteError::RollbackFailed`]).
///
/// `close` is queued behind earlier operations; later operations fail.
pub trait SqliteDatabase: SqliteExecutor {
    /// Object-safe transaction; use the typed [`SqliteDatabaseExt::transaction`].
    fn transaction_dyn<'a>(
        &'a self,
        callback: TransactionCallback<'a>,
    ) -> BoxFuture<'a, Result<(), TransactionFailure>>;

    /// Release the database once earlier operations finish.
    fn close(&self) -> BoxFuture<'static, Result<(), SqliteError>>;
}

/// Typed transactions over any [`SqliteDatabase`], including `dyn SqliteDatabase`.
pub trait SqliteDatabaseExt: SqliteDatabase {
    /// TS `transaction<T>(callback)`: run `callback` in one transaction and return its value.
    ///
    /// The callback's own error comes back unchanged. An error an adapter substitutes for it
    /// (another error type) arrives as [`SqliteError::Adapter`]; database failures arrive as
    /// [`SqliteError`]; both convert through `E: From<SqliteError>`.
    fn transaction<'a, T, E, F, Fut>(&'a self, callback: F) -> BoxFuture<'a, Result<T, E>>
    where
        T: Send + 'a,
        E: Error + From<SqliteError> + Send + Sync + 'static,
        F: FnOnce(SqliteTransaction) -> Fut + Send + 'a,
        Fut: Future<Output = Result<T, E>> + Send + 'a,
    {
        let slot: Arc<Mutex<Option<T>>> = Arc::new(Mutex::new(None));
        let writer = Arc::clone(&slot);
        let settled = self.transaction_dyn(Box::new(move |transaction| {
            Box::pin(async move {
                let value = callback(transaction)
                    .await
                    .map_err(|error| Box::new(error) as TransactionCallbackError)?;
                *writer.lock().unwrap_or_else(PoisonError::into_inner) = Some(value);
                Ok(())
            })
        }));
        Box::pin(async move {
            match settled.await {
                Ok(()) => slot
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .take()
                    .ok_or_else(|| E::from(SqliteError::MissingTransactionResult)),
                Err(TransactionFailure::Callback(error)) => Err(match error.downcast::<E>() {
                    Ok(error) => *error,
                    Err(other) => E::from(SqliteError::Adapter(Arc::from(other))),
                }),
                Err(TransactionFailure::Database(error)) => Err(E::from(error)),
            }
        })
    }
}

impl<D: SqliteDatabase + ?Sized> SqliteDatabaseExt for D {}
