//! SQLite durable storage (`storage/sqlite/index.ts`) and its native adapter
//! (`storage/sqlite/node.ts`).
//!
//! `database`, `migrations`, and `storage` are portable: they depend only on the
//! [`SqliteDatabase`] facade. `native` adapts a bundled SQLite to that facade.

mod database;
mod migrations;
mod native;
mod storage;

pub use database::{
    SqliteDatabase, SqliteDatabaseExt, SqliteError, SqliteExecutor, SqliteRow, SqliteTransaction,
    SqliteValue, TransactionCallback, TransactionCallbackError, TransactionFailure,
};
pub use migrations::{
    apply_sqlite_migrations, SqliteMigration, SqliteMigrationError, CURRENT_SQLITE_SCHEMA_VERSION,
    SQLITE_MIGRATIONS,
};
pub use native::{
    open_native_sqlite_database, open_native_sqlite_storage, NativeSqliteDatabase,
    NativeSqliteError, NativeSqliteStorageOptions, PrepareObserver,
};
pub use storage::SqliteStorage;
