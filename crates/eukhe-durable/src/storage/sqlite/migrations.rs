//! Durable SQLite schema history. Port of `storage/sqlite/migrations.ts`.
//!
//! The SQL text is byte-identical to the TS source, so files created by either port are
//! interchangeable.

use super::database::{SqliteDatabase, SqliteDatabaseExt, SqliteError, SqliteTransaction};

/// One immutable schema migration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SqliteMigration {
    pub version: i64,
    pub statements: &'static [&'static str],
}

// next_id is TEXT because node:sqlite rejects INTEGER results outside JavaScript's safe integer range.
const INITIAL_SCHEMA: &[&str] = &[
    "CREATE TABLE durable_metadata (
		singleton INTEGER PRIMARY KEY CHECK (singleton = 1),
		next_id TEXT NOT NULL,
		next_seq INTEGER NOT NULL
	) STRICT",
    "INSERT INTO durable_metadata (singleton, next_id, next_seq) VALUES (1, '2', 1)",
    "CREATE TABLE record_ids (
		id INTEGER PRIMARY KEY,
		record_type TEXT NOT NULL CHECK (record_type IN ('conversation', 'entry', 'task', 'submission', 'document'))
	) STRICT",
    "CREATE TABLE conversations (
		id INTEGER PRIMARY KEY,
		owner_conversation_id INTEGER,
		owner_task_id INTEGER,
		record TEXT NOT NULL CHECK (json_valid(record))
	) STRICT",
    "CREATE INDEX conversations_by_owner_conversation ON conversations (owner_conversation_id, id)",
    "CREATE INDEX conversations_by_owner_task ON conversations (owner_task_id, id)",
    "CREATE TABLE entries (
		id INTEGER PRIMARY KEY,
		conversation_id INTEGER NOT NULL,
		head INTEGER,
		commit_seq INTEGER NOT NULL,
		record TEXT NOT NULL CHECK (json_valid(record))
	) STRICT",
    "CREATE INDEX entries_by_conversation ON entries (conversation_id, id DESC)",
    "CREATE INDEX entry_heads_by_conversation ON entries (conversation_id, id DESC) WHERE head IS NOT NULL",
    "CREATE TABLE tasks (
		id INTEGER PRIMARY KEY,
		conversation_id INTEGER NOT NULL,
		kind TEXT NOT NULL,
		status TEXT NOT NULL CHECK (status IN ('pending', 'running', 'waiting', 'completing', 'terminal')),
		abort_requested INTEGER NOT NULL CHECK (abort_requested IN (0, 1)),
		background INTEGER NOT NULL CHECK (background IN (0, 1)),
		record TEXT NOT NULL CHECK (json_valid(record))
	) STRICT",
    "CREATE INDEX tasks_by_status ON tasks (status, id)",
    "CREATE INDEX tasks_by_conversation ON tasks (conversation_id, id)",
    "CREATE INDEX tasks_by_kind ON tasks (kind, id)",
    "CREATE INDEX tasks_by_abort_requested ON tasks (abort_requested, id)",
    "CREATE INDEX tasks_by_background ON tasks (background, id)",
    "CREATE TABLE submissions (
		id INTEGER PRIMARY KEY,
		conversation_id INTEGER NOT NULL,
		request_id TEXT,
		status TEXT NOT NULL CHECK (status IN ('queued', 'placed', 'done', 'unanswered')),
		record TEXT NOT NULL CHECK (json_valid(record))
	) STRICT",
    "CREATE INDEX submissions_by_request ON submissions (conversation_id, request_id)",
    "CREATE INDEX submissions_by_conversation ON submissions (conversation_id, id)",
    "CREATE INDEX submissions_by_status ON submissions (status, id)",
    "CREATE TABLE documents (
		id INTEGER PRIMARY KEY,
		kind TEXT NOT NULL,
		family INTEGER NOT NULL CHECK (family IN (0, 1)),
		key_value TEXT NOT NULL,
		scope_kind TEXT NOT NULL CHECK (scope_kind IN ('session', 'conversation', 'task')),
		owner_id INTEGER NOT NULL,
		created_at INTEGER NOT NULL,
		retired_at INTEGER,
		record TEXT NOT NULL CHECK (json_valid(record))
	) STRICT",
    "CREATE INDEX documents_by_address
		ON documents (kind, scope_kind, owner_id, family, key_value, created_at DESC, retired_at)",
    "CREATE INDEX documents_by_scope ON documents (scope_kind, owner_id, id)",
    "CREATE INDEX documents_by_scope_kind ON documents (scope_kind, owner_id, kind, id)",
    "CREATE TABLE document_revisions (
		document_id INTEGER NOT NULL,
		seq INTEGER NOT NULL,
		kind TEXT NOT NULL CHECK (kind IN ('base', 'delta')),
		version INTEGER NOT NULL,
		content TEXT NOT NULL CHECK (json_valid(content)),
		PRIMARY KEY (document_id, seq)
	) STRICT",
    "CREATE INDEX document_revisions_by_kind ON document_revisions (document_id, kind, seq DESC)",
];

/// Immutable, ordered schema history. Append new migrations after the initial schema ships.
pub const SQLITE_MIGRATIONS: &[SqliteMigration] = &[SqliteMigration {
    version: 1,
    statements: INITIAL_SCHEMA,
}];

/// Version of the last migration in [`SQLITE_MIGRATIONS`].
pub const CURRENT_SQLITE_SCHEMA_VERSION: i64 = match SQLITE_MIGRATIONS.last() {
    Some(migration) => migration.version,
    None => 0,
};

/// Why [`apply_sqlite_migrations`] failed.
#[derive(Debug, Clone, thiserror::Error)]
pub enum SqliteMigrationError {
    #[error("Durable SQLite migrations must have contiguous versions starting at 1")]
    NonContiguousVersions,
    #[error("Durable SQLite schema metadata is missing")]
    MissingSchemaMetadata,
    #[error("Durable SQLite schema version {version} is newer than supported version {supported}")]
    NewerSchema { version: i64, supported: i64 },
    #[error(transparent)]
    Sqlite(#[from] SqliteError),
}

/// Apply all pending schema migrations atomically. TS default `migrations` is
/// [`SQLITE_MIGRATIONS`].
///
/// # Errors
/// Non-contiguous `migrations`, a database newer than `migrations`, or a SQLite failure; the
/// bootstrap and every pending migration roll back together.
pub async fn apply_sqlite_migrations<D: SqliteDatabase + ?Sized>(
    database: &D,
    migrations: &[SqliteMigration],
) -> Result<(), SqliteMigrationError> {
    for (expected, migration) in (1_i64..).zip(migrations) {
        if migration.version != expected {
            return Err(SqliteMigrationError::NonContiguousVersions);
        }
    }

    database
        .transaction(|transaction: SqliteTransaction| async move {
            transaction
                .exec(
                    "CREATE TABLE IF NOT EXISTS durable_schema (
\t\t\tsingleton INTEGER PRIMARY KEY CHECK (singleton = 1),
\t\t\tversion INTEGER NOT NULL CHECK (version >= 0)
\t\t) STRICT"
                        .into(),
                )
                .await?;
            transaction
                .run(
                    "INSERT OR IGNORE INTO durable_schema (singleton, version) VALUES (1, 0)"
                        .into(),
                    Vec::new(),
                )
                .await?;
            let row = transaction
                .get(
                    "SELECT version FROM durable_schema WHERE singleton = 1".into(),
                    Vec::new(),
                )
                .await?
                .ok_or(SqliteMigrationError::MissingSchemaMetadata)?;
            let version = row.integer("version")?;
            let current_version = migrations.last().map_or(0, |migration| migration.version);
            if version > current_version {
                return Err(SqliteMigrationError::NewerSchema {
                    version,
                    supported: current_version,
                });
            }
            for migration in migrations {
                if migration.version <= version {
                    continue;
                }
                for statement in migration.statements {
                    transaction.exec((*statement).into()).await?;
                }
                transaction
                    .run(
                        "UPDATE durable_schema SET version = ? WHERE singleton = 1".into(),
                        vec![migration.version.into()],
                    )
                    .await?;
            }
            Ok(())
        })
        .await
}
