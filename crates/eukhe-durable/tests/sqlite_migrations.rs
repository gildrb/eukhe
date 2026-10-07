//! Port of `test/sqlite-migrations.test.ts`: durable SQLite migrations.

use std::path::PathBuf;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::{to_json, JsonValue};
use eukhe_durable::storage::sqlite::{
    apply_sqlite_migrations, open_native_sqlite_database, open_native_sqlite_storage,
    NativeSqliteStorageOptions, SqliteDatabase, SqliteExecutor, SqliteMigration, SqliteRow,
    SqliteValue, CURRENT_SQLITE_SCHEMA_VERSION, SQLITE_MIGRATIONS,
};
use eukhe_durable::types::{
    ConversationRecord, EntryId, EntryRecord, Storage, StorageWrite, ROOT_CONVERSATION_ID,
};
use tempfile::TempDir;

fn database_path() -> (TempDir, PathBuf) {
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-migrations-")
        .tempdir()
        .unwrap();
    let path = directory.path().join("storage.sqlite");
    (directory, path)
}

fn row(columns: &[(&str, SqliteValue)]) -> SqliteRow {
    columns
        .iter()
        .map(|(name, value)| (*name, value.clone()))
        .collect()
}

fn options() -> NativeSqliteStorageOptions {
    NativeSqliteStorageOptions::default()
}

#[tokio::test]
async fn creates_the_current_schema_and_can_be_applied_repeatedly() {
    let (_directory, path) = database_path();
    let database = open_native_sqlite_database(&path, options()).await.unwrap();
    apply_sqlite_migrations(&database, SQLITE_MIGRATIONS)
        .await
        .unwrap();
    apply_sqlite_migrations(&database, SQLITE_MIGRATIONS)
        .await
        .unwrap();
    assert_eq!(
        database
            .get(
                "SELECT version FROM durable_schema WHERE singleton = 1".into(),
                Vec::new()
            )
            .await
            .unwrap(),
        Some(row(&[(
            "version",
            SqliteValue::Integer(CURRENT_SQLITE_SCHEMA_VERSION)
        )]))
    );
    assert_eq!(
        database
            .get(
                "SELECT next_id, next_seq FROM durable_metadata WHERE singleton = 1".into(),
                Vec::new()
            )
            .await
            .unwrap(),
        Some(row(&[
            ("next_id", SqliteValue::Text("2".to_owned())),
            ("next_seq", SqliteValue::Integer(1)),
        ]))
    );
    database.close().await.unwrap();
}

#[tokio::test]
async fn rejects_a_database_newer_than_the_portable_core() {
    let (_directory, path) = database_path();
    let database = open_native_sqlite_database(&path, options()).await.unwrap();
    apply_sqlite_migrations(&database, SQLITE_MIGRATIONS)
        .await
        .unwrap();
    database
        .run(
            "UPDATE durable_schema SET version = ? WHERE singleton = 1".into(),
            vec![(CURRENT_SQLITE_SCHEMA_VERSION + 1).into()],
        )
        .await
        .unwrap();
    database.close().await.unwrap();

    let error = open_native_sqlite_storage(&path, options())
        .await
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("is newer than supported version"),
        "{error}"
    );
}

#[tokio::test]
async fn rolls_initial_bootstrap_and_every_pending_migration_back_together() {
    let (_directory, path) = database_path();
    let database = open_native_sqlite_database(&path, options()).await.unwrap();
    let failed = [
        SqliteMigration {
            version: 1,
            statements: &[
                "CREATE TABLE migration_first (value TEXT) STRICT",
                "INSERT INTO migration_first (value) VALUES ('retained')",
            ],
        },
        SqliteMigration {
            version: 2,
            statements: &[
                "CREATE TABLE migration_second (value TEXT) STRICT",
                "THIS IS NOT SQL",
            ],
        },
    ];
    assert!(apply_sqlite_migrations(&database, &failed).await.is_err());
    assert_eq!(
        database
            .get(
                "SELECT count(*) AS count FROM sqlite_schema WHERE name IN ('durable_schema', 'migration_first', 'migration_second')".into(),
                Vec::new()
            )
            .await
            .unwrap(),
        Some(row(&[("count", SqliteValue::Integer(0))]))
    );

    apply_sqlite_migrations(
        &database,
        &[
            failed[0],
            SqliteMigration {
                version: 2,
                statements: &["CREATE TABLE migration_second (value TEXT) STRICT"],
            },
        ],
    )
    .await
    .unwrap();
    assert_eq!(
        database
            .get(
                "SELECT version FROM durable_schema WHERE singleton = 1".into(),
                Vec::new()
            )
            .await
            .unwrap(),
        Some(row(&[("version", SqliteValue::Integer(2))]))
    );
    assert_eq!(
        database
            .get("SELECT value FROM migration_first".into(), Vec::new())
            .await
            .unwrap(),
        Some(row(&[("value", SqliteValue::Text("retained".to_owned()))]))
    );
    database.close().await.unwrap();
}

#[expect(clippy::too_many_lines, reason = "1:1 port of one TS test")]
#[tokio::test]
async fn rolls_a_failed_migration_back_and_preserves_stored_data_for_a_successful_retry() {
    let (_directory, path) = database_path();
    let cx = &*BACKGROUND_CONTEXT;
    let storage = open_native_sqlite_storage(&path, options()).await.unwrap();
    let retained = EntryRecord {
        model: None,
        data: Some(JsonValue::from(serde_json::json!({ "retained": true }))),
        edits: None,
        kind: "retained".to_owned(),
        id: EntryId::from_number(2),
        conversation_id: ROOT_CONVERSATION_ID,
        head: None,
        by_task_id: None,
    };
    storage
        .commit(
            &[
                StorageWrite::Conversation {
                    value: ConversationRecord {
                        id: ROOT_CONVERSATION_ID,
                        parent: None,
                        owner: None,
                    },
                },
                StorageWrite::Entry {
                    value: retained.clone(),
                },
            ],
            cx,
        )
        .await
        .unwrap();
    storage.close(cx).await.unwrap();

    let database = open_native_sqlite_database(&path, options()).await.unwrap();
    let next_version = CURRENT_SQLITE_SCHEMA_VERSION + 1;
    let mut failed_migrations = SQLITE_MIGRATIONS.to_vec();
    failed_migrations.push(SqliteMigration {
        version: next_version,
        statements: &[
            "CREATE TABLE migration_probe (value TEXT) STRICT",
            "THIS IS NOT SQL",
        ],
    });
    assert!(apply_sqlite_migrations(&database, &failed_migrations)
        .await
        .is_err());
    assert_eq!(
        database
            .get(
                "SELECT version FROM durable_schema WHERE singleton = 1".into(),
                Vec::new()
            )
            .await
            .unwrap(),
        Some(row(&[(
            "version",
            SqliteValue::Integer(CURRENT_SQLITE_SCHEMA_VERSION)
        )]))
    );
    assert_eq!(
        database
            .get(
                "SELECT count(*) AS count FROM sqlite_schema WHERE type = 'table' AND name = 'migration_probe'".into(),
                Vec::new()
            )
            .await
            .unwrap(),
        Some(row(&[("count", SqliteValue::Integer(0))]))
    );

    let mut successful_migrations = SQLITE_MIGRATIONS.to_vec();
    successful_migrations.push(SqliteMigration {
        version: next_version,
        statements: &["CREATE TABLE migration_probe (value TEXT) STRICT"],
    });
    apply_sqlite_migrations(&database, &successful_migrations)
        .await
        .unwrap();
    assert_eq!(
        database
            .get(
                "SELECT version FROM durable_schema WHERE singleton = 1".into(),
                Vec::new()
            )
            .await
            .unwrap(),
        Some(row(&[("version", SqliteValue::Integer(next_version))]))
    );
    assert_eq!(
        database
            .get(
                "SELECT record, commit_seq FROM entries WHERE id = 2".into(),
                Vec::new()
            )
            .await
            .unwrap(),
        Some(row(&[
            (
                "record",
                // The exact `JSON.stringify` text of the committed record (the TS test spells
                // the same text as an object literal in its own key order).
                SqliteValue::Text(to_json(&retained).unwrap().to_string())
            ),
            ("commit_seq", SqliteValue::Integer(1)),
        ]))
    );
    assert_eq!(
        database
            .get(
                "SELECT next_id, next_seq FROM durable_metadata WHERE singleton = 1".into(),
                Vec::new()
            )
            .await
            .unwrap(),
        Some(row(&[
            ("next_id", SqliteValue::Text("3".to_owned())),
            ("next_seq", SqliteValue::Integer(2)),
        ]))
    );
    database.close().await.unwrap();
}
