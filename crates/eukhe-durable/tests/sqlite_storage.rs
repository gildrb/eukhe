//! Port of `test/sqlite-storage.test.ts`: Pico `SqliteStorage`.
//!
//! The storage conformance registrations of the TS file live with the conformance suite.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::delta::Op;
use eukhe_chord::json::{JsonObject, JsonValue};
use eukhe_durable::ids::mint;
use eukhe_durable::storage::sqlite::{
    open_native_sqlite_storage, NativeSqliteStorageOptions, SqliteStorage,
};
use eukhe_durable::types::{
    AnyTaskRecord, ConversationId, ConversationRecord, ConversationSemantics, DocumentBase,
    DocumentContent, DocumentCopySource, DocumentCreate, DocumentDelta, DocumentId, DocumentPoint,
    DocumentRecordScope, EntryId, EntryRecord, RewindableFork, Seq, Storage, StorageWrite,
    StoredEntry, TaskId, TaskState, ROOT_CONVERSATION_ID,
};
use rusqlite::{Connection, OpenFlags};
use tempfile::TempDir;

struct Created {
    storage: SqliteStorage,
    path: PathBuf,
    _directory: TempDir,
}

async fn create_sqlite_storage(options: NativeSqliteStorageOptions) -> Created {
    let directory = tempfile::Builder::new()
        .prefix("pi-durable-sqlite-")
        .tempdir()
        .unwrap();
    let path = directory.path().join("storage.sqlite");
    let storage = open_native_sqlite_storage(&path, options).await.unwrap();
    Created {
        storage,
        path,
        _directory: directory,
    }
}

fn entry(
    id: EntryId,
    conversation_id: ConversationId,
    data: Option<serde_json::Value>,
) -> EntryRecord {
    EntryRecord {
        model: None,
        data: data.map(JsonValue::from),
        edits: None,
        kind: "message".to_owned(),
        id,
        conversation_id,
        head: None,
        by_task_id: None,
    }
}

async fn create_root(storage: &dyn Storage) -> Seq {
    storage
        .commit(
            &[StorageWrite::Conversation {
                value: ConversationRecord {
                    id: ROOT_CONVERSATION_ID,
                    parent: None,
                    owner: None,
                },
            }],
            &BACKGROUND_CONTEXT,
        )
        .await
        .unwrap()
}

fn pending_task(id: TaskId) -> AnyTaskRecord {
    AnyTaskRecord {
        id,
        conversation_id: ROOT_CONVERSATION_ID,
        kind: "test.task".to_owned(),
        version: 1,
        input: JsonValue::Null,
        owner: None,
        background: false,
        abort_requested: false,
        state: TaskState::Pending {
            checkpoint: JsonValue::from(serde_json::json!({ "phase": "ready" })),
        },
        memos: None,
        started_at: None,
        ended_at: None,
        abandon_on_restart: false,
        abort_reason: None,
    }
}

fn object(value: serde_json::Value) -> Arc<JsonObject> {
    match JsonValue::from(value) {
        JsonValue::Object(object) => object,
        other => panic!("not an object: {other}"),
    }
}

fn ops(value: serde_json::Value) -> Arc<[Op]> {
    JsonValue::from(value)
        .as_array()
        .unwrap()
        .iter()
        .map(|op| Op::from_json(op).unwrap())
        .collect()
}

fn base(version: u64, value: serde_json::Value) -> DocumentBase {
    DocumentBase {
        version,
        value: object(value),
    }
}

fn delta(version: u64, value: serde_json::Value) -> DocumentContent {
    DocumentContent::Delta(DocumentDelta {
        version,
        ops: ops(value),
    })
}

fn session_document(id: DocumentId, kind: &str) -> DocumentCreate {
    DocumentCreate {
        id,
        kind: kind.to_owned(),
        key: None,
        scope: DocumentRecordScope::Session,
    }
}

fn rewindable_document(id: DocumentId, kind: &str) -> DocumentCreate {
    DocumentCreate {
        id,
        kind: kind.to_owned(),
        key: None,
        scope: DocumentRecordScope::Conversation {
            conversation_id: ROOT_CONVERSATION_ID,
            semantics: ConversationSemantics::Rewindable(RewindableFork::AsOf),
        },
    }
}

fn sql_id(id: u64) -> i64 {
    i64::try_from(id).unwrap()
}

fn read_only(path: &Path) -> Connection {
    Connection::open_with_flags(path, OpenFlags::SQLITE_OPEN_READ_ONLY).unwrap()
}

fn scalar(db: &Connection, sql: &str) -> i64 {
    db.query_row(sql, [], |row| row.get("value")).unwrap()
}

fn revision_count(path: &Path, document_id: DocumentId) -> i64 {
    let db = read_only(path);
    db.query_row(
        "SELECT count(*) AS count FROM document_revisions WHERE document_id = ?",
        [sql_id(document_id.get())],
        |row| row.get("count"),
    )
    .unwrap()
}

#[tokio::test]
async fn persists_records_sequence_allocation_and_global_id_allocation_across_reopen() {
    let cx = &*BACKGROUND_CONTEXT;
    let Created {
        storage,
        path,
        _directory,
    } = create_sqlite_storage(NativeSqliteStorageOptions::default()).await;
    assert_eq!(create_root(&storage).await.get(), 1);
    let entry_id: EntryId = mint(&storage).await.unwrap();
    assert_eq!(
        storage
            .commit(
                &[StorageWrite::Entry {
                    value: entry(entry_id, ROOT_CONVERSATION_ID, None)
                }],
                cx
            )
            .await
            .unwrap()
            .get(),
        2
    );
    storage.close(cx).await.unwrap();

    let reopened = open_native_sqlite_storage(&path, NativeSqliteStorageOptions::default())
        .await
        .unwrap();
    assert_eq!(
        reopened.entry(entry_id, cx).await.unwrap(),
        Some(StoredEntry {
            entry: entry(entry_id, ROOT_CONVERSATION_ID, None),
            commit_seq: Seq::from_number(2),
        })
    );
    assert_eq!(
        mint::<EntryId, _>(&reopened).await.unwrap().get(),
        entry_id.get() + 1
    );
    let task_id: TaskId = mint(&reopened).await.unwrap();
    assert_eq!(
        reopened
            .commit(
                &[StorageWrite::Task {
                    value: pending_task(task_id)
                }],
                cx
            )
            .await
            .unwrap()
            .get(),
        3
    );
    reopened.close(cx).await.unwrap();
}

#[tokio::test]
async fn rejects_persisted_metadata_corruption_on_reopen() {
    let Created {
        storage,
        path,
        _directory,
    } = create_sqlite_storage(NativeSqliteStorageOptions::default()).await;
    storage.close(&BACKGROUND_CONTEXT).await.unwrap();
    let database = Connection::open(&path).unwrap();
    database
        .execute_batch("DELETE FROM durable_metadata")
        .unwrap();
    database.close().unwrap();
    let error = open_native_sqlite_storage(&path, NativeSqliteStorageOptions::default())
        .await
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("Durable SQLite metadata is missing"),
        "{error}"
    );
}

#[tokio::test]
async fn rejects_a_document_whose_required_base_is_missing() {
    let cx = &*BACKGROUND_CONTEXT;
    let Created {
        storage,
        path,
        _directory,
    } = create_sqlite_storage(NativeSqliteStorageOptions::default()).await;
    create_root(&storage).await;
    let id: DocumentId = mint(&storage).await.unwrap();
    storage
        .commit(
            &[StorageWrite::DocumentCreate {
                record: session_document(id, "corrupt"),
                content: base(1, serde_json::json!({ "retained": true })),
            }],
            cx,
        )
        .await
        .unwrap();
    let database = Connection::open(&path).unwrap();
    database
        .execute(
            "DELETE FROM document_revisions WHERE document_id = ?",
            [sql_id(id.get())],
        )
        .unwrap();
    database.close().unwrap();
    let error = storage
        .document(id, DocumentPoint::Current, cx)
        .await
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains(&format!("Document {id} is missing a required base")),
        "{error}"
    );
    storage.close(cx).await.unwrap();
}

#[tokio::test]
async fn replays_detached_root_replacements_and_follow_up_edits_while_rejecting_corrupt_operations()
{
    let cx = &*BACKGROUND_CONTEXT;
    let Created {
        storage,
        path,
        _directory,
    } = create_sqlite_storage(NativeSqliteStorageOptions::default()).await;
    create_root(&storage).await;
    let id: DocumentId = mint(&storage).await.unwrap();
    storage
        .commit(
            &[StorageWrite::DocumentCreate {
                record: session_document(id, "replay"),
                content: base(
                    1,
                    serde_json::json!({ "nested": { "value": 1 }, "rows": [] }),
                ),
            }],
            cx,
        )
        .await
        .unwrap();
    for content in [
        delta(
            1,
            serde_json::json!([["r", { "nested": { "value": 2 }, "rows": [{ "id": 1 }] }]]),
        ),
        delta(
            1,
            serde_json::json!([
                ["s", ["nested", "value"], 3],
                ["p", ["rows"], 1, 0, [{ "id": 2 }]],
                ["m", ["rows"], [1, 0]],
            ]),
        ),
        delta(1, serde_json::json!([["s", ["nested", "value"], 4]])),
    ] {
        storage
            .commit(&[StorageWrite::DocumentChange { id, content }], cx)
            .await
            .unwrap();
    }

    let expected =
        object(serde_json::json!({ "nested": { "value": 4 }, "rows": [{ "id": 2 }, { "id": 1 }] }));
    let first = storage
        .document(id, DocumentPoint::Current, cx)
        .await
        .unwrap()
        .unwrap();
    assert_eq!(first.value, expected);
    // Mutating a returned value must not change what storage returns next.
    let mut value = first.value;
    let detached = Arc::make_mut(&mut value);
    detached
        .get_mut("nested")
        .and_then(JsonValue::as_object_mut)
        .unwrap()
        .insert("value", JsonValue::from(99));
    detached
        .get_mut("rows")
        .and_then(JsonValue::as_array_mut)
        .unwrap()[0]
        .as_object_mut()
        .unwrap()
        .insert("id", JsonValue::from(99));
    assert_eq!(
        storage
            .document(id, DocumentPoint::Current, cx)
            .await
            .unwrap()
            .unwrap()
            .value,
        expected
    );

    let database = Connection::open(&path).unwrap();
    database
        .execute(
            "UPDATE document_revisions SET content = ? WHERE document_id = ? AND seq =
					(SELECT max(seq) FROM document_revisions WHERE document_id = ?)",
            rusqlite::params![r#"[["unknown"]]"#, sql_id(id.get()), sql_id(id.get())],
        )
        .unwrap();
    database.close().unwrap();
    let error = storage
        .document(id, DocumentPoint::Current, cx)
        .await
        .unwrap_err();
    assert!(error.to_string().contains("unknown op verb"), "{error}");
    storage.close(cx).await.unwrap();
}

#[tokio::test]
async fn rolls_sql_rows_and_sequence_allocation_back_as_one_transaction() {
    let cx = &*BACKGROUND_CONTEXT;
    let Created {
        storage,
        path,
        _directory,
    } = create_sqlite_storage(NativeSqliteStorageOptions::default()).await;
    create_root(&storage).await;
    let transient_id: EntryId = mint(&storage).await.unwrap();
    let transient_task_id: TaskId = mint(&storage).await.unwrap();
    let transient_document_id: DocumentId = mint(&storage).await.unwrap();
    // TS fails the batch with a circular task input after the entry and task rows were
    // written; Rust records cannot be circular, so a document copy whose source cannot be
    // read fails the batch at the same point (after every table write).
    let error = storage
        .commit(
            &[
                StorageWrite::Entry {
                    value: entry(transient_id, ROOT_CONVERSATION_ID, None),
                },
                StorageWrite::Task {
                    value: pending_task(transient_task_id),
                },
                StorageWrite::DocumentCopy {
                    record: rewindable_document(transient_document_id, "copy"),
                    source: DocumentCopySource {
                        id: DocumentId::from_number(999),
                        at: DocumentPoint::Current,
                    },
                },
            ],
            cx,
        )
        .await
        .unwrap_err();
    assert!(
        error.to_string().contains(&format!(
            "Document copy {transient_document_id} was rejected"
        )),
        "{error}"
    );
    assert_eq!(storage.entry(transient_id, cx).await.unwrap(), None);
    assert_eq!(storage.task(transient_task_id, cx).await.unwrap(), None);
    let committed_id: EntryId = mint(&storage).await.unwrap();
    assert_eq!(
        storage
            .commit(
                &[StorageWrite::Entry {
                    value: entry(committed_id, ROOT_CONVERSATION_ID, None)
                }],
                cx
            )
            .await
            .unwrap()
            .get(),
        2
    );

    let db = read_only(&path);
    assert_eq!(scalar(&db, "SELECT count(*) AS value FROM entries"), 1);
    assert_eq!(
        scalar(
            &db,
            "SELECT next_seq AS value FROM durable_metadata WHERE singleton = 1"
        ),
        3
    );
    db.close().unwrap();
    storage.close(cx).await.unwrap();
}

#[tokio::test]
async fn reconstructs_recent_and_ancient_rewindable_points_after_reopen() {
    let cx = &*BACKGROUND_CONTEXT;
    let Created {
        storage,
        path,
        _directory,
    } = create_sqlite_storage(NativeSqliteStorageOptions::default()).await;
    create_root(&storage).await;
    let id: DocumentId = mint(&storage).await.unwrap();
    let created_at = storage
        .commit(
            &[StorageWrite::DocumentCreate {
                record: rewindable_document(id, "history"),
                content: base(1, serde_json::json!({ "count": 0 })),
            }],
            cx,
        )
        .await
        .unwrap();
    let mut ancient_at = created_at;
    let mut recent_at = created_at;
    for count in 1..=40 {
        let content = if count == 20 {
            DocumentContent::Base(base(1, serde_json::json!({ "count": count })))
        } else {
            delta(1, serde_json::json!([["s", ["count"], count]]))
        };
        recent_at = storage
            .commit(&[StorageWrite::DocumentChange { id, content }], cx)
            .await
            .unwrap();
        if count == 5 {
            ancient_at = recent_at;
        }
    }
    storage.close(cx).await.unwrap();
    let reopened = open_native_sqlite_storage(&path, NativeSqliteStorageOptions::default())
        .await
        .unwrap();
    assert_eq!(
        reopened
            .document(id, DocumentPoint::At(ancient_at), cx)
            .await
            .unwrap()
            .unwrap()
            .value,
        object(serde_json::json!({ "count": 5 }))
    );
    assert_eq!(
        reopened
            .document(id, DocumentPoint::At(recent_at), cx)
            .await
            .unwrap()
            .unwrap()
            .value,
        object(serde_json::json!({ "count": 40 }))
    );
    reopened.close(cx).await.unwrap();
}

fn plan(db: &Connection, sql: &str, params: impl rusqlite::Params) -> String {
    let mut statement = db.prepare(sql).unwrap();
    let details: Vec<String> = statement
        .query_map(params, |row| row.get("detail"))
        .unwrap()
        .collect::<Result<_, _>>()
        .unwrap();
    details.join("\n")
}

#[expect(clippy::too_many_lines, reason = "1:1 port of one TS test")]
#[tokio::test]
async fn uses_indexes_for_exact_addresses_exact_scopes_entry_history_and_document_revision_tails() {
    let Created {
        storage,
        path,
        _directory,
    } = create_sqlite_storage(NativeSqliteStorageOptions::default()).await;
    storage.close(&BACKGROUND_CONTEXT).await.unwrap();
    let db = read_only(&path);
    let details = [
        plan(
            &db,
            "EXPLAIN QUERY PLAN SELECT record FROM documents
						WHERE kind = ? AND scope_kind = ? AND owner_id = ? AND family = ? AND key_value = ?
						AND retired_at IS NULL ORDER BY created_at DESC LIMIT 1",
            rusqlite::params!["kind", "session", 0, 0, ""],
        ),
        plan(
            &db,
            "EXPLAIN QUERY PLAN SELECT record FROM documents
						WHERE kind = ? AND scope_kind = ? AND owner_id = ? AND family = ? AND key_value = ?
						AND created_at <= ? AND (retired_at IS NULL OR retired_at > ?)
						ORDER BY created_at DESC LIMIT 1",
            rusqlite::params!["kind", "conversation", 1, 0, "", 10, 10],
        ),
        plan(
            &db,
            "EXPLAIN QUERY PLAN SELECT record FROM documents
						WHERE scope_kind = ? AND owner_id = ? AND kind = ? AND id > ? ORDER BY id LIMIT ?",
            rusqlite::params!["task", 1, "kind", 0, 10],
        ),
        plan(
            &db,
            "EXPLAIN QUERY PLAN SELECT record FROM entries
						WHERE conversation_id = ? AND id <= ? ORDER BY id DESC LIMIT ?",
            rusqlite::params![1, 10, 10],
        ),
        plan(
            &db,
            "EXPLAIN QUERY PLAN SELECT record FROM entries
						WHERE conversation_id = ? AND head IS NOT NULL AND id <= ? ORDER BY id DESC LIMIT 1",
            rusqlite::params![1, 10],
        ),
        plan(
            &db,
            "EXPLAIN QUERY PLAN SELECT record FROM tasks WHERE status = ? AND id > ? ORDER BY id LIMIT ?",
            rusqlite::params!["pending", 0, 10],
        ),
        plan(
            &db,
            "EXPLAIN QUERY PLAN SELECT seq, kind, version, content FROM document_revisions
						WHERE document_id = ? AND kind = 'base' AND seq <= ? ORDER BY seq DESC LIMIT 1",
            rusqlite::params![1, 10],
        ),
        plan(
            &db,
            "EXPLAIN QUERY PLAN SELECT seq, kind, version, content FROM document_revisions
						WHERE document_id = ? AND seq > ? AND seq <= ? ORDER BY seq",
            rusqlite::params![1, 5, 10],
        ),
    ];
    assert!(
        details[0].contains("documents_by_address"),
        "{}",
        details[0]
    );
    assert!(
        details[1].contains("documents_by_address"),
        "{}",
        details[1]
    );
    assert!(
        details[2].contains("documents_by_scope_kind"),
        "{}",
        details[2]
    );
    assert!(
        details[3].contains("entries_by_conversation"),
        "{}",
        details[3]
    );
    assert!(
        details[4].contains("entry_heads_by_conversation"),
        "{}",
        details[4]
    );
    assert!(details[5].contains("tasks_by_status"), "{}", details[5]);
    assert!(
        details[6].contains("document_revisions_by_kind"),
        "{}",
        details[6]
    );
    assert!(
        details[7].contains("sqlite_autoindex_document_revisions_1"),
        "{}",
        details[7]
    );
    for detail in &details[..3] {
        assert!(!detail.contains("SCAN documents"), "{detail}");
    }
    assert!(
        !details[7].contains("SCAN document_revisions"),
        "{}",
        details[7]
    );
    db.close().unwrap();
}

#[tokio::test]
async fn reclaims_current_only_revisions_only_after_a_base_or_retirement() {
    let cx = &*BACKGROUND_CONTEXT;
    let Created {
        storage,
        path,
        _directory,
    } = create_sqlite_storage(NativeSqliteStorageOptions::default()).await;
    create_root(&storage).await;
    let id: DocumentId = mint(&storage).await.unwrap();
    storage
        .commit(
            &[StorageWrite::DocumentCreate {
                record: session_document(id, "latest"),
                content: base(1, serde_json::json!({ "count": 0 })),
            }],
            cx,
        )
        .await
        .unwrap();
    for count in 1..=10 {
        storage
            .commit(
                &[StorageWrite::DocumentChange {
                    id,
                    content: delta(1, serde_json::json!([["s", ["count"], count]])),
                }],
                cx,
            )
            .await
            .unwrap();
    }
    assert_eq!(revision_count(&path, id), 11);
    let revisions = read_only(&path);
    let content: String = revisions
        .query_row(
            "SELECT content FROM document_revisions WHERE document_id = ? AND kind = 'delta' ORDER BY seq DESC LIMIT 1",
            [sql_id(id.get())],
            |row| row.get("content"),
        )
        .unwrap();
    assert_eq!(
        JsonValue::parse(&content).unwrap(),
        JsonValue::from(serde_json::json!([["s", ["count"], 10]]))
    );
    revisions.close().unwrap();
    storage
        .commit(
            &[StorageWrite::DocumentChange {
                id,
                content: DocumentContent::Base(base(1, serde_json::json!({ "count": 11 }))),
            }],
            cx,
        )
        .await
        .unwrap();
    assert_eq!(revision_count(&path, id), 1);
    storage
        .commit(
            &[StorageWrite::DocumentChange {
                id,
                content: delta(1, serde_json::json!([["r", { "count": 12 }]])),
            }],
            cx,
        )
        .await
        .unwrap();
    assert_eq!(revision_count(&path, id), 2);
    storage
        .commit(&[StorageWrite::DocumentRetire { id }], cx)
        .await
        .unwrap();
    assert_eq!(revision_count(&path, id), 0);
    storage.close(cx).await.unwrap();
}

#[tokio::test]
async fn auto_checkpoints_wal_frames_and_truncates_the_wal_on_close() {
    let cx = &*BACKGROUND_CONTEXT;
    let Created {
        storage,
        path,
        _directory,
    } = create_sqlite_storage(NativeSqliteStorageOptions {
        wal_autocheckpoint_pages: Some(1),
        busy_timeout_ms: None,
    })
    .await;
    create_root(&storage).await;
    for index in 0..20 {
        let id: EntryId = mint(&storage).await.unwrap();
        storage
            .commit(
                &[StorageWrite::Entry {
                    value: entry(
                        id,
                        ROOT_CONVERSATION_ID,
                        Some(serde_json::json!({ "text": "x".repeat(32 * 1024), "index": index })),
                    ),
                }],
                cx,
            )
            .await
            .unwrap();
    }
    let mut wal_path = path.clone().into_os_string();
    wal_path.push("-wal");
    let wal_path = PathBuf::from(wal_path);
    assert!(std::fs::metadata(&wal_path).unwrap().len() < 512 * 1024);
    let observer = read_only(&path);
    assert_eq!(
        scalar(&observer, "SELECT count(*) AS value FROM entries"),
        20
    );
    storage.close(cx).await.unwrap();
    assert_eq!(std::fs::metadata(&wal_path).unwrap().len(), 0);
    observer.close().unwrap();
}

#[tokio::test]
async fn reuses_pages_released_by_current_only_checkpoints() {
    let cx = &*BACKGROUND_CONTEXT;
    let Created {
        storage,
        path,
        _directory,
    } = create_sqlite_storage(NativeSqliteStorageOptions::default()).await;
    create_root(&storage).await;
    let id: DocumentId = mint(&storage).await.unwrap();
    let large = "x".repeat(512 * 1024);
    storage
        .commit(
            &[StorageWrite::DocumentCreate {
                record: session_document(id, "reuse"),
                content: base(1, serde_json::json!({ "text": large })),
            }],
            cx,
        )
        .await
        .unwrap();
    storage
        .commit(
            &[StorageWrite::DocumentChange {
                id,
                content: DocumentContent::Base(base(1, serde_json::json!({ "text": "small" }))),
            }],
            cx,
        )
        .await
        .unwrap();
    let before = read_only(&path);
    let pages_after_delete = scalar(
        &before,
        "SELECT page_count AS value FROM pragma_page_count() ",
    );
    let free_after_delete = scalar(
        &before,
        "SELECT freelist_count AS value FROM pragma_freelist_count() ",
    );
    before.close().unwrap();
    assert!(free_after_delete > 0);
    storage
        .commit(
            &[StorageWrite::DocumentChange {
                id,
                content: DocumentContent::Base(base(1, serde_json::json!({ "text": large }))),
            }],
            cx,
        )
        .await
        .unwrap();
    let after = read_only(&path);
    let pages_after_reuse = scalar(
        &after,
        "SELECT page_count AS value FROM pragma_page_count() ",
    );
    let free_after_reuse = scalar(
        &after,
        "SELECT freelist_count AS value FROM pragma_freelist_count() ",
    );
    after.close().unwrap();
    assert!(pages_after_reuse <= pages_after_delete + 2);
    assert!(free_after_reuse < free_after_delete);
    storage.close(cx).await.unwrap();
}

#[tokio::test]
async fn keeps_representative_row_and_document_storage_bounded() {
    let cx = &*BACKGROUND_CONTEXT;
    let Created {
        storage,
        path,
        _directory,
    } = create_sqlite_storage(NativeSqliteStorageOptions::default()).await;
    create_root(&storage).await;
    for index in 0..100 {
        let id: EntryId = mint(&storage).await.unwrap();
        storage
            .commit(
                &[StorageWrite::Entry {
                    value: entry(
                        id,
                        ROOT_CONVERSATION_ID,
                        Some(serde_json::json!({ "index": index, "text": "x".repeat(1_024) })),
                    ),
                }],
                cx,
            )
            .await
            .unwrap();
    }
    let document_id: DocumentId = mint(&storage).await.unwrap();
    storage
        .commit(
            &[StorageWrite::DocumentCreate {
                record: rewindable_document(document_id, "size.history"),
                content: base(1, serde_json::json!({ "count": 0 })),
            }],
            cx,
        )
        .await
        .unwrap();
    for count in 1..=100 {
        storage
            .commit(
                &[StorageWrite::DocumentChange {
                    id: document_id,
                    content: delta(1, serde_json::json!([["s", ["count"], count]])),
                }],
                cx,
            )
            .await
            .unwrap();
    }
    storage.close(cx).await.unwrap();
    assert!(std::fs::metadata(&path).unwrap().len() < 1024 * 1024);
}
