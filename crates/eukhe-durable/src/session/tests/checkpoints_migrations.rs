//! Port of `test/session-checkpoints-migrations.test.ts`.
//!
//! Checkpoint predicates and migrations are plain `fn` pointers, so each test
//! records their calls in statics local to the test.

use std::future::Future;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::delta::{Draft, Op};
use eukhe_chord::json::{JsonObject, JsonValue};
use futures::FutureExt;
use serde::{Deserialize, Serialize};

use super::support::{
    assert_error, context, create_conversation, document_changes, fail, flush, json,
    open_test_session, ops_json, Deferred, TestSession,
};
use crate::documents::{
    DocDefinition, DocFamilyDefinition, RewindableConversationDoc, RewindableConversationDocFamily,
    SessionDoc,
};
use crate::errors::StorageError;
use crate::session::{
    ObservedDocumentValue, Ops, Session, SessionError, SessionResult, Tx, WatchListener,
};
use crate::types::{
    ConversationId, ConversationOwnership, DocumentAddress, DocumentBase, DocumentContent,
    DocumentDelta, DocumentPoint, DocumentScope, EntryDraft, EntryId, RewindableFork, Storage,
    StorageWrite,
};

/// Unwrap a `const fn define` result in a static initializer.
macro_rules! defined {
    ($token:expr) => {
        match $token {
            Ok(token) => token,
            Err(_) => panic!("valid definition"),
        }
    };
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// One recorded predicate call: the addresses of the exact value and ops it
/// received (TS keeps the references and checks them with `toBe`).
struct Call {
    value: usize,
    ops: usize,
}

fn record(calls: &Mutex<Vec<Call>>, value: &JsonObject, ops: &[Op]) {
    lock(calls).push(Call {
        value: std::ptr::from_ref(value).addr(),
        ops: ops.as_ptr().addr(),
    });
}

/// TS `documentWrites`: the document writes of one batch.
fn document_writes(writes: &[StorageWrite]) -> Vec<StorageWrite> {
    writes
        .iter()
        .filter(|write| {
            matches!(
                write,
                StorageWrite::DocumentCreate { .. }
                    | StorageWrite::DocumentChange { .. }
                    | StorageWrite::DocumentRetire { .. }
            )
        })
        .cloned()
        .collect()
}

fn content_kind(content: &DocumentContent) -> &'static str {
    match content {
        DocumentContent::Base(_) => "base",
        DocumentContent::Delta(_) => "delta",
    }
}

/// The content kind of a `document.change`, otherwise the write type.
fn write_kind(write: &StorageWrite) -> &'static str {
    match write {
        StorageWrite::DocumentChange { content, .. } => content_kind(content),
        StorageWrite::Conversation { .. } => "conversation",
        StorageWrite::Entry { .. } => "entry",
        StorageWrite::Task { .. } => "task",
        StorageWrite::Submission { .. } => "submission",
        StorageWrite::DocumentCreate { .. } => "document.create",
        StorageWrite::DocumentCopy { .. } => "document.copy",
        StorageWrite::DocumentRetire { .. } => "document.retire",
    }
}

/// Content kinds of every `document.change` in `writes`.
fn change_kinds<'a>(writes: impl IntoIterator<Item = &'a StorageWrite>) -> Vec<&'static str> {
    writes
        .into_iter()
        .filter_map(|write| match write {
            StorageWrite::DocumentChange { content, .. } => Some(content_kind(content)),
            _ => None,
        })
        .collect()
}

#[track_caller]
fn base_of(write: &StorageWrite) -> &DocumentBase {
    match write {
        StorageWrite::DocumentChange {
            content: DocumentContent::Base(base),
            ..
        } => base,
        other => panic!("expected a document.change base, got {other:?}"),
    }
}

#[track_caller]
fn delta_of(write: &StorageWrite) -> &DocumentDelta {
    match write {
        StorageWrite::DocumentChange {
            content: DocumentContent::Delta(delta),
            ..
        } => delta,
        other => panic!("expected a document.change delta, got {other:?}"),
    }
}

fn is_retire(write: &StorageWrite) -> bool {
    matches!(write, StorageWrite::DocumentRetire { .. })
}

/// Build a JSON object from entries.
fn obj<const N: usize>(entries: [(&str, JsonValue); N]) -> JsonValue {
    let mut object = JsonObject::with_capacity(N);
    for (key, value) in entries {
        object.insert(key, value);
    }
    JsonValue::from(object)
}

/// `value[key]`, `null` when absent.
fn field(value: &JsonObject, key: &str) -> JsonValue {
    value.get(key).cloned().unwrap_or(JsonValue::Null)
}

fn as_json(value: &Arc<JsonObject>) -> JsonValue {
    JsonValue::Object(Arc::clone(value))
}

fn observed_json(value: &ObservedDocumentValue) -> JsonValue {
    value.as_ref().map_or(JsonValue::Null, as_json)
}

/// The integer `draft[key]`.
fn draft_integer(draft: &Draft, key: &str) -> SessionResult<i64> {
    let item = draft.get(key)?.expect("field is present");
    Ok(item
        .as_value()
        .and_then(JsonValue::as_i64)
        .expect("integer field"))
}

fn listener(
    deliver: impl Fn(ObservedDocumentValue, Ops) + Send + Sync + 'static,
) -> WatchListener<ObservedDocumentValue> {
    Arc::new(move |value, ops, _cx| {
        deliver(value, ops);
        async { Ok(()) }.boxed()
    })
}

async fn snapshot(session: &Session, token: &SessionDoc<JsonValue>) -> Arc<JsonObject> {
    session
        .snapshot(token, (), context())
        .await
        .unwrap()
        .expect("document exists")
}

async fn snapshot_json(session: &Session, token: &SessionDoc<JsonValue>) -> JsonValue {
    as_json(&snapshot(session, token).await)
}

/// `session.commit((tx) => tx.doc(token).then(() => undefined))`.
async fn acquire(session: &Session, token: &'static SessionDoc<JsonValue>) {
    session
        .commit(
            move |tx| async move {
                tx.doc(token, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
}

/// `(await tx.doc(token)).count++`.
async fn increment(session: &Session, token: &'static SessionDoc<JsonValue>) {
    session
        .commit(
            move |tx| async move {
                let draft = tx.doc(token, ()).await?;
                let count = draft_integer(&draft, "count")?;
                draft.set("count", JsonValue::try_from(count + 1)?)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
}

/// `(await tx.doc(token)).count = count`.
async fn set_count(session: &Session, token: &'static SessionDoc<JsonValue>, count: i32) {
    session
        .commit(
            move |tx| async move {
                tx.doc(token, ()).await?.set("count", count)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
}

// ─── Session document checkpoints ───────────────────────────────────────────

/// TS reads `this.initial()` through the definition receiver; a Rust `fn`
/// predicate has no receiver, so it reads the same definition through its
/// token.
#[tokio::test]
async fn calls_checkpoint_when_with_its_definition_as_the_receiver() {
    static DOC: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "checkpoint.receiver",
        version: 1,
        initial: || json(r#"{"count":0}"#),
        migrate: None,
        checkpoint_when: Some(|value, _ops, _info| {
            let initial = (DOC.definition().initial)();
            value.get("count").and_then(JsonValue::as_i64)
                == initial["count"].as_i64().map(|count| count + 2)
        }),
    }));
    let TestSession {
        session, storage, ..
    } = open_test_session();
    for count in 0..=2 {
        set_count(&session, &DOC, count).await;
    }
    let commits = storage.commits();
    assert_eq!(change_kinds(commits.iter().flatten()), ["delta", "base"]);
}

#[tokio::test]
async fn selects_bases_only_for_nonempty_ordinary_batches_and_passes_the_exact_prepared_revision_and_ops(
) {
    static CALLS: Mutex<Vec<Call>> = Mutex::new(Vec::new());
    static FALSE_CALLS: Mutex<Vec<Call>> = Mutex::new(Vec::new());
    static BASE_DOC: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "checkpoint.base",
        version: 1,
        initial: || json(r#"{"items":[]}"#),
        migrate: None,
        checkpoint_when: Some(|value, ops, _info| {
            record(&CALLS, value, ops);
            true
        }),
    }));
    static DELTA_DOC: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "checkpoint.delta",
        version: 1,
        initial: || json(r#"{"count":0}"#),
        migrate: None,
        checkpoint_when: Some(|value, ops, _info| {
            record(&FALSE_CALLS, value, ops);
            false
        }),
    }));
    static DEFAULT_DOC: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "checkpoint.default",
        version: 1,
        initial: || json(r#"{"count":0}"#),
        migrate: None,
        checkpoint_when: None,
    }));
    let TestSession {
        session,
        storage,
        publications,
    } = open_test_session();

    session
        .commit(
            |tx| async move {
                tx.doc(&BASE_DOC, ()).await?;
                tx.doc(&DELTA_DOC, ()).await?;
                tx.doc(&DEFAULT_DOC, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(lock(&CALLS).len(), 0);
    assert_eq!(lock(&FALSE_CALLS).len(), 0);
    // `document.create` content is always a complete base by type.
    assert!(document_writes(&storage.last_commit())
        .iter()
        .all(|write| matches!(write, StorageWrite::DocumentCreate { .. })));

    session
        .commit(
            |tx| async move {
                tx.doc(&BASE_DOC, ()).await?.child("items")?.push(["x"])?;
                let delta = tx.doc(&DELTA_DOC, ()).await?;
                delta.set(
                    "count",
                    JsonValue::try_from(draft_integer(&delta, "count")? + 1)?,
                )?;
                let default = tx.doc(&DEFAULT_DOC, ()).await?;
                default.set(
                    "count",
                    JsonValue::try_from(draft_integer(&default, "count")? + 1)?,
                )?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    let admitted = storage.admitted_commits().pop().unwrap();
    let writes: Vec<StorageWrite> = admitted
        .into_iter()
        .filter(|write| matches!(write, StorageWrite::DocumentChange { .. }))
        .collect();
    assert_eq!(change_kinds(&writes), ["base", "delta", "delta"]);
    assert_eq!(lock(&CALLS).len(), 1);
    assert_eq!(lock(&FALSE_CALLS).len(), 1);
    let snapshot = snapshot(&session, &BASE_DOC).await;
    let delta_snapshot = session
        .snapshot(&DELTA_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    let changes = document_changes(&publications.last());
    let (published, published_delta) = (&changes[0], &changes[1]);
    let calls = lock(&CALLS);
    let false_calls = lock(&FALSE_CALLS);
    assert_eq!(calls[0].value, Arc::as_ptr(&snapshot).addr());
    assert_eq!(calls[0].ops, published.ops.as_ptr().addr());
    assert_eq!(false_calls[0].value, Arc::as_ptr(&delta_snapshot).addr());
    assert_eq!(false_calls[0].ops, published_delta.ops.as_ptr().addr());
    assert_eq!(delta_of(&writes[1]).ops.as_ptr().addr(), false_calls[0].ops);
    assert!(Arc::ptr_eq(&base_of(&writes[0]).value, &snapshot));
}

#[tokio::test]
async fn passes_the_stored_delta_count_since_the_newest_base_including_after_unload_and_version_bases(
) {
    static SEEN: Mutex<Vec<u64>> = Mutex::new(Vec::new());
    static V1: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "checkpoint.deltas-since-base",
        version: 1,
        initial: || json(r#"{"count":0}"#),
        migrate: None,
        checkpoint_when: Some(|_value, _ops, info| {
            lock(&SEEN).push(info.deltas_since_base);
            info.deltas_since_base >= 2
        }),
    }));
    static V2: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "checkpoint.deltas-since-base",
        version: 2,
        initial: || json(r#"{"count":0}"#),
        migrate: Some(|value, _from| Ok(obj([("count", field(value, "count"))]))),
        checkpoint_when: Some(|_value, _ops, info| {
            lock(&SEEN).push(info.deltas_since_base);
            false
        }),
    }));
    let TestSession {
        session, storage, ..
    } = open_test_session();
    acquire(&session, &V1).await;
    increment(&session, &V1).await;
    increment(&session, &V1).await;
    increment(&session, &V1).await;
    session.unload_documents().await.unwrap();
    increment(&session, &V1).await;
    assert_eq!(*lock(&SEEN), [0, 1, 2, 0]);
    let commits = storage.commits();
    let kinds: Vec<&str> = commits[commits.len() - 4..]
        .iter()
        .map(|writes| write_kind(&writes[0]))
        .collect();
    assert_eq!(kinds, ["delta", "delta", "base", "delta"]);

    // A required version base resets the count without calling the predicate.
    increment(&session, &V2).await;
    increment(&session, &V2).await;
    assert_eq!(*lock(&SEEN), [0, 1, 2, 0, 0]);
    let commits = storage.commits();
    assert_eq!(base_of(&commits[commits.len() - 2][0]).version, 2);
}

#[tokio::test]
async fn skips_the_predicate_for_empty_batches_but_calls_it_for_nonempty_structural_no_ops() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    static DOC: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "checkpoint.no-op",
        version: 1,
        initial: || json(r#"{"items":["a","b"]}"#),
        migrate: None,
        checkpoint_when: Some(|_value, _ops, _info| {
            CALLS.fetch_add(1, Ordering::SeqCst);
            false
        }),
    }));
    let TestSession {
        session, storage, ..
    } = open_test_session();
    acquire(&session, &DOC).await;
    let commits = storage.commit_count();

    session
        .commit(
            |tx| async move {
                let items = tx.doc(&DOC, ()).await?.child("items")?;
                items.push(["x"])?;
                items.pop()?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(CALLS.load(Ordering::SeqCst), 0);
    assert_eq!(storage.commit_count(), commits);

    session
        .commit(
            |tx| async move {
                let items = tx.doc(&DOC, ()).await?.child("items")?;
                let first = items.shift()?.expect("an item");
                items.unshift([first])?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(CALLS.load(Ordering::SeqCst), 1);
    delta_of(&storage.last_commit()[0]);
}

/// TS throws from the second document's predicate. A Rust `CheckpointWhenFn`
/// returns `bool` and cannot fail, and predicates run after every other
/// validation, so the closest failure after checkpoint selection is a Storage
/// failure of the prepared batch. `ControlledStorage` records the offered
/// batch before rejecting it, so `storage.commits` grows by one where TS
/// expects no growth; publications and exact snapshots stay unchanged.
#[tokio::test]
async fn rolls_back_every_prepared_document_when_a_checkpoint_predicate_throws() {
    static FIRST_CALLS: AtomicUsize = AtomicUsize::new(0);
    static FIRST: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "checkpoint.rollback.first",
        version: 1,
        initial: || json(r#"{"count":0}"#),
        migrate: None,
        checkpoint_when: Some(|_value, _ops, _info| {
            FIRST_CALLS.fetch_add(1, Ordering::SeqCst);
            false
        }),
    }));
    static SECOND: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "checkpoint.rollback.second",
        version: 1,
        initial: || json(r#"{"count":0}"#),
        migrate: None,
        checkpoint_when: Some(|_value, _ops, _info| false),
    }));
    let TestSession {
        session,
        storage,
        publications,
    } = open_test_session();
    session
        .commit(
            |tx| async move {
                tx.doc(&FIRST, ()).await?;
                tx.doc(&SECOND, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    let commits = storage.commit_count();
    let published = publications.len();

    storage.fail_next_commit(StorageError::failed(TestFailure("checkpoint failed")));
    let result = session
        .commit(
            |tx| async move {
                tx.doc(&FIRST, ()).await?.set("count", 1)?;
                tx.doc(&SECOND, ()).await?.set("count", 2)?;
                Ok(())
            },
            context(),
        )
        .await;
    assert_error(result, "checkpoint failed");
    flush().await;
    assert_eq!(FIRST_CALLS.load(Ordering::SeqCst), 1);
    assert_eq!(storage.commit_count(), commits + 1);
    assert_eq!(publications.len(), published);
    // A Storage failure now fails the Session (TS `SessionFailed`), so the
    // TS follow-up commit on the same Session has no Rust counterpart.
    assert!(matches!(
        session.snapshot(&FIRST, (), context()).await,
        Err(SessionError::Failed(_))
    ));
}

/// A test failure with a fixed message.
#[derive(Debug, thiserror::Error)]
#[error("{0}")]
struct TestFailure(&'static str);

#[tokio::test]
async fn persists_repeated_false_decisions_as_deltas_and_replays_the_complete_tail() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    static DOC: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "checkpoint.tail",
        version: 1,
        initial: || json(r#"{"values":[]}"#),
        migrate: None,
        checkpoint_when: Some(|_value, _ops, _info| {
            CALLS.fetch_add(1, Ordering::SeqCst);
            false
        }),
    }));
    let TestSession {
        session, storage, ..
    } = open_test_session();
    acquire(&session, &DOC).await;
    for value in 1..=8 {
        session
            .commit(
                move |tx| async move {
                    tx.doc(&DOC, ()).await?.child("values")?.push([value])?;
                    Ok(())
                },
                context(),
            )
            .await
            .unwrap();
    }
    let commits = storage.commits();
    let changes = change_kinds(commits.iter().flatten());
    assert_eq!(changes.len(), 8);
    assert!(changes.iter().all(|kind| *kind == "delta"));
    assert_eq!(CALLS.load(Ordering::SeqCst), 8);
    session.unload_documents().await.unwrap();
    assert_eq!(
        snapshot_json(&session, &DOC).await,
        json(r#"{"values":[1,2,3,4,5,6,7,8]}"#)
    );
}

#[tokio::test]
async fn keeps_a_prepared_root_replacement_as_a_delta_when_the_predicate_is_false() {
    fn initial() -> JsonValue {
        let mut object = JsonObject::with_capacity(4_100);
        for index in 0..4_100 {
            object.insert(format!("field{index}"), JsonValue::from(0));
        }
        JsonValue::from(object)
    }
    static DOC: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "checkpoint.root-replacement",
        version: 1,
        initial,
        migrate: None,
        checkpoint_when: Some(|_value, _ops, _info| false),
    }));
    let TestSession {
        session, storage, ..
    } = open_test_session();
    acquire(&session, &DOC).await;
    session
        .commit(
            |tx| async move {
                let value = tx.doc(&DOC, ()).await?;
                for index in 0..4_100 {
                    value.set(format!("field{index}"), 1)?;
                }
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let write = storage.last_commit().remove(0);
    let delta = delta_of(&write);
    assert_eq!(delta.ops.len(), 1);
    assert!(matches!(delta.ops[0], Op::Replace(_)));
    session.unload_documents().await.unwrap();
    assert_eq!(
        snapshot(&session, &DOC).await.get("field4099"),
        Some(&JsonValue::from(1))
    );
}

#[tokio::test]
async fn uses_ordinary_checkpoint_selection_before_retirement() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    static DOC: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "checkpoint.retire",
        version: 1,
        initial: || json(r#"{"count":0}"#),
        migrate: None,
        checkpoint_when: Some(|_value, _ops, _info| {
            CALLS.fetch_add(1, Ordering::SeqCst);
            true
        }),
    }));
    let TestSession {
        session, storage, ..
    } = open_test_session();
    acquire(&session, &DOC).await;
    session
        .commit(
            |tx| async move {
                tx.doc(&DOC, ()).await?.set("count", 1)?;
                tx.retire_doc(&DOC, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(CALLS.load(Ordering::SeqCst), 1);
    let writes = document_writes(&storage.last_commit());
    assert_eq!(writes.len(), 2);
    base_of(&writes[0]);
    assert!(is_retire(&writes[1]));
}

// ─── Session document migrations ────────────────────────────────────────────

/// TS mutates the object `migrate` returned and checks the snapshot is
/// unaffected. A Rust `migrate` returns an owned value that the Session
/// converts, so the callback can retain no alias; the test checks the value.
#[tokio::test]
async fn migrates_read_only_once_per_cold_load_copies_the_callback_result_and_writes_nothing() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    static FROM_VERSIONS: Mutex<Vec<u64>> = Mutex::new(Vec::new());
    static OLD: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.read-only",
        version: 1,
        initial: || json(r#"{"count":2}"#),
        migrate: None,
        checkpoint_when: None,
    }));
    static CURRENT: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.read-only",
        version: 3,
        initial: || json(r#"{"count":0,"labels":[]}"#),
        migrate: Some(|value, from_version| {
            lock(&FROM_VERSIONS).push(from_version);
            CALLS.fetch_add(1, Ordering::SeqCst);
            Ok(obj([
                ("count", field(value, "count")),
                ("labels", json(r#"["migrated"]"#)),
            ]))
        }),
        checkpoint_when: None,
    }));
    let TestSession {
        session, storage, ..
    } = open_test_session();
    acquire(&session, &OLD).await;
    session.unload_documents().await.unwrap();
    let commits = storage.commit_count();

    let first = snapshot(&session, &CURRENT).await;
    assert!(Arc::ptr_eq(&snapshot(&session, &CURRENT).await, &first));
    assert_eq!(CALLS.load(Ordering::SeqCst), 1);
    assert_eq!(storage.commit_count(), commits);
    assert_eq!(
        as_json(&first),
        json(r#"{"count":2,"labels":["migrated"]}"#)
    );

    session.unload_documents().await.unwrap();
    let second = snapshot(&session, &CURRENT).await;
    assert!(!Arc::ptr_eq(&second, &first));
    assert_eq!(second, first);
    assert_eq!(CALLS.load(Ordering::SeqCst), 2);
    assert_eq!(storage.commit_count(), commits);
    assert_eq!(*lock(&FROM_VERSIONS), [1, 1]);
}

#[tokio::test]
async fn writes_the_required_base_on_the_first_successful_transaction_then_writes_deltas() {
    static CHECKPOINTS: AtomicUsize = AtomicUsize::new(0);
    static OLD: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.transition",
        version: 1,
        initial: || json(r#"{"count":4}"#),
        migrate: None,
        checkpoint_when: None,
    }));
    static CURRENT: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.transition",
        version: 3,
        initial: || json(r#"{"count":0}"#),
        migrate: Some(|value, from_version| {
            let count = value
                .get("count")
                .and_then(JsonValue::as_u64)
                .expect("count");
            Ok(obj([(
                "count",
                JsonValue::try_from(count + from_version - 1)?,
            )]))
        }),
        checkpoint_when: Some(|_value, _ops, _info| {
            CHECKPOINTS.fetch_add(1, Ordering::SeqCst);
            false
        }),
    }));
    let TestSession {
        session,
        storage,
        publications,
    } = open_test_session();
    acquire(&session, &OLD).await;
    session.unload_documents().await.unwrap();
    // An observer of the older shape.
    let watch = session
        .watch_doc(&OLD, (), context())
        .await
        .unwrap()
        .unwrap();
    let frames: Arc<Mutex<Vec<(JsonValue, JsonValue)>>> = Arc::default();
    let sink = Arc::clone(&frames);
    watch
        .start(listener(move |value, ops| {
            lock(&sink).push((observed_json(&value), ops_json(&ops)));
        }))
        .unwrap();
    assert_eq!(
        snapshot_json(&session, &CURRENT).await,
        json(r#"{"count":4}"#)
    );
    let snapshot_value = snapshot(&session, &CURRENT).await;
    // An observer of the new shape: the migration changes nothing it sees.
    let current = session
        .watch_doc(&CURRENT, (), context())
        .await
        .unwrap()
        .unwrap();
    let current_frames: Arc<Mutex<Vec<JsonValue>>> = Arc::default();
    let sink = Arc::clone(&current_frames);
    current
        .start(listener(move |value, _ops| {
            lock(&sink).push(observed_json(&value));
        }))
        .unwrap();

    acquire(&session, &CURRENT).await;
    flush().await;
    let base = base_of(&storage.last_commit()[0]).clone();
    assert_eq!(base.version, 3);
    assert_eq!(as_json(&base.value), json(r#"{"count":4}"#));
    assert_eq!(CHECKPOINTS.load(Ordering::SeqCst), 0);
    // The migration-only base is published, so the older-shape watch receives
    // the new value as a root replacement.
    let changes = document_changes(&publications.last());
    assert_eq!(changes.len(), 1);
    assert_eq!(changes[0].version, Some(3));
    assert_eq!(
        changes[0].value.as_ref().map(as_json),
        Some(json(r#"{"count":4}"#))
    );
    assert!(changes[0].ops.is_empty());
    assert_eq!(
        *lock(&frames),
        [(json(r#"{"count":4}"#), json(r#"[["r",{"count":4}]]"#))]
    );
    assert!(lock(&current_frames).is_empty());
    watch.stop().await;
    current.stop().await;
    assert!(Arc::ptr_eq(
        &snapshot(&session, &CURRENT).await,
        &snapshot_value
    ));

    set_count(&session, &CURRENT, 7).await;
    assert_eq!(delta_of(&storage.last_commit()[0]).version, 3);
    assert_eq!(CHECKPOINTS.load(Ordering::SeqCst), 1);
    session.unload_documents().await.unwrap();
    assert_eq!(
        snapshot_json(&session, &CURRENT).await,
        json(r#"{"count":7}"#)
    );
}

#[tokio::test]
async fn rolls_migration_and_edits_back_with_the_callback_then_coalesces_later_edits_into_one_base()
{
    static MIGRATIONS: AtomicUsize = AtomicUsize::new(0);
    static OLD: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.rollback",
        version: 1,
        initial: || json(r#"{"count":1}"#),
        migrate: None,
        checkpoint_when: None,
    }));
    static CURRENT: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.rollback",
        version: 2,
        initial: || json(r#"{"count":0,"migrated":false}"#),
        migrate: Some(|value, _from| {
            MIGRATIONS.fetch_add(1, Ordering::SeqCst);
            Ok(obj([
                ("count", field(value, "count")),
                ("migrated", JsonValue::from(true)),
            ]))
        }),
        checkpoint_when: None,
    }));
    let TestSession {
        session,
        storage,
        publications,
    } = open_test_session();
    acquire(&session, &OLD).await;
    session.unload_documents().await.unwrap();
    let commits = storage.commit_count();

    let result = session
        .commit(
            |tx| async move {
                tx.doc(&CURRENT, ()).await?.set("count", 8)?;
                fail::<()>("rollback")
            },
            context(),
        )
        .await;
    assert_error(result, "rollback");
    assert_eq!(storage.commit_count(), commits);
    assert_eq!(
        snapshot_json(&session, &CURRENT).await,
        json(r#"{"count":1,"migrated":true}"#)
    );
    assert_eq!(MIGRATIONS.load(Ordering::SeqCst), 1);

    session
        .commit(
            |tx| async move {
                let value = tx.doc(&CURRENT, ()).await?;
                value.set("count", 9)?;
                value.set("migrated", false)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let writes = document_writes(&storage.last_commit());
    assert_eq!(writes.len(), 1);
    let base = base_of(&writes[0]);
    assert_eq!(base.version, 2);
    assert_eq!(
        as_json(&base.value),
        json(r#"{"count":9,"migrated":false}"#)
    );
    flush().await;
    let published = document_changes(&publications.last()).remove(0);
    let admitted = storage.admitted_commits().pop().unwrap().remove(0);
    let published_value = published.value.clone().unwrap();
    assert!(Arc::ptr_eq(
        &published_value,
        &snapshot(&session, &CURRENT).await
    ));
    assert!(Arc::ptr_eq(&published_value, &base_of(&admitted).value));
    assert!(!published.ops.is_empty());
    assert_eq!(MIGRATIONS.load(Ordering::SeqCst), 1);
}

/// TS migrates to `{ invalid: new Date() }`; a Rust migration result is
/// serialized, so the closest non-strict value is a non-finite number.
#[tokio::test]
async fn strict_checks_migration_results_before_tracker_ownership_and_remains_usable_after_rejection(
) {
    #[derive(Serialize, Deserialize)]
    struct InvalidValue {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        invalid: Option<f64>,
    }
    static OLD: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.invalid",
        version: 1,
        initial: || json(r#"{"count":1}"#),
        migrate: None,
        checkpoint_when: None,
    }));
    static INVALID: SessionDoc<InvalidValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.invalid",
        version: 2,
        initial: || InvalidValue { invalid: None },
        migrate: Some(|_value, _from| {
            Ok(InvalidValue {
                invalid: Some(f64::NAN),
            })
        }),
        checkpoint_when: None,
    }));
    static OTHER: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.invalid.other",
        version: 1,
        initial: || json(r#"{"ok":true}"#),
        migrate: None,
        checkpoint_when: None,
    }));
    let TestSession {
        session, storage, ..
    } = open_test_session();
    acquire(&session, &OLD).await;
    session.unload_documents().await.unwrap();
    let commits = storage.commit_count();
    assert_error(
        session.snapshot(&INVALID, (), context()).await,
        "strict JSON",
    );
    assert_error(
        session
            .commit(
                |tx| async move {
                    tx.doc(&INVALID, ()).await?;
                    Ok(())
                },
                context(),
            )
            .await,
        "strict JSON",
    );
    assert_eq!(storage.commit_count(), commits);
    acquire(&session, &OTHER).await;
    assert_eq!(
        snapshot_json(&session, &OTHER).await,
        json(r#"{"ok":true}"#)
    );
}

#[tokio::test]
async fn rejects_newer_stored_versions_and_older_versions_without_migration_for_snapshots_and_transactions(
) {
    static V2: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.compatibility",
        version: 2,
        initial: || json(r#"{"count":2}"#),
        migrate: None,
        checkpoint_when: None,
    }));
    static V1: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.compatibility",
        version: 1,
        initial: || json(r#"{"count":1}"#),
        migrate: None,
        checkpoint_when: None,
    }));
    static V3_WITHOUT_MIGRATION: SessionDoc<JsonValue> =
        defined!(SessionDoc::define(DocDefinition {
            kind: "migration.compatibility",
            version: 3,
            initial: || json(r#"{"count":3}"#),
            migrate: None,
            checkpoint_when: None,
        }));
    async fn acquire_result(
        session: &Session,
        token: &'static SessionDoc<JsonValue>,
    ) -> SessionResult<()> {
        session
            .commit(
                move |tx| async move {
                    tx.doc(token, ()).await?;
                    Ok(())
                },
                context(),
            )
            .await
    }
    let TestSession {
        session, storage, ..
    } = open_test_session();
    acquire(&session, &V2).await;
    session.unload_documents().await.unwrap();
    let commits = storage.commit_count();

    assert_error(
        session.snapshot(&V1, (), context()).await,
        "newer version 2 than 1",
    );
    assert_error(
        acquire_result(&session, &V1).await,
        "newer version 2 than 1",
    );
    assert_error(
        session.snapshot(&V3_WITHOUT_MIGRATION, (), context()).await,
        "requires migration from version 2",
    );
    assert_error(
        acquire_result(&session, &V3_WITHOUT_MIGRATION).await,
        "requires migration from version 2",
    );
    assert_eq!(storage.commit_count(), commits);
}

/// TS throws `must not run` from the predicate; a Rust predicate cannot
/// throw, so it counts its calls and the test expects none.
#[tokio::test]
async fn persists_a_required_migration_base_before_retirement_without_consulting_the_checkpoint_predicate(
) {
    static CHECKPOINTS: AtomicUsize = AtomicUsize::new(0);
    static OLD: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.retire",
        version: 1,
        initial: || json(r#"{"count":1}"#),
        migrate: None,
        checkpoint_when: None,
    }));
    static CURRENT: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.retire",
        version: 2,
        initial: || json(r#"{"count":0}"#),
        migrate: Some(|value, _from| Ok(obj([("count", field(value, "count"))]))),
        checkpoint_when: Some(|_value, _ops, _info| {
            CHECKPOINTS.fetch_add(1, Ordering::SeqCst);
            false
        }),
    }));
    let TestSession {
        session, storage, ..
    } = open_test_session();
    acquire(&session, &OLD).await;
    session.unload_documents().await.unwrap();
    session
        .commit(
            |tx| async move {
                tx.doc(&CURRENT, ()).await?;
                tx.retire_doc(&CURRENT, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let writes = document_writes(&storage.last_commit());
    assert_eq!(writes.len(), 2);
    let base = base_of(&writes[0]);
    assert_eq!(base.version, 2);
    assert_eq!(as_json(&base.value), json(r#"{"count":1}"#));
    assert!(is_retire(&writes[1]));
    assert_eq!(CHECKPOINTS.load(Ordering::SeqCst), 0);
}

#[tokio::test]
async fn leaves_unaccessed_older_documents_and_unavailable_definitions_untouched() {
    static SECOND_MIGRATIONS: AtomicUsize = AtomicUsize::new(0);
    static FIRST_V1: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.lazy.first",
        version: 1,
        initial: || json(r#"{"count":1}"#),
        migrate: None,
        checkpoint_when: None,
    }));
    static SECOND_V1: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.lazy.second",
        version: 1,
        initial: || json(r#"{"count":2}"#),
        migrate: None,
        checkpoint_when: None,
    }));
    static FIRST_V2: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.lazy.first",
        version: 2,
        initial: || json(r#"{"count":0}"#),
        migrate: Some(|value, _from| Ok(obj([("count", field(value, "count"))]))),
        checkpoint_when: None,
    }));
    // Defined but never accessed (TS `defineDoc` without a binding).
    static _SECOND_V2: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
        kind: "migration.lazy.second",
        version: 2,
        initial: || json(r#"{"count":0}"#),
        migrate: Some(|value, _from| {
            SECOND_MIGRATIONS.fetch_add(1, Ordering::SeqCst);
            Ok(obj([("count", field(value, "count"))]))
        }),
        checkpoint_when: None,
    }));
    let TestSession {
        session, storage, ..
    } = open_test_session();
    session
        .commit(
            |tx| async move {
                tx.doc(&FIRST_V1, ()).await?;
                tx.doc(&SECOND_V1, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    session.unload_documents().await.unwrap();
    let commits = storage.commit_count();
    assert_eq!(
        snapshot_json(&session, &FIRST_V2).await,
        json(r#"{"count":1}"#)
    );
    assert_eq!(storage.commit_count(), commits);
    assert_eq!(SECOND_MIGRATIONS.load(Ordering::SeqCst), 0);
    let address = DocumentAddress {
        kind: "migration.lazy.second".to_owned(),
        scope: DocumentScope::Session,
        key: None,
    };
    let second_record = storage
        .find_document(&address, DocumentPoint::Current, context())
        .await
        .unwrap()
        .unwrap();
    let stored = storage
        .document(second_record.id, DocumentPoint::Current, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(stored.version, 1);
}

// ─── Session historical document snapshots ──────────────────────────────────

/// Append an entry of `kind`, run `then` in the same commit, and return the
/// entry ID.
async fn append_with<F, Fut>(
    session: &Session,
    conversation_id: ConversationId,
    kind: &'static str,
    then: F,
) -> EntryId
where
    F: FnOnce(Tx) -> Fut + Send + 'static,
    Fut: Future<Output = SessionResult<()>> + Send + 'static,
{
    session
        .commit(
            move |tx| async move {
                let id = tx
                    .append_entry(conversation_id, EntryDraft::new(kind))
                    .await?
                    .id;
                then(tx).await?;
                Ok(id)
            },
            context(),
        )
        .await
        .unwrap()
}

/// Fork an ownerless child of `parent` at `at` and return its ID.
async fn fork(session: &Session, parent: ConversationId, at: EntryId) -> ConversationId {
    session
        .commit(
            move |tx| async move {
                let child = tx.fork_conversation(parent, at, ConversationOwnership::Ownerless);
                Ok(child.await?.id)
            },
            context(),
        )
        .await
        .unwrap()
}

/// The older shape of `history.migration`; records nothing, so it lives
/// outside the test that uses it.
static HISTORY_V1: RewindableConversationDoc<JsonValue> =
    defined!(RewindableConversationDoc::define(
        DocDefinition {
            kind: "history.migration",
            version: 1,
            initial: || json(r#"{"count":0}"#),
            migrate: None,
            checkpoint_when: None,
        },
        RewindableFork::AsOf,
    ));

static HISTORY_FAMILY: RewindableConversationDocFamily<JsonValue, String> =
    defined!(RewindableConversationDocFamily::define(
        DocFamilyDefinition {
            kind: "history.family",
            version: 1,
            initial: |seed: String| obj([("seed", seed.into()), ("count", 0.into())]),
            migrate: None,
            checkpoint_when: None,
        },
        RewindableFork::AsOf,
    ));

#[tokio::test]
async fn migrates_current_and_historical_rewindable_values_independently_and_follows_fork_ancestry()
{
    static MIGRATIONS: Mutex<Vec<u64>> = Mutex::new(Vec::new());
    static V3: RewindableConversationDoc<JsonValue> = defined!(RewindableConversationDoc::define(
        DocDefinition {
            kind: "history.migration",
            version: 3,
            initial: || json(r#"{"count":0,"version":3}"#),
            migrate: Some(|value, from_version| {
                lock(&MIGRATIONS).push(from_version);
                Ok(obj([
                    ("count", field(value, "count")),
                    ("version", 3.into()),
                ]))
            }),
            checkpoint_when: None,
        },
        RewindableFork::AsOf,
    ));
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let conversation_id = create_conversation(&session).await;
    let first_entry = append_with(&session, conversation_id, "first", move |tx| async move {
        tx.doc(&HISTORY_V1, conversation_id)
            .await?
            .set("count", 1)?;
        tx.doc_member(
            &HISTORY_FAMILY,
            (conversation_id, "member"),
            &"seed".to_owned(),
        )
        .await?
        .set("count", 1)?;
        Ok(())
    })
    .await;
    let second_entry = append_with(&session, conversation_id, "second", move |tx| async move {
        tx.doc(&HISTORY_V1, conversation_id)
            .await?
            .set("count", 2)?;
        Ok(())
    })
    .await;
    session.unload_documents().await.unwrap();
    let commits = storage.commit_count();
    let current = session
        .snapshot(&V3, conversation_id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(as_json(&current), json(r#"{"count":2,"version":3}"#));
    assert_eq!(*lock(&MIGRATIONS), [1]);
    assert_eq!(storage.commit_count(), commits);

    let third_entry = append_with(&session, conversation_id, "third", move |tx| async move {
        tx.doc(&V3, conversation_id).await?;
        Ok(())
    })
    .await;
    assert!(storage.last_commit().iter().any(|write| matches!(
        write,
        StorageWrite::DocumentChange {
            content: DocumentContent::Base(base),
            ..
        } if base.version == 3
    )));

    let as_of = |conversation_id, at| {
        let read = session.snapshot_as_of(&V3, conversation_id, at, context());
        async move { read.await.map(|value| value.as_ref().map(as_json)) }
    };
    let family_as_of = |conversation_id, at| {
        let read =
            session.snapshot_as_of(&HISTORY_FAMILY, (conversation_id, "member"), at, context());
        async move { read.await.unwrap().as_ref().map(as_json) }
    };
    let (one, two) = (
        Some(json(r#"{"count":1,"version":3}"#)),
        Some(json(r#"{"count":2,"version":3}"#)),
    );
    let member = Some(json(r#"{"seed":"seed","count":1}"#));
    assert_eq!(as_of(conversation_id, first_entry).await.unwrap(), one);
    assert_eq!(as_of(conversation_id, second_entry).await.unwrap(), two);
    assert_eq!(as_of(conversation_id, third_entry).await.unwrap(), two);
    assert_eq!(*lock(&MIGRATIONS), [1, 1, 1]);
    assert_eq!(family_as_of(conversation_id, first_entry).await, member);

    let child_id = fork(&session, conversation_id, second_entry).await;
    assert_eq!(as_of(child_id, first_entry).await.unwrap(), one);
    assert_eq!(as_of(child_id, second_entry).await.unwrap(), two);
    assert_eq!(family_as_of(child_id, first_entry).await, member);
    assert_error(
        as_of(child_id, third_entry).await,
        &format!("Entry {third_entry} is not visible"),
    );
}

#[tokio::test]
async fn selects_the_incarnation_alive_at_the_entry_commit_across_retirement_and_recreation() {
    static DOC: RewindableConversationDoc<JsonValue> = defined!(RewindableConversationDoc::define(
        DocDefinition {
            kind: "history.incarnation",
            version: 1,
            initial: || json(r#"{"value":"initial"}"#),
            migrate: None,
            checkpoint_when: None,
        },
        RewindableFork::AsOf,
    ));
    let TestSession { session, .. } = open_test_session();
    let conversation_id = create_conversation(&session).await;
    let before_creation =
        append_with(&session, conversation_id, "before", |_tx| async { Ok(()) }).await;
    let created_at = append_with(&session, conversation_id, "create", move |tx| async move {
        tx.doc(&DOC, conversation_id).await?.set("value", "old")?;
        Ok(())
    })
    .await;
    let retired_at = append_with(&session, conversation_id, "retire", move |tx| async move {
        tx.retire_doc(&DOC, conversation_id).await
    })
    .await;
    let recreated_at = append_with(
        &session,
        conversation_id,
        "recreate",
        move |tx| async move {
            tx.doc(&DOC, conversation_id).await?.set("value", "new")?;
            Ok(())
        },
    )
    .await;

    let as_of = |at| {
        let read = session.snapshot_as_of(&DOC, conversation_id, at, context());
        async move { read.await.map(|value| value.as_ref().map(as_json)) }
    };
    assert_eq!(as_of(before_creation).await.unwrap(), None);
    assert_eq!(
        as_of(created_at).await.unwrap(),
        Some(json(r#"{"value":"old"}"#))
    );
    assert_eq!(as_of(retired_at).await.unwrap(), None);
    assert_eq!(
        as_of(recreated_at).await.unwrap(),
        Some(json(r#"{"value":"new"}"#))
    );
    session.close(context()).await.unwrap();
    assert_error(as_of(recreated_at).await, "closed");
}

// ─── Session tracker cache across definition versions ───────────────────────

static CACHE_V1: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
    kind: "cache.versioned",
    version: 1,
    initial: || json(r#"{"name":"first"}"#),
    migrate: None,
    checkpoint_when: None,
}));

static CACHE_V2: SessionDoc<JsonValue> = defined!(SessionDoc::define(DocDefinition {
    kind: "cache.versioned",
    version: 2,
    initial: || json(r#"{"names":[]}"#),
    migrate: Some(|value, _from| Ok(obj([("names", vec![field(value, "name")].into())]))),
    checkpoint_when: None,
}));

/// `(await tx.doc(V2Doc)).names.push("second")`.
async fn push_second_name(session: &Session) {
    session
        .commit(
            |tx| async move {
                tx.doc(&CACHE_V2, ())
                    .await?
                    .child("names")?
                    .push(["second"])?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
}

#[tokio::test]
async fn migrates_a_document_cached_by_an_older_token_without_unloading() {
    let TestSession {
        session, storage, ..
    } = open_test_session();
    acquire(&session, &CACHE_V1).await;
    assert_eq!(
        snapshot_json(&session, &CACHE_V1).await,
        json(r#"{"name":"first"}"#)
    );

    // Reloaded extension code accesses the still-cached document with a newer token.
    assert_eq!(
        snapshot_json(&session, &CACHE_V2).await,
        json(r#"{"names":["first"]}"#)
    );
    push_second_name(&session).await;
    let write = document_writes(&storage.last_commit()).remove(0);
    let base = base_of(&write);
    assert_eq!(base.version, 2);
    assert_eq!(
        as_json(&base.value),
        json(r#"{"names":["first","second"]}"#)
    );
    assert_error(
        session.snapshot(&CACHE_V1, (), context()).await,
        "newer version 2",
    );
}

#[tokio::test]
async fn sends_observers_of_an_older_shape_a_root_replacement_after_a_newer_token_writes() {
    let TestSession { session, .. } = open_test_session();
    acquire(&session, &CACHE_V1).await;
    let state = session
        .document_state(&CACHE_V1, (), context())
        .await
        .unwrap()
        .unwrap();
    let watch = session
        .watch_doc(&CACHE_V1, (), context())
        .await
        .unwrap()
        .unwrap();
    let frames: Arc<Mutex<Vec<JsonValue>>> = Arc::default();
    let delivered = Deferred::new();
    let (sink, signal) = (Arc::clone(&frames), delivered.clone());
    watch
        .start(listener(move |_value, ops| {
            lock(&sink).push(ops_json(&ops));
            signal.resolve();
        }))
        .unwrap();
    push_second_name(&session).await;
    delivered.wait().await;
    assert_eq!(state.value(), json(r#"{"names":["first","second"]}"#));
    assert_eq!(
        observed_json(&watch.value()),
        json(r#"{"names":["first","second"]}"#)
    );
    assert_eq!(
        *lock(&frames),
        [json(r#"[["r",{"names":["first","second"]}]]"#)]
    );
    state.dispose().unwrap();
    watch.stop().await;
}

#[tokio::test]
async fn serves_an_older_token_from_storage_after_a_newer_token_migrated_only_in_memory() {
    let TestSession { session, .. } = open_test_session();
    acquire(&session, &CACHE_V1).await;
    session.unload_documents().await.unwrap();
    assert_eq!(
        snapshot_json(&session, &CACHE_V2).await,
        json(r#"{"names":["first"]}"#)
    );
    assert_eq!(
        snapshot_json(&session, &CACHE_V1).await,
        json(r#"{"name":"first"}"#)
    );
    session
        .commit(
            |tx| async move {
                tx.doc(&CACHE_V1, ()).await?.set("name", "renamed")?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(
        snapshot_json(&session, &CACHE_V2).await,
        json(r#"{"names":["renamed"]}"#)
    );
}
