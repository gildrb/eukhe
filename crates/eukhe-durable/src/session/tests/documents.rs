//! Port of `test/session-documents.test.ts`.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{create_context_key, with_context_value, Context};
use eukhe_chord::delta::{Draft, Op};
use eukhe_chord::json::{JsonObject, JsonValue};
use serde::{Deserialize, Serialize};

use super::support::{
    assert_error, child, context, create_conversation, document_changes, flush, json,
    open_test_session, TestSession,
};
use crate::documents::{
    ConversationDoc, DocDefinition, DocFamilyDefinition, RewindableConversationDoc, SessionDoc,
    SessionDocFamily,
};
use crate::errors::StorageError;
use crate::session::{SessionError, SessionResult, TransactionScope, Tx, TxFuture};
use crate::types::{
    AnyTaskRecord, ConversationId, DocumentAddress, DocumentContent, DocumentPoint, DocumentScope,
    LatestFork, RewindableFork, Storage, StorageWrite,
};

fn live_initial() -> JsonValue {
    json(r#"{"items":[],"nested":{"count":0},"other":{"label":"x"}}"#)
}

const LIVE_DOC: ConversationDoc<JsonValue> = match ConversationDoc::define(
    DocDefinition {
        kind: "test.live",
        version: 1,
        initial: live_initial,
        migrate: None,
        checkpoint_when: None,
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

const REWINDABLE_LIVE_DOC: RewindableConversationDoc<JsonValue> =
    match RewindableConversationDoc::define(
        DocDefinition {
            kind: "test.live",
            version: 1,
            initial: live_initial,
            migrate: None,
            checkpoint_when: None,
        },
        RewindableFork::AsOf,
    ) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };

const LIVE_DOC_V2: ConversationDoc<JsonValue> = match ConversationDoc::define(
    DocDefinition {
        kind: "test.live",
        version: 2,
        initial: live_initial,
        migrate: None,
        checkpoint_when: None,
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

const COUNTER_DOC: SessionDoc<JsonValue> = match SessionDoc::define(DocDefinition {
    kind: "test.counter",
    version: 1,
    initial: || json(r#"{"count":0}"#),
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

fn member(seed: &str) -> JsonValue {
    json(&format!(
        r#"{{"seed":{},"hits":0}}"#,
        serde_json::to_string(seed).expect("string serializes")
    ))
}

const MEMBER_DOC: SessionDocFamily<JsonValue, String> =
    match SessionDocFamily::define(DocFamilyDefinition {
        kind: "test.member",
        version: 1,
        initial: |seed: String| member(&seed),
        migrate: None,
        checkpoint_when: None,
    }) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };

/// `snapshot[key]`, `None` when absent (TS `undefined`).
fn field(snapshot: &Arc<JsonObject>, key: &str) -> Option<JsonValue> {
    JsonValue::Object(Arc::clone(snapshot)).get(key).cloned()
}

fn message(snapshot: &Arc<JsonObject>) -> Option<JsonValue> {
    field(snapshot, "message")
}

/// The `serde_json` form of a persisted record or write.
fn to_serde(value: &impl Serialize) -> serde_json::Value {
    serde_json::to_value(value).expect("records serialize")
}

/// Vitest `toMatchObject`: objects match by subset, arrays element-wise.
fn matches(actual: &serde_json::Value, expected: &serde_json::Value) -> bool {
    match (actual, expected) {
        (serde_json::Value::Object(actual), serde_json::Value::Object(expected)) => {
            expected.iter().all(|(key, expected)| {
                actual
                    .get(key)
                    .is_some_and(|actual| matches(actual, expected))
            })
        }
        (serde_json::Value::Array(actual), serde_json::Value::Array(expected)) => {
            actual.len() == expected.len()
                && actual
                    .iter()
                    .zip(expected)
                    .all(|(actual, expected)| matches(actual, expected))
        }
        _ => actual == expected,
    }
}

#[track_caller]
fn assert_matches(actual: &impl Serialize, expected: &serde_json::Value) {
    let actual = to_serde(actual);
    assert!(
        matches(&actual, expected),
        "{actual} does not match {expected}"
    );
}

fn write_type(write: &StorageWrite) -> String {
    to_serde(write)["type"]
        .as_str()
        .expect("writes are tagged")
        .to_owned()
}

fn count_type(writes: &[StorageWrite], kind: &str) -> usize {
    writes
        .iter()
        .filter(|write| write_type(write) == kind)
        .count()
}

/// `expect.objectContaining({ type: "document.create", record: { kind: "test.live" } })`.
fn has_live_create(writes: &[StorageWrite]) -> bool {
    writes.iter().any(|write| {
        matches(
            &to_serde(write),
            &serde_json::json!({ "type": "document.create", "record": { "kind": "test.live" } }),
        )
    })
}

fn has_retire(writes: &[StorageWrite], id: crate::types::DocumentId) -> bool {
    writes.iter().any(
        |write| matches!(write, StorageWrite::DocumentRetire { id: retired } if *retired == id),
    )
}

/// Increment the numeric `draft[key]`.
fn increment(draft: &Draft, key: &str) -> SessionResult<()> {
    let current = draft
        .get(key)?
        .and_then(|item| item.as_value().and_then(JsonValue::as_f64))
        .expect("a numeric field");
    draft.set(key, JsonValue::try_from(current + 1.0).expect("finite"))?;
    Ok(())
}

async fn snapshot_live(test: &TestSession, conversation_id: ConversationId) -> Arc<JsonObject> {
    test.session
        .snapshot(&LIVE_DOC, conversation_id, context())
        .await
        .unwrap()
        .expect("the live document exists")
}

async fn set_live_message(test: &TestSession, conversation_id: ConversationId, value: &str) {
    let value = value.to_owned();
    test.session
        .commit(
            move |tx| async move {
                tx.doc(&LIVE_DOC, conversation_id)
                    .await?
                    .set("message", value.as_str())?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
}

async fn setup_live() -> (TestSession, ConversationId) {
    let test = open_test_session();
    let conversation_id = create_conversation(&test.session).await;
    test.session
        .commit(
            move |tx| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                child(&live, "items").push(["a", "b"])?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    (test, conversation_id)
}

/// A captured Tx operation the test awaits after the callback settled.
type Pending = Arc<Mutex<Option<TxFuture<Draft>>>>;

fn take_pending(pending: &Pending) -> TxFuture<Draft> {
    pending
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .expect("the callback started an acquisition")
}

#[tokio::test]
async fn creates_an_initial_base_on_first_access_and_adopts_it_after_storage_success() {
    let test = open_test_session();
    let conversation_id = create_conversation(&test.session).await;
    set_live_message(&test, conversation_id, "hello").await;
    let writes = test.storage.last_commit();
    assert_eq!(writes.len(), 1);
    assert_matches(
        &writes[0],
        &serde_json::json!({
            "type": "document.create",
            "record": {
                "kind": "test.live",
                "scope": { "kind": "conversation", "conversationId": to_serde(&conversation_id) },
                "history": "latest",
                "fork": "initial",
            },
            "content": { "kind": "base", "version": 1, "value": { "message": "hello", "items": [], "nested": { "count": 0 } } },
        }),
    );
    let snapshot = snapshot_live(&test, conversation_id).await;
    assert_eq!(
        JsonValue::Object(Arc::clone(&snapshot)),
        json(r#"{"message":"hello","items":[],"nested":{"count":0},"other":{"label":"x"}}"#)
    );
    flush().await;
    let publication = test.publications.last();
    let published = document_changes(&publication).remove(0);
    assert_eq!(published.record.created_at, publication.seq);
    let value = published.value.clone().unwrap();
    assert!(Arc::ptr_eq(&value, &snapshot));
    assert_eq!(published.conversation_id, Some(conversation_id));
    let admitted = test.storage.admitted_commits().pop().unwrap();
    let create = admitted
        .iter()
        .find_map(|write| match write {
            StorageWrite::DocumentCreate { content, .. } => Some(content),
            _ => None,
        })
        .unwrap();
    assert!(Arc::ptr_eq(&create.value, &value));
}

#[tokio::test]
async fn never_creates_on_snapshot_and_returns_undefined_when_absent() {
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let conversation_id = create_conversation(&session).await;
    let before = storage.commit_count();
    assert!(session
        .snapshot(&LIVE_DOC, conversation_id, context())
        .await
        .unwrap()
        .is_none());
    assert!(session
        .snapshot(&COUNTER_DOC, (), context())
        .await
        .unwrap()
        .is_none());
    assert!(session
        .snapshot(&MEMBER_DOC, "k", context())
        .await
        .unwrap()
        .is_none());
    assert_eq!(storage.commit_count(), before);
    assert_eq!(storage.mint_count(), 1);
}

#[tokio::test]
async fn returns_shared_immutable_snapshots_and_keeps_prior_revisions_stable() {
    let (test, conversation_id) = setup_live().await;
    let first = snapshot_live(&test, conversation_id).await;
    assert!(Arc::ptr_eq(
        &snapshot_live(&test, conversation_id).await,
        &first
    ));
    test.session
        .commit(
            move |tx| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                child(&live, "nested").set("count", 1)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let second = snapshot_live(&test, conversation_id).await;
    assert!(!Arc::ptr_eq(&second, &first));
    assert_eq!(field(&first, "nested"), Some(json(r#"{"count":0}"#)));
    assert_eq!(field(&second, "nested"), Some(json(r#"{"count":1}"#)));
    // Unchanged subtrees are structurally shared between immutable revisions.
    assert!(field(&second, "items")
        .unwrap()
        .strict_equals(&field(&first, "items").unwrap()));
    assert!(field(&second, "other")
        .unwrap()
        .strict_equals(&field(&first, "other").unwrap()));
}

#[tokio::test]
async fn adopts_by_pointer_swap_and_shares_operation_payloads_with_the_published_revision() {
    let (test, conversation_id) = setup_live().await;
    test.session
        .commit(
            move |tx| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                live.set("other", json(r#"{"label":"y"}"#))?;
                child(&live, "items").push(["c"])?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    let snapshot = snapshot_live(&test, conversation_id).await;
    let published = document_changes(&test.publications.last()).remove(0);
    assert!(Arc::ptr_eq(published.value.as_ref().unwrap(), &snapshot));
    let admitted = test.storage.admitted_commits().pop().unwrap();
    let content = admitted
        .iter()
        .find_map(|write| match write {
            StorageWrite::DocumentChange { content, .. } => Some(content.clone()),
            _ => None,
        })
        .unwrap();
    let DocumentContent::Delta(delta) = content else {
        panic!("Expected delta");
    };
    assert!(Arc::ptr_eq(&published.ops, &delta.ops));
    let set = published
        .ops
        .iter()
        .find(|op| matches!(op, Op::Set(..)))
        .unwrap();
    assert_eq!(set.to_json(), json(r#"["s",["other"],{"label":"y"}]"#));
    // Trusted immutability: the Session makes no second copy of operation payloads.
    let Op::Set(_, payload) = set else {
        unreachable!("found a set op")
    };
    assert!(payload.strict_equals(&field(&snapshot, "other").unwrap()));
}

/// TS checks that each placement copies the mutable source object
/// (`not.toBe`). Rust values are immutable, so a shared placement can never
/// observe a later mutation; the observable contract is the stored values.
#[tokio::test]
async fn copies_assigned_values_per_placement() {
    let (test, conversation_id) = setup_live().await;
    test.session
        .commit(
            move |tx| async move {
                let value = json(r#"{"label":"shared"}"#);
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                live.set("other", value.clone())?;
                live.set("copy", value)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let snapshot = snapshot_live(&test, conversation_id).await;
    assert_eq!(
        field(&snapshot, "other"),
        Some(json(r#"{"label":"shared"}"#))
    );
    assert_eq!(
        field(&snapshot, "copy"),
        Some(json(r#"{"label":"shared"}"#))
    );
}

#[tokio::test]
async fn suppresses_writes_and_publications_for_empty_batches() {
    let (test, conversation_id) = setup_live().await;
    flush().await;
    let commits = test.storage.commit_count();
    let published = test.publications.len();
    test.session
        .commit(
            move |tx| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                child(&live, "nested").set("count", 0)?;
                let items = child(&live, "items");
                items.push(["z"])?;
                items.pop()?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    assert_eq!(test.storage.commit_count(), commits);
    assert_eq!(test.publications.len(), published);
}

#[tokio::test]
async fn writes_and_publishes_replayable_nonempty_structural_no_ops() {
    let (test, conversation_id) = setup_live().await;
    let before = snapshot_live(&test, conversation_id).await;
    test.session
        .commit(
            move |tx| async move {
                let items = child(&tx.doc(&LIVE_DOC, conversation_id).await?, "items");
                let first = items.shift()?.unwrap();
                items.unshift([first])?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    let writes = test.storage.last_commit();
    assert_matches(
        &writes[0],
        &serde_json::json!({ "type": "document.change", "content": { "kind": "delta" } }),
    );
    let after = snapshot_live(&test, conversation_id).await;
    assert_eq!(after, before);
    assert!(!Arc::ptr_eq(&after, &before));
    assert!(!document_changes(&test.publications.last())[0]
        .ops
        .is_empty());
}

#[tokio::test]
async fn revokes_escaped_drafts_when_the_callback_settles() {
    let (test, conversation_id) = setup_live().await;
    let (escaped, items) = test
        .session
        .commit(
            move |tx| async move {
                let escaped = tx.doc(&LIVE_DOC, conversation_id).await?;
                let items = child(&escaped, "items");
                escaped.set("message", "inside")?;
                Ok((escaped, items))
            },
            context(),
        )
        .await
        .unwrap();
    assert!(escaped.get("message").is_err());
    assert!(escaped.set("message", "outside").is_err());
    assert!(items.len().is_err());
    assert!(items.push(["outside"]).is_err());
    assert_eq!(
        message(&snapshot_live(&test, conversation_id).await),
        Some(json(r#""inside""#))
    );

    let returned = test
        .session
        .commit(
            move |tx| async move { tx.doc(&LIVE_DOC, conversation_id).await },
            context(),
        )
        .await
        .unwrap();
    assert!(returned.get("message").is_err());
}

#[tokio::test]
async fn aborts_every_change_when_the_callback_fails() {
    let (test, conversation_id) = setup_live().await;
    let before = snapshot_live(&test, conversation_id).await;
    let commits = test.storage.commit_count();
    assert_error(
        test.session
            .commit(
                move |tx| async move {
                    let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                    let counter = tx.doc(&COUNTER_DOC, ()).await?;
                    live.set("message", "lost")?;
                    counter.set("count", 5)?;
                    super::support::fail::<()>("callback failed")
                },
                context(),
            )
            .await,
        "callback failed",
    );
    assert_eq!(test.storage.commit_count(), commits);
    assert!(Arc::ptr_eq(
        &snapshot_live(&test, conversation_id).await,
        &before
    ));
    assert!(test
        .session
        .snapshot(&COUNTER_DOC, (), context())
        .await
        .unwrap()
        .is_none());
    set_live_message(&test, conversation_id, "kept").await;
    assert_eq!(
        message(&snapshot_live(&test, conversation_id).await),
        Some(json(r#""kept""#))
    );
}

/// `liveInitCount` is module state in TS; Rust tests run in parallel, so this
/// test counts initializations of its own `test.live` token.
#[tokio::test]
async fn memoizes_concurrent_duplicate_acquisition_and_initializes_once() {
    static LIVE_INIT_COUNT: AtomicUsize = AtomicUsize::new(0);
    const COUNTED_LIVE_DOC: ConversationDoc<JsonValue> = match ConversationDoc::define(
        DocDefinition {
            kind: "test.live",
            version: 1,
            initial: || {
                LIVE_INIT_COUNT.fetch_add(1, Ordering::SeqCst);
                live_initial()
            },
            migrate: None,
            checkpoint_when: None,
        },
        LatestFork::Initial,
    ) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let conversation_id = create_conversation(&session).await;
    let init_count = LIVE_INIT_COUNT.load(Ordering::SeqCst);
    let mints = storage.mint_count();
    session
        .commit(
            move |tx| async move {
                let (first, second) = futures::join!(
                    tx.doc(&COUNTED_LIVE_DOC, conversation_id),
                    tx.doc(&COUNTED_LIVE_DOC, conversation_id)
                );
                let (first, second) = (first?, second?);
                assert_eq!(first, second);
                assert_eq!(tx.doc(&COUNTED_LIVE_DOC, conversation_id).await?, first);
                first.set("message", "once")?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(LIVE_INIT_COUNT.load(Ordering::SeqCst), init_count + 1);
    assert_eq!(storage.mint_count(), mints + 1);
    assert_eq!(count_type(&storage.last_commit(), "document.create"), 1);
}

/// `seeds` is module state in TS; this test records seeds of its own
/// `test.member` token so parallel Rust tests cannot interleave.
#[tokio::test]
async fn uses_the_first_family_seed_and_ignores_seeds_for_existing_members() {
    static SEEDS: Mutex<Vec<String>> = Mutex::new(Vec::new());
    const SEEDED_MEMBER_DOC: SessionDocFamily<JsonValue, String> =
        match SessionDocFamily::define(DocFamilyDefinition {
            kind: "test.member",
            version: 1,
            initial: |seed: String| {
                let value = member(&seed);
                SEEDS
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(seed);
                value
            },
            migrate: None,
            checkpoint_when: None,
        }) {
            Ok(token) => token,
            Err(_) => panic!("valid definition"),
        };
    let TestSession { session, .. } = open_test_session();
    SEEDS.lock().unwrap_or_else(PoisonError::into_inner).clear();
    session
        .commit(
            |tx| async move {
                let first = tx
                    .doc_member(&SEEDED_MEMBER_DOC, "k", &"first".to_owned())
                    .await?;
                let second = tx
                    .doc_member(&SEEDED_MEMBER_DOC, "k", &"second".to_owned())
                    .await?;
                assert_eq!(second, first);
                increment(&first, "hits")
            },
            context(),
        )
        .await
        .unwrap();
    session
        .commit(
            |tx| async move {
                increment(
                    &tx.doc_member(&SEEDED_MEMBER_DOC, "k", &"third".to_owned())
                        .await?,
                    "hits",
                )?;
                increment(
                    &tx.doc_member(&SEEDED_MEMBER_DOC, "other", &"fourth".to_owned())
                        .await?,
                    "hits",
                )
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(
        *SEEDS.lock().unwrap_or_else(PoisonError::into_inner),
        vec!["first".to_owned(), "fourth".to_owned()]
    );
    assert_eq!(
        session
            .snapshot(&SEEDED_MEMBER_DOC, "k", context())
            .await
            .unwrap()
            .map(JsonValue::Object),
        Some(json(r#"{"seed":"first","hits":2}"#))
    );
    assert_eq!(
        session
            .snapshot(&SEEDED_MEMBER_DOC, "other", context())
            .await
            .unwrap()
            .map(JsonValue::Object),
        Some(json(r#"{"seed":"fourth","hits":1}"#))
    );
}

#[tokio::test]
async fn rejects_a_callback_that_succeeds_with_a_pending_acquisition_and_drains_it() {
    let (test, conversation_id) = setup_live().await;
    test.session.unload_documents().await.unwrap();
    let gate = test.storage.hold_find_document();
    let commits = test.storage.commit_count();
    let pending: Pending = Arc::default();
    let slot = Arc::clone(&pending);
    let commit = tokio::spawn(test.session.commit(
        move |tx| {
            *slot.lock().unwrap_or_else(PoisonError::into_inner) =
                Some(tx.doc(&LIVE_DOC, conversation_id));
            async { Ok(()) }
        },
        context(),
    ));
    gate.entered().await;
    flush().await;
    // The line stays held until the late acquisition settles.
    assert!(!commit.is_finished());
    gate.release();
    assert_error(commit.await.unwrap(), "pending Tx operations");
    assert_error(take_pending(&pending).await, "Transaction has settled");
    assert_eq!(test.storage.commit_count(), commits);
    set_live_message(&test, conversation_id, "after").await;
    assert_eq!(
        message(&snapshot_live(&test, conversation_id).await),
        Some(json(r#""after""#))
    );
}

#[tokio::test]
async fn does_not_initialize_or_mint_for_an_absent_acquisition_that_finishes_after_settlement() {
    static INITIALIZED: AtomicUsize = AtomicUsize::new(0);
    const LATE_DOC: SessionDoc<JsonValue> = match SessionDoc::define(DocDefinition {
        kind: "test.late",
        version: 1,
        initial: || {
            INITIALIZED.fetch_add(1, Ordering::SeqCst);
            json(r#"{"count":0}"#)
        },
        migrate: None,
        checkpoint_when: None,
    }) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let gate = storage.hold_find_document();
    let mints = storage.mint_count();
    let pending: Pending = Arc::default();
    let slot = Arc::clone(&pending);
    let commit = tokio::spawn(session.commit(
        move |tx| {
            *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(tx.doc(&LATE_DOC, ()));
            async { Ok(()) }
        },
        context(),
    ));
    gate.entered().await;
    gate.release();
    assert_error(commit.await.unwrap(), "pending Tx operations");
    assert_error(take_pending(&pending).await, "Transaction has settled");
    assert_eq!(INITIALIZED.load(Ordering::SeqCst), 0);
    assert_eq!(storage.mint_count(), mints);
}

#[tokio::test]
async fn rejects_with_the_callback_error_when_it_fails_with_a_pending_acquisition() {
    let (test, conversation_id) = setup_live().await;
    test.session.unload_documents().await.unwrap();
    let gate = test.storage.hold_find_document();
    let pending: Pending = Arc::default();
    let slot = Arc::clone(&pending);
    let commit = tokio::spawn(test.session.commit(
        move |tx| {
            *slot.lock().unwrap_or_else(PoisonError::into_inner) =
                Some(tx.doc(&LIVE_DOC, conversation_id));
            async { super::support::fail::<()>("callback failed") }
        },
        context(),
    ));
    gate.entered().await;
    gate.release();
    assert_error(commit.await.unwrap(), "callback failed");
    assert_error(take_pending(&pending).await, "Transaction has settled");
}

fn missing_task(conversation_id: ConversationId) -> AnyTaskRecord {
    serde_json::from_value(serde_json::json!({
        "id": 999,
        "conversationId": to_serde(&conversation_id),
        "kind": "missing",
        "version": 1,
        "input": null,
        "background": false,
        "abortRequested": false,
        "state": { "status": "pending", "checkpoint": { "phase": "start" } },
    }))
    .expect("a valid task record")
}

/// TS passes `{} as never` to `setTask`; Rust needs a well-typed record.
#[tokio::test]
async fn rejects_tx_use_after_the_callback_settles() {
    let (test, conversation_id) = setup_live().await;
    let captured: Arc<Mutex<Option<Tx>>> = Arc::default();
    let slot = Arc::clone(&captured);
    test.session
        .commit_with(
            move |tx| {
                *slot.lock().unwrap_or_else(PoisonError::into_inner) = Some(tx);
                async { Ok(()) }
            },
            context(),
            TransactionScope::default(),
        )
        .await
        .unwrap();
    let captured = captured
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .take()
        .unwrap();
    assert_error(
        captured.doc(&LIVE_DOC, conversation_id).await,
        "Transaction has settled",
    );
    assert_error(
        captured.conversation(conversation_id).await,
        "Transaction has settled",
    );
    assert_error(
        captured.set_task(missing_task(conversation_id)),
        "Transaction has settled",
    );
}

#[tokio::test]
async fn rejects_tokens_whose_semantics_or_version_disagree_with_the_stored_incarnation() {
    let (test, conversation_id) = setup_live().await;
    assert_error(
        test.session
            .snapshot(&REWINDABLE_LIVE_DOC, conversation_id, context())
            .await,
        "does not match the supplied definition semantics",
    );
    assert_error(
        test.session
            .commit(
                move |tx| async move {
                    tx.doc(&REWINDABLE_LIVE_DOC, conversation_id).await?;
                    Ok(())
                },
                context(),
            )
            .await,
        "does not match the supplied definition semantics",
    );
    assert_error(
        test.session
            .commit(
                move |tx| async move {
                    tx.doc(&LIVE_DOC_V2, conversation_id).await?;
                    Ok(())
                },
                context(),
            )
            .await,
        "requires migration from version 1",
    );
}

/// A typed document value that serializes to a non-finite number.
#[derive(Serialize, Deserialize)]
struct NonFinite {
    at: f64,
}

/// TS initializes with a `Date` and pushes `undefined` into a draft. Rust
/// drafts accept only `JsonValue`, so both halves use a typed initializer
/// that is not strict JSON (NaN); the second half keeps the TS assertions
/// on a conversation document: nothing is admitted and nothing is created.
#[tokio::test]
async fn rejects_non_json_initializer_values_and_draft_placements_before_storage_admission() {
    const DATE_DOC: SessionDoc<NonFinite> = match SessionDoc::define(DocDefinition {
        kind: "test.date",
        version: 1,
        initial: || NonFinite { at: f64::NAN },
        migrate: None,
        checkpoint_when: None,
    }) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };
    const NON_JSON_LIVE_DOC: ConversationDoc<NonFinite> = match ConversationDoc::define(
        DocDefinition {
            kind: "test.nonjson",
            version: 1,
            initial: || NonFinite { at: f64::INFINITY },
            migrate: None,
            checkpoint_when: None,
        },
        LatestFork::Initial,
    ) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let conversation_id = create_conversation(&session).await;
    assert_error(
        session
            .commit(
                |tx| async move {
                    tx.doc(&DATE_DOC, ()).await?;
                    Ok(())
                },
                context(),
            )
            .await,
        "strict JSON",
    );
    let commits = storage.commit_count();
    assert_error(
        session
            .commit(
                move |tx| async move {
                    tx.doc(&NON_JSON_LIVE_DOC, conversation_id).await?;
                    Ok(())
                },
                context(),
            )
            .await,
        "strict JSON",
    );
    assert_eq!(storage.commit_count(), commits);
    assert!(session
        .snapshot(&NON_JSON_LIVE_DOC, conversation_id, context())
        .await
        .unwrap()
        .is_none());
}

#[tokio::test]
async fn rolls_back_prepared_documents_when_batch_assembly_fails() {
    let (test, conversation_id) = setup_live().await;
    test.session
        .commit(
            |tx| async move {
                tx.doc(&COUNTER_DOC, ()).await?.set("count", 1)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let live = snapshot_live(&test, conversation_id).await;
    let counter = test
        .session
        .snapshot(&COUNTER_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    let commits = test.storage.commit_count();
    assert_error(
        test.session
            .commit_with(
                move |tx| async move {
                    tx.doc(&LIVE_DOC, conversation_id)
                        .await?
                        .set("message", "lost")?;
                    tx.doc(&COUNTER_DOC, ()).await?.set("count", 2)?;
                    // Replacing a missing task fails during assembly, after every change was prepared.
                    tx.set_task(missing_task(conversation_id))
                },
                context(),
                TransactionScope::default(),
            )
            .await,
        "Task 999 does not exist",
    );
    assert_eq!(test.storage.commit_count(), commits);
    assert!(Arc::ptr_eq(
        &snapshot_live(&test, conversation_id).await,
        &live
    ));
    assert!(Arc::ptr_eq(
        &test
            .session
            .snapshot(&COUNTER_DOC, (), context())
            .await
            .unwrap()
            .unwrap(),
        &counter
    ));
    test.session
        .commit(
            move |tx| async move {
                tx.doc(&LIVE_DOC, conversation_id)
                    .await?
                    .set("message", "next")?;
                tx.doc(&COUNTER_DOC, ()).await?.set("count", 3)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let counter = test
        .session
        .snapshot(&COUNTER_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(field(&counter, "count"), Some(json("3")));
}

#[tokio::test]
async fn fails_the_session_after_a_storage_failure_and_publishes_nothing() {
    let (test, conversation_id) = setup_live().await;
    flush().await;
    let before = snapshot_live(&test, conversation_id).await;
    let published = test.publications.len();
    test.storage
        .fail_next_commit(StorageError::Failed(Arc::new(std::io::Error::other(
            "disk vanished",
        ))));
    assert_error(
        test.session
            .commit(
                move |tx| async move {
                    tx.doc(&LIVE_DOC, conversation_id)
                        .await?
                        .set("message", "uncertain")?;
                    Ok(())
                },
                context(),
            )
            .await,
        "disk vanished",
    );
    flush().await;
    assert_eq!(test.publications.len(), published);
    assert!(message(&before).is_none());
    assert!(matches!(
        test.session
            .snapshot(&LIVE_DOC, conversation_id, context())
            .await,
        Err(SessionError::Failed(_))
    ));
    assert!(matches!(
        test.session.commit(|_tx| async { Ok(()) }, context()).await,
        Err(SessionError::Failed(_))
    ));
    // TS awaits close and ignores nothing: a failed close still settles.
    let _ = test.session.close(context()).await;
}

#[tokio::test]
async fn keeps_the_previous_revision_unchanged_through_storage_settlement() {
    let (test, conversation_id) = setup_live().await;
    let before = snapshot_live(&test, conversation_id).await;
    let copy = JsonValue::parse(&JsonValue::Object(Arc::clone(&before)).to_string()).unwrap();
    let gate = test.storage.hold_commits();
    let commit = tokio::spawn(test.session.commit(
        move |tx| async move {
            let live = tx.doc(&LIVE_DOC, conversation_id).await?;
            child(&live, "items").push(["c"])?;
            child(&live, "nested").set("count", 9)?;
            Ok(())
        },
        context(),
    ));
    gate.entered().await;
    assert!(Arc::ptr_eq(
        &snapshot_live(&test, conversation_id).await,
        &before
    ));
    assert_eq!(JsonValue::Object(Arc::clone(&before)), copy);
    gate.release();
    commit.await.unwrap().unwrap();
    let after = snapshot_live(&test, conversation_id).await;
    assert_eq!(field(&after, "items"), Some(json(r#"["a","b","c"]"#)));
    assert_eq!(JsonValue::Object(before), copy);
}

#[tokio::test]
async fn retires_documents_and_creates_a_new_incarnation_at_the_same_address() {
    let (test, conversation_id) = setup_live().await;
    flush().await;
    let old_id = document_changes(&test.publications.last())[0].record.id;
    test.session
        .commit(
            move |tx| async move {
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                live.set("message", "final")?;
                tx.retire_doc(&LIVE_DOC, conversation_id).await?;
                let replacement = tx.doc(&LIVE_DOC, conversation_id).await?;
                assert_ne!(replacement, live);
                replacement.set("message", "new")?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let writes = test.storage.last_commit();
    assert_eq!(writes.len(), 3);
    assert!(writes
        .iter()
        .any(|write| matches!(write, StorageWrite::DocumentChange { id, .. } if *id == old_id)));
    assert!(has_retire(&writes, old_id));
    assert!(has_live_create(&writes));
    flush().await;
    let publication = test.publications.last();
    let mut changes = document_changes(&publication).into_iter();
    let (retired, created) = (changes.next().unwrap(), changes.next().unwrap());
    assert_eq!(retired.record.id, old_id);
    assert!(retired.value.is_none());
    assert!(retired.ops.is_empty());
    assert_eq!(retired.record.retired_at, Some(publication.seq));
    assert_ne!(created.record.id, old_id);
    assert_eq!(created.record.created_at, publication.seq);
    let created_value = created.value.clone().unwrap();
    assert_eq!(message(&created_value), Some(json(r#""new""#)));
    assert_eq!(field(&created_value, "items"), Some(json("[]")));
    assert!(created.ops.is_empty());
    assert!(Arc::ptr_eq(
        &snapshot_live(&test, conversation_id).await,
        &created_value
    ));

    let retire = move |tx: Tx| async move { tx.retire_doc(&LIVE_DOC, conversation_id).await };
    test.session.commit(retire, context()).await.unwrap();
    assert!(test
        .session
        .snapshot(&LIVE_DOC, conversation_id, context())
        .await
        .unwrap()
        .is_none());
    test.session.unload_documents().await.unwrap();
    assert!(test
        .session
        .snapshot(&LIVE_DOC, conversation_id, context())
        .await
        .unwrap()
        .is_none());
    // Retiring an absent address is a no-op.
    let commits = test.storage.commit_count();
    test.session.commit(retire, context()).await.unwrap();
    assert_eq!(test.storage.commit_count(), commits);
}

#[tokio::test]
async fn retires_without_acquisition_and_recreates_both_existing_and_absent_addresses() {
    let (test, conversation_id) = setup_live().await;
    flush().await;
    let old_id = document_changes(&test.publications.last())[0].record.id;
    test.session.unload_documents().await.unwrap();
    test.session
        .commit(
            move |tx| async move {
                let retired = tx.retire_doc(&LIVE_DOC, conversation_id);
                let replacement = tx.doc(&LIVE_DOC, conversation_id);
                let (live, retired) = futures::join!(replacement, retired);
                retired?;
                live?.set("message", "replacement")?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let existing_writes = test.storage.last_commit();
    assert_eq!(existing_writes.len(), 2);
    assert!(has_retire(&existing_writes, old_id));
    assert!(has_live_create(&existing_writes));

    test.session
        .commit(
            |tx| async move {
                let retired = tx.retire_doc(&MEMBER_DOC, "absent");
                let replacement = tx.doc_member(&MEMBER_DOC, "absent", &"seed".to_owned());
                let (member, retired) = futures::join!(replacement, retired);
                retired?;
                member?.set("hits", 1)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let absent_writes = test.storage.last_commit();
    assert_eq!(count_type(&absent_writes, "document.retire"), 0);
    assert_eq!(count_type(&absent_writes, "document.create"), 1);
    assert_eq!(
        test.session
            .snapshot(&MEMBER_DOC, "absent", context())
            .await
            .unwrap()
            .map(JsonValue::Object),
        Some(json(r#"{"seed":"seed","hits":1}"#))
    );
}

#[tokio::test]
async fn retires_the_existing_incarnation_when_retirement_races_a_pending_acquisition() {
    let (test, conversation_id) = setup_live().await;
    flush().await;
    let old_id = document_changes(&test.publications.last())[0].record.id;
    test.session
        .commit(
            move |tx| async move {
                let acquired = tx.doc(&LIVE_DOC, conversation_id);
                let retired = tx.retire_doc(&LIVE_DOC, conversation_id);
                acquired.await?.set("message", "final")?;
                retired.await
            },
            context(),
        )
        .await
        .unwrap();
    let first_writes = test.storage.last_commit();
    assert_eq!(first_writes.len(), 2);
    assert!(first_writes.iter().any(|write| matches!(
        write,
        StorageWrite::DocumentChange { id, content: DocumentContent::Delta(_) } if *id == old_id
    )));
    assert!(has_retire(&first_writes, old_id));
    assert!(test
        .session
        .snapshot(&LIVE_DOC, conversation_id, context())
        .await
        .unwrap()
        .is_none());

    set_live_message(&test, conversation_id, "second").await;
    flush().await;
    let second_id = document_changes(&test.publications.last())[0].record.id;
    test.session
        .commit(
            move |tx| async move {
                let acquired = tx.doc(&LIVE_DOC, conversation_id);
                let retired = tx.retire_doc(&LIVE_DOC, conversation_id);
                let recreated = tx.doc(&LIVE_DOC, conversation_id);
                let (old, fresh, retired) = futures::join!(acquired, recreated, retired);
                retired?;
                let (old, fresh) = (old?, fresh?);
                assert_ne!(fresh, old);
                fresh.set("message", "third")?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    let writes = test.storage.last_commit();
    assert_eq!(writes.len(), 2);
    assert!(has_retire(&writes, second_id));
    assert!(has_live_create(&writes));
    assert_eq!(
        message(&snapshot_live(&test, conversation_id).await),
        Some(json(r#""third""#))
    );
}

#[tokio::test]
async fn reloads_an_unloaded_document_from_storage() {
    let (test, conversation_id) = setup_live().await;
    let loaded = snapshot_live(&test, conversation_id).await;
    let reads = test.storage.document_read_count();
    test.session.unload_documents().await.unwrap();
    let reloaded = snapshot_live(&test, conversation_id).await;
    // TS also expects a fresh object (`not.toBe`); Rust MemoryStorage shares
    // its immutable stored value, so the reload is observed via the read count.
    assert!(test.storage.document_read_count() > reads);
    assert_eq!(reloaded, loaded);
    test.session
        .commit(
            move |tx| async move {
                child(&tx.doc(&LIVE_DOC, conversation_id).await?, "items").push(["c"])?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    test.session.unload_documents().await.unwrap();
    assert_eq!(
        field(&snapshot_live(&test, conversation_id).await, "items"),
        Some(json(r#"["a","b","c"]"#))
    );
}

/// TS compares the delivered context by identity; Rust `Context` has no
/// identity, so the commit context carries a unique value the listener reads.
#[tokio::test]
async fn delivers_complete_publications_synchronously_after_adoption() {
    let (test, conversation_id) = setup_live().await;
    let published = test.publications.len();
    let key = create_context_key::<u64>("commit context");
    let commit_context: Context = with_context_value(&key, 7, context());
    let listener_context: Arc<Mutex<Option<Context>>> = Arc::default();
    let sink = Arc::clone(&listener_context);
    let unsubscribe = test
        .session
        .subscribe_commits(Arc::new(move |_publication, delivered| {
            *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(delivered.clone());
        }))
        .unwrap();
    let result = test
        .session
        .commit(
            move |tx| async move {
                tx.doc(&LIVE_DOC, conversation_id)
                    .await?
                    .set("message", "m")?;
                Ok("done")
            },
            &commit_context,
        )
        .await
        .unwrap();
    assert_eq!(result, "done");
    let delivered = listener_context
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .expect("the listener ran before the commit settled");
    assert_eq!(delivered.value(&key), Some(7));
    assert_eq!(test.publications.len(), published + 1);
    unsubscribe.unsubscribe();
}

#[tokio::test]
async fn publishes_close_synchronously_and_supports_unsubscription() {
    let TestSession { session, .. } = open_test_session();
    let calls: Arc<Mutex<Vec<&'static str>>> = Arc::default();
    let active = Arc::clone(&calls);
    drop(
        session
            .subscribe_close(Arc::new(move || {
                active
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push("active");
            }))
            .unwrap(),
    );
    let removed = Arc::clone(&calls);
    let unsubscribe = session
        .subscribe_close(Arc::new(move || {
            removed
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push("removed");
        }))
        .unwrap();
    unsubscribe.unsubscribe();
    session.close(context()).await.unwrap();
    assert_eq!(
        *calls.lock().unwrap_or_else(PoisonError::into_inner),
        vec!["active"]
    );
}

#[tokio::test]
async fn settles_admitted_commits_before_close_and_rejects_later_admission() {
    let (test, conversation_id) = setup_live().await;
    let gate = test.storage.hold_commits();
    let commit = tokio::spawn(test.session.commit(
        move |tx| async move {
            tx.doc(&LIVE_DOC, conversation_id)
                .await?
                .set("message", "admitted")?;
            Ok(())
        },
        context(),
    ));
    gate.entered().await;
    let queued = tokio::spawn(test.session.commit(
        move |tx| async move {
            tx.doc(&LIVE_DOC, conversation_id)
                .await?
                .set("message", "queued")?;
            Ok(())
        },
        context(),
    ));
    let admitted_snapshot = tokio::spawn(test.session.snapshot(&MEMBER_DOC, "absent", context()));
    let closed = tokio::spawn(test.session.close(context()));
    assert_error(
        test.session.commit(|_tx| async { Ok(()) }, context()).await,
        "closed",
    );
    assert_error(
        test.session
            .snapshot(&LIVE_DOC, conversation_id, context())
            .await,
        "closed",
    );
    gate.release();
    commit.await.unwrap().unwrap();
    queued.await.unwrap().unwrap();
    assert!(admitted_snapshot.await.unwrap().unwrap().is_none());
    closed.await.unwrap().unwrap();
    let stored = test
        .storage
        .find_document(
            &DocumentAddress {
                kind: "test.live".to_owned(),
                scope: DocumentScope::Conversation { conversation_id },
                key: None,
            },
            DocumentPoint::Current,
            context(),
        )
        .await;
    assert!(stored.is_err());
}
