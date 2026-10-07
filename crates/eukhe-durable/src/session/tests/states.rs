//! Port of `test/session-states.test.ts`.

use std::convert::Infallible;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::delta::Op;
use eukhe_chord::json::JsonValue;

use super::support::{
    context, create_conversation, document_changes, flush, json, open_test_session, TestSession,
};
use crate::documents::{
    ConversationDoc, DocDefinition, DocFamilyDefinition, SessionDoc, SessionDocFamily,
};
use crate::types::LatestFork;

const STATE_DOC: SessionDoc<JsonValue> = match SessionDoc::define(DocDefinition {
    kind: "state.state",
    version: 1,
    initial: || json(r#"{"value":0,"retained":{"label":"stable"}}"#),
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

const FAMILY_DOC: SessionDocFamily<JsonValue, String> =
    match SessionDocFamily::define(DocFamilyDefinition {
        kind: "state.family",
        version: 1,
        initial: |seed: String| {
            json(&format!(
                r#"{{"value":{}}}"#,
                eukhe_chord::json::utf16_len(&seed)
            ))
        },
        migrate: None,
        checkpoint_when: None,
    }) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };

fn number(value: &JsonValue) -> Option<f64> {
    value.get("value").and_then(JsonValue::as_f64)
}

async fn set_value(test: &TestSession, value: i32) {
    test.session
        .commit(
            move |tx| async move {
                tx.doc(&STATE_DOC, ()).await?.set("value", value)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
}

async fn create_state() -> TestSession {
    let test = open_test_session();
    test.session
        .commit(
            |tx| async move {
                tx.doc(&STATE_DOC, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    test
}

#[tokio::test]
async fn never_creates_an_absent_document() {
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let commits = storage.commit_count();
    assert!(session
        .document_state(&STATE_DOC, (), context())
        .await
        .unwrap()
        .is_none());
    assert!(session
        .document_state(&FAMILY_DOC, "missing", context())
        .await
        .unwrap()
        .is_none());
    assert_eq!(storage.commit_count(), commits);
    assert_eq!(storage.mint_count(), 0);
}

#[tokio::test]
async fn returns_an_immediately_hydrated_read_only_state_with_contiguous_chord_deliveries() {
    let test = create_state().await;
    let baseline = test
        .session
        .snapshot(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    let state = test
        .session
        .document_state(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    let deliveries: Arc<Mutex<Vec<(JsonValue, u64)>>> = Arc::default();
    let sink = Arc::clone(&deliveries);
    let _subscription = state.subscribe(move |value, _cx, delivery| {
        sink.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push((value, delivery.sequence));
    });
    assert!(state
        .value()
        .strict_equals(&JsonValue::Object(Arc::clone(&baseline))));

    set_value(&test, 1).await;
    set_value(&test, 2).await;
    flush().await;

    let deliveries = deliveries
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone();
    assert_eq!(
        deliveries
            .iter()
            .map(|(_, sequence)| *sequence)
            .collect::<Vec<_>>(),
        vec![0, 1, 2]
    );
    assert_eq!(
        deliveries
            .iter()
            .map(|(value, _)| number(value))
            .collect::<Vec<_>>(),
        vec![Some(0.0), Some(1.0), Some(2.0)]
    );
    let snapshot = test
        .session
        .snapshot(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    assert!(state.value().strict_equals(&JsonValue::Object(snapshot)));
    state.dispose().unwrap();
}

#[tokio::test]
async fn creates_independent_disposable_states_for_one_incarnation() {
    let test = create_state().await;
    let first = test
        .session
        .document_state(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    let second = test
        .session
        .document_state(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    // Independent states: disposing one leaves the other attached (below).
    set_value(&test, 1).await;
    flush().await;
    assert_eq!(number(&first.value()), Some(1.0));
    assert_eq!(number(&second.value()), Some(1.0));

    first.dispose().unwrap();
    set_value(&test, 2).await;
    flush().await;
    assert_eq!(number(&first.value()), Some(1.0));
    assert_eq!(number(&second.value()), Some(2.0));
    second.dispose().unwrap();
}

#[tokio::test]
async fn shares_exact_committed_value_and_operation_references_with_chord() {
    let test = create_state().await;
    let state = test
        .session
        .document_state(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    let received: Arc<Mutex<Option<Arc<[Op]>>>> = Arc::default();
    let sink = Arc::clone(&received);
    let _subscription = state.state_ref().subscribe(move |ops, _sequence, _cx| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(Arc::clone(ops));
        Ok::<(), Infallible>(())
    });
    set_value(&test, 4).await;
    flush().await;
    let published = document_changes(&test.publications.last()).remove(0);
    assert!(state
        .value()
        .strict_equals(&JsonValue::Object(published.value.clone().unwrap())));
    let received = received
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .clone()
        .unwrap();
    assert!(Arc::ptr_eq(&received, &published.ops));
    let snapshot = test
        .session
        .snapshot(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    assert!(state.value()["retained"].strict_equals(&JsonValue::Object(snapshot)["retained"]));
    state.dispose().unwrap();
}

#[tokio::test]
async fn captures_a_late_baseline_without_redelivering_an_already_covered_commit() {
    let test = create_state().await;
    set_value(&test, 1).await;
    let state = test
        .session
        .document_state(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    let deliveries: Arc<Mutex<Vec<u64>>> = Arc::default();
    let sink = Arc::clone(&deliveries);
    let _subscription = state.subscribe(move |_value, _cx, delivery| {
        sink.lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(delivery.sequence);
    });
    flush().await;
    assert_eq!(number(&state.value()), Some(1.0));
    assert_eq!(
        *deliveries.lock().unwrap_or_else(PoisonError::into_inner),
        vec![0]
    );
    state.dispose().unwrap();
}

#[tokio::test]
async fn publishes_null_retirement_and_never_follows_a_replacement_incarnation() {
    let test = create_state().await;
    let old_state = test
        .session
        .document_state(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    let retirement: Arc<Mutex<Option<Arc<[Op]>>>> = Arc::default();
    let sink = Arc::clone(&retirement);
    let _subscription = old_state.state_ref().subscribe(move |ops, _sequence, _cx| {
        *sink.lock().unwrap_or_else(PoisonError::into_inner) = Some(Arc::clone(ops));
        Ok::<(), Infallible>(())
    });
    test.session
        .commit(
            |tx| async move {
                tx.retire_doc(&STATE_DOC, ()).await?;
                tx.doc(&STATE_DOC, ()).await?.set("value", 10)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    assert!(old_state.value().is_null());
    assert_eq!(
        retirement
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .as_deref(),
        Some(&[Op::Replace(JsonValue::Null)][..])
    );

    let replacement = test
        .session
        .document_state(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(number(&replacement.value()), Some(10.0));
    set_value(&test, 11).await;
    flush().await;
    assert!(old_state.value().is_null());
    assert_eq!(number(&replacement.value()), Some(11.0));
    old_state.dispose().unwrap();
    replacement.dispose().unwrap();
}

#[tokio::test]
async fn cold_loads_a_definition_free_fork_copy() {
    const COPIED: ConversationDoc<JsonValue> = match ConversationDoc::define(
        DocDefinition {
            kind: "state.copied",
            version: 1,
            initial: || json(r#"{"value":0}"#),
            migrate: None,
            checkpoint_when: None,
        },
        LatestFork::Current,
    ) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };
    let TestSession {
        session, storage, ..
    } = open_test_session();
    let parent_id = create_conversation(&session).await;
    let entry = session
        .commit(
            move |tx| async move {
                let created = tx
                    .append_entry(parent_id, crate::types::EntryDraft::new("point"))
                    .await?;
                tx.doc(&COPIED, parent_id).await?.set("value", 7)?;
                Ok(created)
            },
            context(),
        )
        .await
        .unwrap();
    let child_id = session
        .commit(
            move |tx| async move {
                Ok(tx
                    .fork_conversation(
                        parent_id,
                        entry.id,
                        crate::types::ConversationOwnership::Ownerless,
                    )
                    .await?
                    .id)
            },
            context(),
        )
        .await
        .unwrap();
    let reads = storage.document_read_count();
    let state = session
        .document_state(&COPIED, child_id, context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(state.value(), json(r#"{"value":7}"#));
    assert!(storage.document_read_count() > reads);
    state.dispose().unwrap();
}

#[tokio::test]
async fn hydrates_a_migrated_tracker_without_writing_and_skips_an_equal_version_base_update() {
    const OLD: SessionDoc<JsonValue> = match SessionDoc::define(DocDefinition {
        kind: "state.migration",
        version: 1,
        initial: || json(r#"{"value":3}"#),
        migrate: None,
        checkpoint_when: None,
    }) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };
    const CURRENT: SessionDoc<JsonValue> = match SessionDoc::define(DocDefinition {
        kind: "state.migration",
        version: 2,
        initial: || json(r#"{"value":0,"migrated":false}"#),
        migrate: Some(|value, _from| {
            Ok(json(&format!(
                r#"{{"value":{},"migrated":true}}"#,
                value.get("value").cloned().unwrap_or(JsonValue::Null)
            )))
        }),
        checkpoint_when: None,
    }) {
        Ok(token) => token,
        Err(_) => panic!("valid definition"),
    };
    let TestSession {
        session, storage, ..
    } = open_test_session();
    session
        .commit(
            |tx| async move {
                tx.doc(&OLD, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    session.unload_documents().await.unwrap();
    let commits = storage.commit_count();
    let state = session
        .document_state(&CURRENT, (), context())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(state.value(), json(r#"{"value":3,"migrated":true}"#));
    assert_eq!(storage.commit_count(), commits);
    let baseline = state.value();

    session
        .commit(
            |tx| async move {
                tx.doc(&CURRENT, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    assert_eq!(storage.commit_count(), commits + 1);
    assert!(state.value().strict_equals(&baseline));
    session
        .commit(
            |tx| async move {
                tx.doc(&CURRENT, ()).await?.set("value", 4)?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    flush().await;
    assert_eq!(state.value(), json(r#"{"value":4,"migrated":true}"#));
    state.dispose().unwrap();
}

#[tokio::test]
async fn continues_from_exact_committed_values_after_the_tracker_cache_unloads() {
    let test = create_state().await;
    let state = test
        .session
        .document_state(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    let baseline = state.value();
    let reads = test.storage.document_read_count();
    test.session.unload_documents().await.unwrap();
    let reloaded = JsonValue::Object(
        test.session
            .snapshot(&STATE_DOC, (), context())
            .await
            .unwrap()
            .unwrap(),
    );
    assert_eq!(reloaded, baseline);
    // TS also expects a fresh object (`not.toBe`); Rust MemoryStorage may share
    // its immutable stored value, so the reload is observed via the read count.
    assert!(test.storage.document_read_count() > reads);
    set_value(&test, 6).await;
    flush().await;
    assert_eq!(number(&state.value()), Some(6.0));
    state.dispose().unwrap();
}

/// TS checks `Object.isFrozen` is false; Rust values are immutable by type, so
/// the observable part is that the state shares the snapshot's revision.
#[tokio::test]
async fn exposes_trusted_shared_immutable_values_without_freezing() {
    let test = create_state().await;
    let snapshot = test
        .session
        .snapshot(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    let state = test
        .session
        .document_state(&STATE_DOC, (), context())
        .await
        .unwrap()
        .unwrap();
    assert!(state.value().strict_equals(&JsonValue::Object(snapshot)));
    state.dispose().unwrap();
}
