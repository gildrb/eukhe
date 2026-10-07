//! Port of `test/memory-storage.test.ts`.

use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_chord::json::JsonValue;
use eukhe_durable::storage::MemoryStorage;
use eukhe_durable::testing::{run_storage_conformance, StorageConformanceOptions};
use eukhe_durable::types::{
    ConversationRecord, EntryId, EntryRecord, Seq, Storage, StorageWrite, ROOT_CONVERSATION_ID,
};

#[tokio::test(flavor = "multi_thread")]
async fn memory_storage_conformance() {
    run_storage_conformance(
        "MemoryStorage",
        StorageConformanceOptions {
            with_storage: Arc::new(|test| {
                Box::pin(async move { test(Arc::new(MemoryStorage::new())).await })
            }),
        },
    )
    .await;
}

fn nested(values: &[i32]) -> JsonValue {
    let mut object = eukhe_chord::json::JsonObject::new();
    object.insert("nested", values.iter().copied().collect::<JsonValue>());
    JsonValue::Object(Arc::new(object))
}

/// TS mutates the frozen prepared write and expects a throw. Rust exposes the
/// prepared writes only by shared reference; the closest observable check is
/// that changing a copy of an exposed write leaves the commit unchanged.
#[tokio::test]
async fn does_not_expose_retained_state_through_a_prepared_commit() {
    let cx = &*BACKGROUND_CONTEXT;
    let storage = MemoryStorage::new();
    storage
        .commit(
            &[StorageWrite::Conversation {
                value: ConversationRecord {
                    id: ROOT_CONVERSATION_ID,
                    parent: None,
                    owner: None,
                },
            }],
            cx,
        )
        .await
        .unwrap();
    let entry_id = EntryId::from_number(2);
    let prepared = storage
        .prepare_commit(
            &[StorageWrite::Entry {
                value: EntryRecord {
                    model: None,
                    data: Some(nested(&[1])),
                    edits: None,
                    kind: "test".to_owned(),
                    id: entry_id,
                    conversation_id: ROOT_CONVERSATION_ID,
                    head: None,
                    by_task_id: None,
                },
            }],
            None,
        )
        .unwrap();
    let StorageWrite::Entry { value } = &prepared.writes()[0] else {
        panic!("Expected an entry write")
    };
    let mut exposed = value.clone();
    exposed.data = Some(nested(&[1, 2]));

    assert_eq!(prepared.apply(), Seq::from_number(2));
    assert_eq!(prepared.apply(), Seq::from_number(2));
    assert_eq!(
        storage
            .entry(entry_id, cx)
            .await
            .unwrap()
            .unwrap()
            .entry
            .data,
        Some(nested(&[1]))
    );
}
