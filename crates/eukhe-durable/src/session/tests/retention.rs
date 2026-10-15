//! Document retention (pi-durable 1.2 `documentRetentionMs`): the Session's
//! document cache keeps an unobserved document only for the retention period
//! after its last read or write.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use eukhe_chord::json::JsonValue;

use super::support::{context, json, ControlledStorage};
use crate::documents::{DocDefinition, SessionDoc};
use crate::session::{create_session, DocumentCacheSizes, Session, SessionOptions};
use crate::types::Storage;

const NOTE_DOC: SessionDoc<JsonValue> = match SessionDoc::define(DocDefinition {
    kind: "retention.note",
    version: 1,
    initial: || json(r#"{"count":0}"#),
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("valid definition"),
};

/// A Session with a controllable clock, starting at 0.
struct Retained {
    storage: Arc<ControlledStorage>,
    session: Session,
    now: Arc<AtomicU64>,
}

impl Retained {
    fn open(document_retention_ms: Option<f64>) -> Self {
        let storage = ControlledStorage::new();
        let now = Arc::new(AtomicU64::new(0_f64.to_bits()));
        let clock = Arc::clone(&now);
        let session = create_session(
            Arc::clone(&storage) as Arc<dyn Storage>,
            SessionOptions {
                now: Some(Arc::new(move || {
                    f64::from_bits(clock.load(Ordering::SeqCst))
                })),
                document_retention_ms,
            },
        );
        Self {
            storage,
            session,
            now,
        }
    }

    fn set_now(&self, ms: f64) {
        self.now.store(ms.to_bits(), Ordering::SeqCst);
    }

    async fn write(&self, count: i32) {
        self.session
            .commit(
                move |tx| async move {
                    tx.doc(&NOTE_DOC, ()).await?.set("count", count)?;
                    Ok(())
                },
                context(),
            )
            .await
            .unwrap();
    }

    /// A commit that writes nothing; its end evicts what expired.
    async fn empty_commit(&self) {
        self.session
            .commit(|_tx| async move { Ok(()) }, context())
            .await
            .unwrap();
    }

    /// Wait for every job queued on the line so far, eviction jobs included.
    async fn settle_line(&self) {
        self.session.read_on_line(async { Ok(()) }).await.unwrap();
    }

    async fn read(&self) -> JsonValue {
        JsonValue::Object(
            self.session
                .snapshot(&NOTE_DOC, (), context())
                .await
                .unwrap()
                .expect("the note exists"),
        )
    }

    fn sizes(&self) -> DocumentCacheSizes {
        self.session.document_cache_sizes()
    }
}

fn sizes(cached: usize, idle: usize, attached: usize) -> DocumentCacheSizes {
    DocumentCacheSizes {
        cached,
        idle,
        attached,
    }
}

#[tokio::test]
async fn evicts_an_unobserved_document_after_its_retention_and_reloads_it_on_next_access() {
    let test = Retained::open(Some(1_000.0));
    test.write(1).await;
    assert_eq!(test.sizes(), sizes(1, 1, 0));

    test.set_now(999.0);
    test.empty_commit().await;
    assert_eq!(test.sizes(), sizes(1, 1, 0));
    test.set_now(1_000.0);
    test.empty_commit().await;
    assert_eq!(test.sizes(), sizes(0, 0, 0));

    let reads = test.storage.document_read_count();
    assert_eq!(test.read().await, json(r#"{"count":1}"#));
    assert_eq!(test.storage.document_read_count(), reads + 1);
    assert_eq!(test.sizes(), sizes(1, 1, 0));

    // A read renews the last use: the document stays until a full retention
    // passed after it, and reads from the cache meanwhile.
    test.set_now(1_500.0);
    assert_eq!(test.read().await, json(r#"{"count":1}"#));
    test.set_now(2_499.0);
    test.empty_commit().await;
    assert_eq!(test.sizes(), sizes(1, 1, 0));
    assert_eq!(test.storage.document_read_count(), reads + 1);
    test.set_now(2_500.0);
    test.empty_commit().await;
    assert_eq!(test.sizes(), sizes(0, 0, 0));

    // A write after the reload continues from the stored value.
    test.write(2).await;
    assert_eq!(test.read().await, json(r#"{"count":2}"#));
    test.session.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_a_document_a_watch_or_document_state_observes() {
    let test = Retained::open(Some(1_000.0));
    test.write(1).await;
    let state = test
        .session
        .document_state(&NOTE_DOC, (), context())
        .await
        .unwrap()
        .expect("the note exists");
    let watch = test
        .session
        .watch_doc(&NOTE_DOC, (), context())
        .await
        .unwrap()
        .expect("the note exists");
    assert_eq!(test.sizes(), sizes(1, 0, 1));

    test.set_now(5_000.0);
    test.empty_commit().await;
    assert_eq!(test.sizes(), sizes(1, 0, 1));
    let reads = test.storage.document_read_count();
    assert_eq!(test.read().await, json(r#"{"count":1}"#));
    assert_eq!(test.storage.document_read_count(), reads);

    // One observer left still pins the incarnation.
    state.dispose().unwrap();
    test.set_now(10_000.0);
    test.empty_commit().await;
    assert_eq!(test.sizes(), sizes(1, 0, 1));

    // Once the last detaches, the document is idle from then on.
    watch.cancel();
    assert_eq!(test.sizes(), sizes(1, 1, 0));
    test.set_now(10_999.0);
    test.empty_commit().await;
    assert_eq!(test.sizes(), sizes(1, 1, 0));
    test.set_now(11_000.0);
    test.empty_commit().await;
    assert_eq!(test.sizes(), sizes(0, 0, 0));
    test.session.close(context()).await.unwrap();
}

#[tokio::test]
async fn a_retired_incarnation_pins_nothing_for_its_observers() {
    let test = Retained::open(Some(1_000.0));
    test.write(1).await;
    let state = test
        .session
        .document_state(&NOTE_DOC, (), context())
        .await
        .unwrap()
        .expect("the note exists");
    assert_eq!(test.sizes(), sizes(1, 0, 1));
    test.session
        .commit(
            |tx| async move {
                tx.retire_doc(&NOTE_DOC, ()).await?;
                Ok(())
            },
            context(),
        )
        .await
        .unwrap();
    assert_eq!(test.sizes(), sizes(0, 0, 0));
    state.dispose().unwrap();
    test.session.close(context()).await.unwrap();
}

#[tokio::test]
async fn retention_0_drops_a_document_right_after_use() {
    let test = Retained::open(Some(0.0));
    test.write(1).await;
    assert_eq!(test.sizes(), sizes(0, 0, 0));

    let reads = test.storage.document_read_count();
    assert_eq!(test.read().await, json(r#"{"count":1}"#));
    test.settle_line().await;
    assert_eq!(test.sizes(), sizes(0, 0, 0));
    assert_eq!(test.read().await, json(r#"{"count":1}"#));
    test.settle_line().await;
    assert_eq!(test.sizes(), sizes(0, 0, 0));
    assert_eq!(test.storage.document_read_count(), reads + 2);

    test.write(2).await;
    assert_eq!(test.read().await, json(r#"{"count":2}"#));
    test.session.close(context()).await.unwrap();
}

#[tokio::test]
async fn keeps_documents_for_ten_minutes_by_default() {
    let test = Retained::open(None);
    test.write(1).await;
    test.set_now(599_999.0);
    test.empty_commit().await;
    assert_eq!(test.sizes(), sizes(1, 1, 0));
    test.set_now(600_000.0);
    test.empty_commit().await;
    assert_eq!(test.sizes(), sizes(0, 0, 0));
    test.session.close(context()).await.unwrap();
}
