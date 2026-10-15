//! `settings.document_retention_ms` (pi-durable 1.2 `documentRetentionMs`):
//! the Harness Session reads it at each use.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use super::support::{context, create_models, create_registry};
use crate::harness::agent::{resolve_settings, AGENT_DOC};
use crate::harness::types::{HarnessOptions, HarnessSettings, LiveSettings};
use crate::harness::Harness;
use crate::session::DocumentCacheSizes;
use crate::storage::MemoryStorage;
use crate::types::{ConversationId, ConversationOwnership};

/// Resolved values compare by bits: every one is exact.
#[test]
fn resolves_document_retention_over_its_ten_minute_default() {
    let retention = |document_retention_ms| {
        resolve_settings(Some(&HarnessSettings {
            document_retention_ms,
            ..HarnessSettings::default()
        }))
        .document_retention_ms
        .to_bits()
    };
    assert_eq!(
        [
            resolve_settings(None).document_retention_ms.to_bits(),
            retention(None),
            retention(Some(-1.0)),
            retention(Some(f64::NAN)),
            retention(Some(0.0)),
            retention(Some(2_500.0)),
        ],
        [600_000.0, 600_000.0, 600_000.0, 600_000.0, 0.0, 2_500.0].map(f64::to_bits)
    );
}

/// Wait for every job queued on the Session line so far.
async fn settle_line(harness: &Harness) {
    harness.read_on_line(async { Ok(()) }).await.unwrap();
}

/// An empty commit; its end evicts what expired.
async fn empty_commit(harness: &Harness) {
    harness
        .commit(|_tx| async move { Ok(()) }, context())
        .await
        .unwrap();
    settle_line(harness).await;
}

#[tokio::test]
async fn evicts_unobserved_harness_documents_under_the_live_retention_setting() {
    let settings = Arc::new(LiveSettings::new(HarnessSettings {
        document_retention_ms: Some(1_000.0),
        ..HarnessSettings::default()
    }));
    let now = Arc::new(AtomicU64::new(0_f64.to_bits()));
    let clock = Arc::clone(&now);
    let set_now = |ms: f64| now.store(ms.to_bits(), Ordering::SeqCst);
    let harness = Harness::open(
        Arc::new(MemoryStorage::new()),
        HarnessOptions {
            settings: Some(Arc::clone(&settings) as _),
            now: Some(Arc::new(move || {
                f64::from_bits(clock.load(Ordering::SeqCst))
            })),
            ..HarnessOptions::new(create_models(), Arc::new(create_registry()))
        },
        context(),
    )
    .await
    .unwrap();
    let conversation_id: ConversationId = harness
        .commit(
            |tx| async move {
                Ok(tx
                    .create_conversation(ConversationOwnership::Ownerless)
                    .await?
                    .id)
            },
            context(),
        )
        .await
        .unwrap();
    settle_line(&harness).await;
    let created = harness.document_cache_sizes();
    assert!(created.idle > 0, "{created:?}");
    let resident = DocumentCacheSizes {
        cached: created.cached - created.idle,
        idle: 0,
        attached: created.attached,
    };

    set_now(999.0);
    empty_commit(&harness).await;
    assert_eq!(harness.document_cache_sizes(), created);
    set_now(1_000.0);
    empty_commit(&harness).await;
    assert_eq!(harness.document_cache_sizes(), resident);

    // A setting changed while the Harness runs applies at the next use.
    settings.update(|settings| settings.document_retention_ms = Some(0.0));
    assert!(harness
        .snapshot(&AGENT_DOC, conversation_id, context())
        .await
        .unwrap()
        .is_some());
    empty_commit(&harness).await;
    assert_eq!(harness.document_cache_sizes(), resident);
    harness.close(context()).await.unwrap();
}
