//! Regression tests of the chat memory's waits (`docs/harness.md` H6):
//! every request to an owner in another process has a reply deadline, and
//! a request to a stuck owner ends at it.

use std::time::Duration;

use eukhe_types::platform::transport::bind_transport;

use super::{ImportItem, Memory, Request, IMPORT_ITEM_DEADLINE, REPLY_DEADLINE};
use crate::memory::compactor::tests::Scripted;
use crate::memory::{AppendKey, CompactionPrompt, Kind};

/// One request of each kind.
fn every_request() -> Vec<Request> {
    vec![
        Request::Append {
            kind: Kind::User,
            text: "hi".to_owned(),
            date: "2026-01-01T00:00:00Z".to_owned(),
            dedupe: false,
            key: Some(AppendKey {
                scope: "s".to_owned(),
                seq: 1,
            }),
            images: Vec::new(),
        },
        Request::Import { items: Vec::new() },
        Request::Import {
            items: vec![
                ImportItem {
                    kind: Kind::User,
                    text: "hi".to_owned(),
                    date: "2026-01-01T00:00:00Z".to_owned(),
                };
                500
            ],
        },
        Request::SettledRender { within_ms: 0 },
        Request::SettledRender {
            within_ms: u64::MAX,
        },
        Request::Render,
        Request::Zoom { id: 1, count: 1 },
        Request::Date { id: 1 },
        Request::Tree { node: None },
        Request::Status,
        Request::Persist,
        Request::Parts,
        Request::SetPrompt {
            prompt: CompactionPrompt {
                system: String::new(),
                tools: Vec::new(),
            },
        },
        Request::Subscribe,
    ]
}

/// Every request to an owner in another process has a reply deadline of
/// at least [`REPLY_DEADLINE`] (H6.1), a settled view on top of its settle
/// deadline, an import on top of [`IMPORT_ITEM_DEADLINE`] per item (a
/// large batch to an owner on a slow disk is no stuck owner). The match
/// has no catch-all, so a new request must take a side here.
#[test]
fn every_request_to_a_remote_owner_has_a_reply_deadline() {
    for request in every_request() {
        let deadline = request.reply_deadline();
        let least = match &request {
            Request::SettledRender { within_ms } => {
                Duration::from_millis(*within_ms).saturating_add(REPLY_DEADLINE)
            }
            Request::Import { items } => {
                IMPORT_ITEM_DEADLINE * u32::try_from(items.len()).unwrap() + REPLY_DEADLINE
            }
            Request::Append { .. }
            | Request::Render
            | Request::Zoom { .. }
            | Request::Date { .. }
            | Request::Tree { .. }
            | Request::Status
            | Request::Persist
            | Request::Parts
            | Request::SetPrompt { .. }
            | Request::Subscribe => REPLY_DEADLINE,
        };
        assert!(deadline >= least, "{request:?}: {deadline:?}");
    }
}

/// An owner that is alive (its socket takes connections) but never
/// answers: the request fails at its deadline with an error the turn
/// shows, instead of waiting forever.
#[tokio::test(start_paused = true)]
async fn a_stuck_owner_fails_the_request_at_its_reply_deadline() {
    let dir = tempfile::tempdir().unwrap();
    let _stuck = bind_transport(
        &dir.path().join("lock"),
        eukhe_bend::rules::fsmode::peer_verdict,
    )
    .await
    .unwrap();
    let memory = Memory::open(dir.path(), Scripted::with(Vec::new()))
        .await
        .unwrap();
    assert!(!memory.owns().await);
    let error = tokio::time::timeout(REPLY_DEADLINE * 2, memory.status())
        .await
        .expect("the request outlived its reply deadline")
        .unwrap_err();
    assert_eq!(
        error.to_string(),
        "the chat memory owner did not answer within 30 s: it is stuck (the request may still run)"
    );
}
