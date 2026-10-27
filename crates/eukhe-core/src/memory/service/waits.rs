//! Regression tests of the chat memory's waits (`LAWS.bend` H6):
//! every request to an owner in another process but the lease has a reply
//! deadline, a request to a stuck owner ends at it, and a cancelled wait
//! for the turn file leaves nothing behind.

use std::time::Duration;

use eukhe_types::platform::transport::bind_transport;

use super::turn::TURN_FILE;
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
        Request::AcquireTurn { lease: 1 },
        Request::Release { lease: 1 },
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
/// large batch to an owner on a slow disk is no stuck owner). The one
/// exception is the lease's wait: it waits for another window's turn and
/// ends with that turn or with the run's cancel (H6.2). The match has no
/// catch-all, so a new request must take a side here.
#[test]
fn every_request_to_a_remote_owner_but_the_lease_has_a_reply_deadline() {
    for request in every_request() {
        let deadline = request.reply_deadline();
        let least = match &request {
            Request::AcquireTurn { .. } => {
                assert_eq!(deadline, None, "{request:?}");
                continue;
            }
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
            | Request::Release { .. }
            | Request::SetPrompt { .. }
            | Request::Subscribe => REPLY_DEADLINE,
        };
        assert!(
            deadline.is_some_and(|deadline| deadline >= least),
            "{request:?}: {deadline:?}"
        );
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

/// A lease granted while a holder from before an owner change still has
/// the turn file waits for the file. When that wait is dropped (the turn
/// was cancelled), nothing keeps waiting on the file: the runtime stops at
/// once. A blocking lock on a helper thread outlived the wait and held the
/// runtime's shutdown until the old holder let go.
#[test]
fn a_dropped_wait_for_the_turn_file_leaves_nothing_behind() {
    let dir = tempfile::tempdir().unwrap();
    let old_holder = std::fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(dir.path().join(TURN_FILE))
        .unwrap();
    old_holder.lock().unwrap();
    let chat = dir.path().to_path_buf();
    let (stopped, runtime_stopped) = std::sync::mpsc::channel();
    let session = std::thread::spawn(move || {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .unwrap();
        runtime.block_on(async {
            let memory = Memory::open(&chat, Scripted::with(Vec::new()))
                .await
                .unwrap();
            let mut wait = Box::pin(memory.acquire_turn());
            assert!(futures::poll!(wait.as_mut()).is_pending());
            // The owner answers in order: once this answers, the lease is
            // granted, and the next poll reaches the turn file.
            memory.status().await.unwrap();
            assert!(futures::poll!(wait.as_mut()).is_pending());
        });
        drop(runtime);
        stopped.send(()).unwrap();
    });
    let stopped = runtime_stopped.recv_timeout(Duration::from_secs(10));
    drop(old_holder);
    session.join().unwrap();
    assert_eq!(stopped, Ok(()));
}
