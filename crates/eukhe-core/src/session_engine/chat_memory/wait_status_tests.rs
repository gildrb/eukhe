//! The turn-wait status (`chat_turn_wait`): a root call queued behind
//! another window's turn reports `Waiting`, then `Cleared` once the lease
//! is granted or the wait is dropped; a call on a free chat reports
//! nothing.

use std::sync::Arc;

use serde_json::json;
use tokio::sync::mpsc;

use super::{ChatMemory, TurnWait, TurnWaitSink};
use crate::memory::{Memory, MemoryRole, Summarizer, SummarizerFuture};

/// A compactor that answers at once (short messages never reach it).
struct InstantSummarizer;

impl Summarizer for InstantSummarizer {
    fn complete(&self, _context: eukhe_types::ai::Context) -> SummarizerFuture {
        Box::pin(async {
            Ok(serde_json::from_value(json!({
                "content": [{ "type": "text", "text": "a summary" }],
                "api": "test",
                "provider": "test",
                "model": "m",
                "usage": eukhe_types::ai::Usage::default(),
                "stopReason": "stop",
                "timestamp": 0
            }))?)
        })
    }
}

/// Two windows on one chat; the second reports its waits.
struct Windows {
    first: Arc<ChatMemory>,
    second: Arc<ChatMemory>,
    waits: mpsc::UnboundedReceiver<TurnWait>,
    _tmp: tempfile::TempDir,
}

async fn windows() -> Windows {
    let tmp = tempfile::tempdir().unwrap();
    let memory = Memory::open(tmp.path().join("chat"), Arc::new(InstantSummarizer))
        .await
        .unwrap();
    let first = ChatMemory::new(memory.clone(), MemoryRole::Root);
    let second = ChatMemory::new(memory, MemoryRole::Root);
    let (sender, waits) = mpsc::unbounded_channel();
    let sink: TurnWaitSink = Arc::new(move |wait| {
        sender.send(wait).unwrap();
    });
    second.set_turn_wait_sink(sink);
    Windows {
        first,
        second,
        waits,
        _tmp: tmp,
    }
}

fn fresh_call(window: &Arc<ChatMemory>) -> tokio::task::JoinHandle<anyhow::Result<()>> {
    let window = Arc::clone(window);
    tokio::spawn(async move {
        window.begin_fresh_call();
        window.call_view().await.map(|_view| ())
    })
}

#[tokio::test(flavor = "multi_thread")]
async fn a_call_behind_another_windows_turn_reports_the_wait_until_granted() {
    let mut chat = windows().await;
    chat.first.begin_fresh_call();
    chat.first.call_view().await.unwrap();

    let second = fresh_call(&chat.second);
    assert_eq!(chat.waits.recv().await, Some(TurnWait::Waiting));
    chat.first.release_lease().await.unwrap();
    assert_eq!(chat.waits.recv().await, Some(TurnWait::Cleared));
    second.await.unwrap().unwrap();
    assert!(chat.waits.try_recv().is_err(), "one wait, one clear");
}

#[tokio::test(flavor = "multi_thread")]
async fn a_cancelled_wait_clears_its_status() {
    let mut chat = windows().await;
    chat.first.begin_fresh_call();
    chat.first.call_view().await.unwrap();

    let second = fresh_call(&chat.second);
    assert_eq!(chat.waits.recv().await, Some(TurnWait::Waiting));
    // The turn's abort drops the waiting future.
    second.abort();
    assert_eq!(chat.waits.recv().await, Some(TurnWait::Cleared));
}

#[tokio::test(flavor = "multi_thread")]
async fn a_call_on_a_free_chat_reports_no_wait() {
    let mut chat = windows().await;
    fresh_call(&chat.second).await.unwrap().unwrap();
    assert!(chat.waits.try_recv().is_err(), "a granted lease is no wait");
}
