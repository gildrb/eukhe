//! The live state tree of a session ([`StateTree`]): a background task
//! builds it from the committed history of the storage, then records each
//! commit of the Harness. The commit listener only queues the commit, so
//! no commit waits for the tree; open and attach never wait for the build;
//! a read waits until it ends.

use std::sync::{Arc, Mutex, MutexGuard, PoisonError};
use std::time::Instant;

use eukhe_durable::harness::Harness;
use eukhe_durable::session::{CommitListener, SessionResult, Unsubscribe};
use eukhe_durable::storage::jsonl::HistoryCommit;
use eukhe_durable::tree::{Applied, StateError, StateTree};
use eukhe_durable::types::CommitPublication;
use tokio::sync::{mpsc, watch};
use tokio::task::JoinHandle;

/// Where the live state tree is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TreeCursor {
    /// The build runs.
    Building,
    /// The tree is live; its cursor.
    Ready(usize),
    /// The tree stopped (its build or a record panicked): no read gets it.
    Failed,
}

/// The tree, while it is live.
enum Slot {
    Building,
    Ready(Box<StateTree>),
    Failed,
}

/// The commit subscription, which the tree ends when it fails.
type Subscription = Arc<Mutex<Option<Unsubscribe>>>;

/// The live state tree of one session. Dropping it stops following the
/// commits.
pub struct LiveStateTree {
    slot: Arc<Mutex<Slot>>,
    cursor: watch::Receiver<TreeCursor>,
    subscription: Subscription,
    recorder: JoinHandle<()>,
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Log each change that the tree did not take.
fn report(results: Vec<Result<Applied, StateError>>) {
    for result in results {
        match result {
            Ok(Applied::Accepted) => {}
            Ok(Applied::Rejected) => tracing::warn!("state tree rejected a record"),
            Err(error) => tracing::warn!(%error, "state tree change not recorded"),
        }
    }
}

/// End the commit subscription.
fn unsubscribe(subscription: &Subscription) {
    if let Some(unsubscribe) = lock(subscription).take() {
        unsubscribe.unsubscribe();
    }
}

/// Marks the tree failed and ends the subscription when the recorder
/// unwinds from a panic.
struct FailOnPanic {
    slot: Arc<Mutex<Slot>>,
    cursor: Arc<watch::Sender<TreeCursor>>,
    subscription: Subscription,
}

impl FailOnPanic {
    fn fail(&self) {
        *lock(&self.slot) = Slot::Failed;
        self.cursor.send_replace(TreeCursor::Failed);
        unsubscribe(&self.subscription);
    }
}

impl Drop for FailOnPanic {
    fn drop(&mut self) {
        if std::thread::panicking() {
            tracing::error!("state tree recorder panicked");
            self.fail();
        }
    }
}

impl LiveStateTree {
    /// Follow the commits of `harness`, then take the history with
    /// `take_history` and build the tree from it in the background. A
    /// commit in the history and in the stream counts once.
    ///
    /// # Errors
    ///
    /// The Session is closed.
    pub(crate) fn start(
        harness: &Harness,
        take_history: impl FnOnce() -> Vec<HistoryCommit>,
    ) -> SessionResult<Self> {
        let (queue, commits) = mpsc::unbounded_channel::<CommitPublication>();
        let listener: CommitListener = Arc::new(move |publication, _| {
            // A closed queue means the tree stopped; it records nothing more.
            let _ = queue.send(publication.clone());
        });
        let subscription: Subscription =
            Arc::new(Mutex::new(Some(harness.subscribe_commits(listener)?)));
        let history = take_history();
        let slot = Arc::new(Mutex::new(Slot::Building));
        let (cursor_sender, cursor) = watch::channel(TreeCursor::Building);
        let recorder = tokio::spawn(record_commits(
            history,
            commits,
            FailOnPanic {
                slot: Arc::clone(&slot),
                cursor: Arc::new(cursor_sender),
                subscription: Arc::clone(&subscription),
            },
        ));
        Ok(Self {
            slot,
            cursor,
            subscription,
            recorder,
        })
    }

    /// Run `read` on the tree once the build ends. `None` when the tree
    /// failed.
    pub async fn read<R>(&self, read: impl FnOnce(&StateTree) -> R) -> Option<R> {
        let mut cursor = self.cursor.clone();
        // The recorder holds the sender until it sets an end state.
        let _ = cursor
            .wait_for(|cursor| *cursor != TreeCursor::Building)
            .await;
        match &*lock(&self.slot) {
            Slot::Ready(tree) => Some(read(tree)),
            Slot::Building | Slot::Failed => None,
        }
    }

    /// The cursor of the tree; it changes after each commit that adds
    /// records.
    #[must_use]
    pub fn cursor(&self) -> watch::Receiver<TreeCursor> {
        self.cursor.clone()
    }
}

impl Drop for LiveStateTree {
    fn drop(&mut self) {
        unsubscribe(&self.subscription);
        self.recorder.abort();
    }
}

/// Build the tree from `history` on a blocking thread, then record the
/// queued commits, a batch at a time, until the queue closes.
#[tracing::instrument(skip_all)]
async fn record_commits(
    history: Vec<HistoryCommit>,
    mut commits: mpsc::UnboundedReceiver<CommitPublication>,
    guard: FailOnPanic,
) {
    let started = Instant::now();
    let commit_count = history.len();
    let built = tokio::task::spawn_blocking(move || StateTree::from_history(&history)).await;
    let (tree, results) = match built {
        Ok(built) => built,
        Err(error) => {
            tracing::error!(%error, "state tree build failed");
            guard.fail();
            return;
        }
    };
    report(results);
    tracing::debug!(
        commits = commit_count,
        records = tree.cursor(),
        nodes = tree.tree().len(),
        elapsed_us = started.elapsed().as_micros(),
        "state tree built"
    );
    {
        let mut slot = lock(&guard.slot);
        // Sent under the slot lock: a later batch sends a later cursor.
        guard.cursor.send_replace(TreeCursor::Ready(tree.cursor()));
        *slot = Slot::Ready(Box::new(tree));
    }
    let mut batch = Vec::new();
    while commits.recv_many(&mut batch, 256).await > 0 {
        let mut slot = lock(&guard.slot);
        match &mut *slot {
            Slot::Ready(tree) => {
                for publication in batch.drain(..) {
                    report(tree.record(&publication));
                }
                let next = TreeCursor::Ready(tree.cursor());
                guard.cursor.send_if_modified(|cursor| {
                    let changed = *cursor != next;
                    *cursor = next;
                    changed
                });
            }
            // Only this task sets the slot, and it is ready here.
            Slot::Building | Slot::Failed => return,
        }
    }
}
