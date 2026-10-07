//! Harness helpers (`harness/util.ts`): keyed waiters, paginated scans, and
//! the closed error.

use std::future::Future;
use std::hash::Hash;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_chord::context::Context;
use futures::FutureExt;
use tokio::sync::oneshot;

use crate::session::{SessionError, SessionResult};
use crate::types::{Cursor, Page};

type Sender<T> = oneshot::Sender<SessionResult<T>>;

/// The waiters of one key, by registration ID.
type WaiterSet<T> = Vec<(u64, Sender<T>)>;

struct WaiterSets<K, T> {
    /// Insertion-ordered keys (JS `Map` order) with their waiters.
    sets: Vec<(K, WaiterSet<T>)>,
    next: u64,
}

/// Pending waits by key. Each settles once: through `resolve`,
/// `reject_all`, or cancellation of its context.
pub(crate) struct Waiters<K, T> {
    inner: Arc<Mutex<WaiterSets<K, T>>>,
}

impl<K, T> Default for Waiters<K, T> {
    fn default() -> Self {
        Self {
            inner: Arc::new(Mutex::new(WaiterSets {
                sets: Vec::new(),
                next: 0,
            })),
        }
    }
}

fn lock<K, T>(inner: &Mutex<WaiterSets<K, T>>) -> MutexGuard<'_, WaiterSets<K, T>> {
    inner.lock().unwrap_or_else(PoisonError::into_inner)
}

impl<K, T> Waiters<K, T>
where
    K: Clone + Eq + Hash + Send + 'static,
    T: Clone + Send + 'static,
{
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Register a wait for `key` now; the future settles with its value, the
    /// `reject_all` error, or `cx`'s abort reason.
    pub(crate) fn add(
        &self,
        key: K,
        cx: &Context,
    ) -> impl Future<Output = SessionResult<T>> + Send + 'static {
        let signal = cx.abort_signal();
        if let Some(reason) = signal
            .as_ref()
            .and_then(eukhe_chord::context::AbortSignal::reason)
        {
            return futures::future::ready(Err(SessionError::Aborted(reason))).left_future();
        }
        let (sender, receiver) = oneshot::channel();
        let id = {
            let mut sets = lock(&self.inner);
            sets.next += 1;
            let id = sets.next;
            match sets.sets.iter_mut().find(|(each, _)| *each == key) {
                Some((_, set)) => set.push((id, sender)),
                None => sets.sets.push((key.clone(), vec![(id, sender)])),
            }
            id
        };
        let inner = Arc::clone(&self.inner);
        async move {
            let settled = match &signal {
                None => receiver.await,
                Some(signal) => {
                    tokio::select! {
                        settled = receiver => settled,
                        reason = signal.cancelled() => {
                            let mut sets = lock(&inner);
                            if let Some(position) = sets.sets.iter().position(|(each, _)| *each == key) {
                                let set = &mut sets.sets[position].1;
                                set.retain(|(each, _)| *each != id);
                                if set.is_empty() {
                                    sets.sets.remove(position);
                                }
                            }
                            return Err(SessionError::Aborted(reason));
                        }
                    }
                }
            };
            match settled {
                Ok(settled) => settled,
                // Only a dropped `Waiters` drops an unsettled sender; like a
                // JS promise nobody settles, the wait never ends.
                Err(_) => futures::future::pending().await,
            }
        }
        .right_future()
    }

    /// Keys with pending waiters, in first-registration order.
    pub(crate) fn keys(&self) -> Vec<K> {
        lock(&self.inner)
            .sets
            .iter()
            .map(|(key, _)| key.clone())
            .collect()
    }

    /// Settle every waiter of `key` with `value`.
    pub(crate) fn resolve(&self, key: &K, value: &T) {
        let set = {
            let mut sets = lock(&self.inner);
            let position = sets.sets.iter().position(|(each, _)| each == key);
            position.map(|position| sets.sets.remove(position).1)
        };
        for (_, sender) in set.unwrap_or_default() {
            // A waiter whose future was dropped no longer listens.
            let _ = sender.send(Ok(value.clone()));
        }
    }

    /// Reject every pending waiter with `error`.
    pub(crate) fn reject_all(&self, error: &SessionError) {
        let sets = std::mem::take(&mut lock(&self.inner).sets);
        for (_, set) in sets {
            for (_, sender) in set {
                // A waiter whose future was dropped no longer listens.
                let _ = sender.send(Err(error.clone()));
            }
        }
    }
}

/// Every item of a paginated scan, in page order.
///
/// # Errors
///
/// The first failing page's error.
pub(crate) async fn scan_all<T, F, Fut>(mut scan: F) -> SessionResult<Vec<T>>
where
    F: FnMut(Option<Cursor>) -> Fut,
    Fut: Future<Output = SessionResult<Page<T>>>,
{
    let mut items = Vec::new();
    let mut cursor = None;
    loop {
        let page = scan(cursor).await?;
        items.extend(page.items);
        cursor = page.next;
        if cursor.is_none() {
            return Ok(items);
        }
    }
}

/// The error of every operation after the Harness closed.
pub(crate) fn closed_error() -> SessionError {
    SessionError::error("Harness is closed")
}

#[cfg(test)]
mod tests {
    use eukhe_chord::context::{with_cancel, BACKGROUND_CONTEXT};

    use super::*;

    #[tokio::test]
    async fn resolves_rejects_and_cancels_waiters() {
        let waiters: Waiters<u32, &'static str> = Waiters::new();
        let first = waiters.add(1, &BACKGROUND_CONTEXT);
        let (cx, cancel) = with_cancel(&BACKGROUND_CONTEXT);
        let cancelled = waiters.add(1, &cx);
        let other = waiters.add(2, &BACKGROUND_CONTEXT);
        assert_eq!(waiters.keys(), vec![1, 2]);
        cancel.cancel(None);
        assert!(matches!(cancelled.await, Err(SessionError::Aborted(_))));
        waiters.resolve(&1, &"done");
        assert_eq!(first.await.ok(), Some("done"));
        assert_eq!(waiters.keys(), vec![2]);
        waiters.reject_all(&closed_error());
        assert_eq!(
            other.await.err().map(|error| error.to_string()),
            Some("Harness is closed".to_owned())
        );
        assert!(waiters.keys().is_empty());
    }
}
