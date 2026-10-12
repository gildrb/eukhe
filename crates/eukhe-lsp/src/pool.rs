//! Started servers keyed by (server, workspace root, configuration
//! fingerprint), port of omp2 `lsp_pool.rs`: concurrent callers share one
//! startup, unrelated servers start concurrently, and a failed startup or
//! an exited server is negatively cached for the crash backoff so a broken
//! server is not respawned on every request.

use std::collections::HashMap;
use std::future::Future;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, Instant};

use parking_lot::Mutex;
use tokio::sync::Mutex as AsyncMutex;

/// Negative startup cache lifetime (omp2 `CRASH_BACKOFF`).
pub(crate) const CRASH_BACKOFF: Duration = Duration::from_mins(3);

/// Complete identity of one shareable started server.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct PoolKey {
    pub(crate) server: String,
    pub(crate) root: PathBuf,
    pub(crate) fingerprint: u64,
}

enum Entry<T> {
    Empty,
    Ready(Arc<T>),
    Failed { at: Instant, reason: String },
}

/// What a slot holds right now.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SlotState {
    Empty,
    /// A startup holds the slot.
    Starting,
    Ready,
    Failed {
        reason: String,
    },
}

/// Why no client came back.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Refused {
    /// This call's startup failed (now cached).
    Startup(String),
    /// A recent failure is cached.
    Backoff {
        retry_after: Duration,
        reason: String,
    },
}

/// The pool.
pub(crate) struct Pool<T> {
    backoff: Duration,
    entries: Mutex<HashMap<PoolKey, Arc<AsyncMutex<Entry<T>>>>>,
}

impl<T> Pool<T> {
    pub(crate) fn new(backoff: Duration) -> Self {
        Self {
            backoff,
            entries: Mutex::default(),
        }
    }

    fn slot(&self, key: &PoolKey) -> Arc<AsyncMutex<Entry<T>>> {
        Arc::clone(
            self.entries
                .lock()
                .entry(key.clone())
                .or_insert_with(|| Arc::new(AsyncMutex::new(Entry::Empty))),
        )
    }

    /// The client of `key`, running `start` at most once for concurrent
    /// callers. A ready client `exited` reports as gone is replaced by a
    /// cached failure (the crash backoff).
    pub(crate) async fn get_or_start<F, Fut>(
        &self,
        key: &PoolKey,
        exited: impl Fn(&T) -> Option<String>,
        start: F,
    ) -> Result<Arc<T>, Refused>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<T, String>>,
    {
        let slot = self.slot(key);
        let mut entry = slot.lock().await;
        if let Entry::Ready(client) = &*entry {
            match exited(client) {
                None => return Ok(Arc::clone(client)),
                Some(reason) => {
                    *entry = Entry::Failed {
                        at: Instant::now(),
                        reason,
                    };
                }
            }
        }
        if let Entry::Failed { at, reason } = &*entry {
            if at.elapsed() < self.backoff {
                return Err(Refused::Backoff {
                    retry_after: self.backoff.saturating_sub(at.elapsed()),
                    reason: reason.clone(),
                });
            }
        }
        match start().await {
            Ok(client) => {
                let client = Arc::new(client);
                *entry = Entry::Ready(Arc::clone(&client));
                Ok(client)
            }
            Err(reason) => {
                *entry = Entry::Failed {
                    at: Instant::now(),
                    reason: reason.clone(),
                };
                Err(Refused::Startup(reason))
            }
        }
    }

    /// The ready client of `key`, without starting one.
    pub(crate) fn ready(&self, key: &PoolKey) -> Option<Arc<T>> {
        let slot = self.entries.lock().get(key).cloned()?;
        let entry = slot.try_lock().ok()?;
        match &*entry {
            Entry::Ready(client) => Some(Arc::clone(client)),
            Entry::Empty | Entry::Failed { .. } => None,
        }
    }

    /// The state of `key`'s slot.
    pub(crate) fn state(&self, key: &PoolKey) -> SlotState {
        let Some(slot) = self.entries.lock().get(key).cloned() else {
            return SlotState::Empty;
        };
        let Ok(entry) = slot.try_lock() else {
            return SlotState::Starting;
        };
        match &*entry {
            Entry::Empty => SlotState::Empty,
            Entry::Ready(_) => SlotState::Ready,
            Entry::Failed { reason, .. } => SlotState::Failed {
                reason: reason.clone(),
            },
        }
    }

    /// Remove every ready client (for shutdown).
    pub(crate) fn drain(&self) -> Vec<Arc<T>> {
        let slots: Vec<_> = self.entries.lock().drain().map(|(_, slot)| slot).collect();
        slots
            .into_iter()
            .filter_map(|slot| match slot.try_lock().ok().as_deref() {
                Some(Entry::Ready(client)) => Some(Arc::clone(client)),
                Some(Entry::Empty | Entry::Failed { .. }) | None => None,
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};

    use super::*;

    fn key() -> PoolKey {
        PoolKey {
            server: "fixture".to_owned(),
            root: PathBuf::from("/workspace"),
            fingerprint: 7,
        }
    }

    #[allow(clippy::trivially_copy_pass_by_ref)] // the pool hands clients by reference
    fn alive(_: &usize) -> Option<String> {
        None
    }

    #[tokio::test]
    async fn concurrent_callers_share_one_startup() {
        let pool = Arc::new(Pool::<usize>::new(CRASH_BACKOFF));
        let calls = Arc::new(AtomicUsize::new(0));
        let mut tasks = Vec::new();
        for _ in 0..12 {
            let pool = Arc::clone(&pool);
            let calls = Arc::clone(&calls);
            tasks.push(tokio::spawn(async move {
                pool.get_or_start(&key(), alive, || async move {
                    calls.fetch_add(1, Ordering::SeqCst);
                    tokio::task::yield_now().await;
                    Ok(41)
                })
                .await
            }));
        }
        for task in tasks {
            assert_eq!(task.await.unwrap().map(|value| *value), Ok(41));
        }
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[tokio::test]
    async fn failures_and_exits_back_off() {
        let pool = Pool::<usize>::new(CRASH_BACKOFF);
        assert_eq!(
            pool.get_or_start(&key(), alive, || async { Err("boom".to_owned()) })
                .await,
            Err(Refused::Startup("boom".to_owned()))
        );
        assert!(matches!(
            pool.get_or_start(&key(), alive, || async { Ok(1) }).await,
            Err(Refused::Backoff { reason, .. }) if reason == "boom"
        ));

        let pool = Pool::<usize>::new(CRASH_BACKOFF);
        assert_eq!(
            pool.get_or_start(&key(), alive, || async { Ok(1) })
                .await
                .map(|value| *value),
            Ok(1)
        );
        assert_eq!(pool.state(&key()), SlotState::Ready);
        let crashed = |_: &usize| Some("exited".to_owned());
        assert!(matches!(
            pool.get_or_start(&key(), crashed, || async { Ok(2) }).await,
            Err(Refused::Backoff { reason, .. }) if reason == "exited"
        ));
        assert_eq!(
            pool.state(&key()),
            SlotState::Failed {
                reason: "exited".to_owned()
            }
        );

        let pool = Pool::<usize>::new(Duration::ZERO);
        assert!(pool
            .get_or_start(&key(), alive, || async { Err("boom".to_owned()) })
            .await
            .is_err());
        assert_eq!(
            pool.get_or_start(&key(), alive, || async { Ok(3) })
                .await
                .map(|value| *value),
            Ok(3)
        );
    }
}
