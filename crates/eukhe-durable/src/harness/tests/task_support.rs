//! Port of `test/task-support.ts`: deferred values, cancellation helpers,
//! flush-driven polling, a Harness over a registry holding test tasks, and a
//! registry reader that counts its subscriptions.

use std::future::Future;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::AbortSignal;
use tokio::sync::watch;

use crate::harness::define::define_extension;
use crate::harness::registry::Registry;
use crate::harness::types::{
    Clock, Extension, HarnessOptions, HarnessSettingsSource, RegistryReader, RegistrySnapshot,
    ReportFn,
};
use crate::harness::Harness;
use crate::session::{SessionError, Unsubscribe};
use crate::tasks::{AnyTask, NextTaskState};
use crate::types::{Storage, TaskOutcome};

pub(crate) use crate::session::tests::support::flush;

use super::support::{context, create_models, create_registry};

/// A value that resolves once (TS `deferred()`); clones share it.
#[derive(Clone)]
pub(crate) struct Deferred<T: Clone + Send + Sync + 'static = ()> {
    sender: Arc<watch::Sender<Option<T>>>,
}

impl<T: Clone + Send + Sync + 'static> Deferred<T> {
    /// Settle with `value`; later calls are ignored, like a promise.
    pub(crate) fn resolve(&self, value: T) {
        self.sender.send_if_modified(|current| {
            if current.is_some() {
                return false;
            }
            *current = Some(value);
            true
        });
    }

    /// Resolves with the value once settled.
    pub(crate) fn wait(&self) -> impl Future<Output = T> + Send + 'static {
        let mut receiver = self.sender.subscribe();
        async move {
            loop {
                if let Some(value) = receiver.borrow_and_update().clone() {
                    return value;
                }
                // The sender lives in the deferred, which the test keeps.
                if receiver.changed().await.is_err() {
                    return std::future::pending().await;
                }
            }
        }
    }

    /// Whether it has settled.
    pub(crate) fn is_settled(&self) -> bool {
        self.sender.borrow().is_some()
    }
}

/// A fresh unsettled value.
pub(crate) fn deferred<T: Clone + Send + Sync + 'static>() -> Deferred<T> {
    Deferred {
        sender: Arc::new(watch::channel(None).0),
    }
}

/// Resolve with the signal's reason once it aborts, as the error a handler
/// that blocks until cancelled fails with.
pub(crate) async fn aborted(signal: &AbortSignal) -> SessionError {
    SessionError::Aborted(signal.cancelled().await)
}

/// Flush pending work until `check` holds.
///
/// TS flushes 200 times; its storages answer on the event loop, so that
/// bound is deterministic. The native SQLite storage answers from its own
/// thread, which flushes do not wait for, so the bound here is a generous
/// deadline instead of a flush count: a condition that holds is reached
/// as soon as the work it depends on is done, however loaded the machine.
///
/// # Panics
///
/// `Condition was not reached` after the deadline.
pub(crate) async fn eventually<F, Fut>(mut check: F)
where
    F: FnMut() -> Fut,
    Fut: Future<Output = bool>,
{
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(30);
    while !check().await {
        assert!(
            std::time::Instant::now() <= deadline,
            "Condition was not reached"
        );
        flush().await;
    }
}

/// Whether a spawned operation has settled after pending work flushes.
pub(crate) async fn settled<T>(handle: &tokio::task::JoinHandle<T>) -> bool {
    flush().await;
    handle.is_finished()
}

/// Failures a Harness passed to `on_report`, in order.
#[derive(Clone, Default)]
pub(crate) struct Reports(Arc<Mutex<Vec<SessionError>>>);

impl Reports {
    /// The `on_report` callback that collects into this list.
    pub(crate) fn sink(&self) -> ReportFn {
        let reports = Arc::clone(&self.0);
        Arc::new(move |error| {
            reports
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .push(error);
        })
    }

    /// The reports so far.
    pub(crate) fn all(&self) -> Vec<SessionError> {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    pub(crate) fn len(&self) -> usize {
        self.0.lock().unwrap_or_else(PoisonError::into_inner).len()
    }
}

/// Options of [`open_tasks`].
#[derive(Default)]
pub(crate) struct OpenTasksOptions {
    pub(crate) registry: Option<Registry>,
    pub(crate) now: Option<Clock>,
    pub(crate) settings: Option<Arc<dyn HarnessSettingsSource>>,
}

/// A Harness opened by [`open_tasks`], its registry, and its reports.
pub(crate) struct OpenedTasks {
    pub(crate) harness: Harness,
    pub(crate) registry: Registry,
    pub(crate) reports: Reports,
}

/// Open a Harness whose registry holds `tasks`; failures passed to
/// `on_report` are collected.
///
/// # Panics
///
/// The registry rejects the tasks or the Harness fails to open.
pub(crate) async fn open_tasks(
    storage: Arc<dyn Storage>,
    tasks: &[AnyTask],
    options: OpenTasksOptions,
) -> OpenedTasks {
    let registry = options.registry.unwrap_or_else(create_registry);
    if !tasks.is_empty() {
        registry
            .install(define_extension(Extension {
                name: "tasks".to_owned(),
                tasks: tasks.to_vec(),
                ..Extension::default()
            }))
            .expect("install the test tasks");
    }
    let reports = Reports::default();
    let mut harness_options = HarnessOptions::new(create_models(), Arc::new(registry.clone()));
    harness_options.on_report = Some(reports.sink());
    harness_options.now = options.now;
    harness_options.settings = options.settings;
    let harness = Harness::open(storage, harness_options, context())
        .await
        .expect("open the Harness");
    OpenedTasks {
        harness,
        registry,
        reports,
    }
}

/// Next state that completes a task with `result`.
pub(crate) fn completed<S, R>(result: R) -> NextTaskState<S, R> {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Completed { result },
    }
}

/// Next state that aborts a task.
pub(crate) fn aborted_with<S, R>(reason: &str) -> NextTaskState<S, R> {
    NextTaskState::Terminal {
        outcome: TaskOutcome::Aborted {
            reason: Some(reason.to_owned()),
            result: None,
        },
    }
}

/// Registry reader that counts live subscriptions.
pub(crate) struct CountingReader {
    registry: Registry,
    count: Arc<AtomicUsize>,
}

impl CountingReader {
    pub(crate) fn new(registry: Registry) -> Self {
        Self {
            registry,
            count: Arc::default(),
        }
    }

    pub(crate) fn subscriptions(&self) -> usize {
        self.count.load(Ordering::SeqCst)
    }
}

impl RegistryReader for CountingReader {
    fn snapshot(&self) -> RegistrySnapshot {
        self.registry.snapshot()
    }

    fn subscribe(&self, listener: Arc<dyn Fn() + Send + Sync>) -> Unsubscribe {
        self.count.fetch_add(1, Ordering::SeqCst);
        let unsubscribe = self.registry.subscribe(listener);
        let count = Arc::clone(&self.count);
        let active = Mutex::new(true);
        Unsubscribe::new(move || {
            let mut active = active.lock().unwrap_or_else(PoisonError::into_inner);
            if !*active {
                return false;
            }
            *active = false;
            count.fetch_sub(1, Ordering::SeqCst);
            unsubscribe.unsubscribe()
        })
    }
}
