//! Ports of the chord package's service, state, and facet tests, with the
//! shared test helpers.

use std::cell::RefCell;
use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};

use futures::future::Shared;
use futures::FutureExt;
use tokio::sync::oneshot;

use crate::delta::Op;
use crate::error::ChordError;
use crate::json::JsonValue;

mod boundary;
mod facet_loader;
mod facets;
mod json;
mod service_delivery;
mod service_wire;
mod services;
mod state;
mod state_delivery;
mod state_diff;
mod state_draft;
mod state_fuzz;
mod state_value;

thread_local! {
    static UNCAUGHT: RefCell<Option<Vec<ChordError>>> = const { RefCell::new(None) };
}

/// Capture uncaught errors reported on this thread (the TS tests spy on
/// `queueMicrotask`). Returns whether the error was captured.
pub(crate) fn capture_uncaught(error: &ChordError) -> bool {
    UNCAUGHT.with(|captured| match captured.borrow_mut().as_mut() {
        Some(errors) => {
            errors.push(error.clone());
            true
        }
        None => false,
    })
}

/// Start capturing uncaught errors reported on this thread.
pub(crate) fn start_capturing_uncaught() {
    UNCAUGHT.with(|captured| *captured.borrow_mut() = Some(Vec::new()));
}

/// Stop capturing and return the captured errors.
pub(crate) fn take_uncaught() -> Vec<ChordError> {
    UNCAUGHT.with(|captured| captured.borrow_mut().take().unwrap_or_default())
}

/// A JSON literal.
pub(crate) fn json(value: serde_json::Value) -> JsonValue {
    JsonValue::from(value)
}

/// Operations as their JSON tuples.
pub(crate) fn ops_json(ops: &[Op]) -> JsonValue {
    ops.iter().map(Op::to_json).collect()
}

/// A shared list that callbacks append to.
pub(crate) struct Recorder<T>(Arc<Mutex<Vec<T>>>);

impl<T> Clone for Recorder<T> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl<T> Default for Recorder<T> {
    fn default() -> Self {
        Self(Arc::new(Mutex::new(Vec::new())))
    }
}

impl<T: Clone> Recorder<T> {
    pub(crate) fn push(&self, value: T) {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(value);
    }

    pub(crate) fn get(&self) -> Vec<T> {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    pub(crate) fn len(&self) -> usize {
        self.0.lock().unwrap_or_else(PoisonError::into_inner).len()
    }
}

type Settlement = Result<(), ChordError>;

/// A TS `deferred()`: a promise settled from the outside.
#[derive(Clone)]
pub(crate) struct Gate {
    sender: Arc<Mutex<Option<oneshot::Sender<Settlement>>>>,
    receiver: Shared<oneshot::Receiver<Settlement>>,
}

impl Gate {
    pub(crate) fn new() -> Self {
        let (sender, receiver) = oneshot::channel();
        Self {
            sender: Arc::new(Mutex::new(Some(sender))),
            receiver: receiver.shared(),
        }
    }

    fn settle(&self, result: Result<(), ChordError>) {
        let sender = self
            .sender
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take();
        if let Some(sender) = sender {
            drop(sender.send(result));
        }
    }

    pub(crate) fn resolve(&self) {
        self.settle(Ok(()));
    }

    pub(crate) fn reject(&self, error: ChordError) {
        self.settle(Err(error));
    }

    /// The promise.
    pub(crate) fn wait(&self) -> impl Future<Output = Result<(), ChordError>> + Send + 'static {
        let receiver = self.receiver.clone();
        async move {
            match receiver.await {
                Ok(result) => result,
                Err(_) => Err(ChordError::error("gate dropped")),
            }
        }
    }
}

/// TS `vi.waitFor`: yield to spawned tasks until `condition` holds.
pub(crate) async fn wait_for(condition: impl Fn() -> bool) {
    for _ in 0..10_000 {
        if condition() {
            return;
        }
        tokio::task::yield_now().await;
    }
    assert!(condition(), "condition was not met");
}
