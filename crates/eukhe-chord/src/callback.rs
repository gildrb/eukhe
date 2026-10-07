//! Callback results and disposers shared by replicated state, services, and
//! facets.
//!
//! TS callbacks typed `() => void | Promise<void>` may finish synchronously,
//! throw synchronously, or return a promise. [`Outcome`] keeps those three
//! cases apart because Chord treats them differently: synchronous listeners
//! run inline during publication, while a returned promise suspends a
//! subscription queue until it settles.

use std::fmt;
use std::future::Future;
use std::sync::{Arc, Mutex, PoisonError};

use futures::future::BoxFuture;
use futures::FutureExt;

use crate::error::{BoxError, ChordError};

/// What a callback produced.
pub enum Outcome {
    /// It returned synchronously.
    Done,
    /// It threw synchronously.
    Failed(ChordError),
    /// It returned a promise. Chord awaits it on a spawned Tokio task, so
    /// callbacks returning this must run inside a Tokio runtime.
    Pending(BoxFuture<'static, Result<(), ChordError>>),
}

impl Outcome {
    /// A promise-returning callback result.
    pub fn pending<F, E>(future: F) -> Self
    where
        F: Future<Output = Result<(), E>> + Send + 'static,
        E: Into<BoxError>,
    {
        Self::Pending(
            future
                .map(|result| result.map_err(|error| ChordError::from(error.into())))
                .boxed(),
        )
    }

    /// A synchronous failure.
    pub fn failed(error: impl Into<BoxError>) -> Self {
        Self::Failed(ChordError::from(error.into()))
    }
}

impl fmt::Debug for Outcome {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Done => formatter.write_str("Done"),
            Self::Failed(error) => formatter.debug_tuple("Failed").field(error).finish(),
            Self::Pending(_) => formatter.write_str("Pending"),
        }
    }
}

impl From<()> for Outcome {
    fn from((): ()) -> Self {
        Self::Done
    }
}

impl<E: Into<BoxError>> From<Result<(), E>> for Outcome {
    fn from(result: Result<(), E>) -> Self {
        match result {
            Ok(()) => Self::Done,
            Err(error) => Self::failed(error),
        }
    }
}

/// A TS `() => void` returned by `subscribe`, `observe`, and `spawn`.
/// Calling it more than once is harmless.
#[derive(Clone)]
pub struct Disposer {
    dispose: Arc<dyn Fn() + Send + Sync>,
}

impl Disposer {
    /// Wrap an idempotent disposal function.
    pub fn new(dispose: impl Fn() + Send + Sync + 'static) -> Self {
        Self {
            dispose: Arc::new(dispose),
        }
    }

    /// Wrap a one-shot disposal function; later calls do nothing.
    pub fn once(dispose: impl FnOnce() + Send + 'static) -> Self {
        let slot = Mutex::new(Some(dispose));
        Self::new(move || {
            let dispose = slot.lock().unwrap_or_else(PoisonError::into_inner).take();
            if let Some(dispose) = dispose {
                dispose();
            }
        })
    }

    /// Run the disposal.
    pub fn dispose(&self) {
        (self.dispose)();
    }
}

impl fmt::Debug for Disposer {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("Disposer")
    }
}

/// A TS `() => void` that may throw: the close function returned by
/// `spawn`. Calling it more than once is harmless.
#[derive(Clone)]
pub struct Closer {
    close: Arc<dyn Fn() -> Result<(), ChordError> + Send + Sync>,
}

impl Closer {
    /// Wrap an idempotent close function.
    pub fn new(close: impl Fn() -> Result<(), ChordError> + Send + Sync + 'static) -> Self {
        Self {
            close: Arc::new(close),
        }
    }

    /// Close.
    ///
    /// # Errors
    ///
    /// Failures publishing the closure.
    pub fn close(&self) -> Result<(), ChordError> {
        (self.close)()
    }
}

impl fmt::Debug for Closer {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("Closer")
    }
}

/// An asynchronous TS callback `() => void | Promise<void>` run at most once.
pub type AsyncCallback = Box<dyn FnOnce() -> Outcome + Send>;

/// Run an [`AsyncCallback`]-style outcome to completion (TS `await callback()`).
pub(crate) async fn settle(outcome: Outcome) -> Result<(), ChordError> {
    match outcome {
        Outcome::Done => Ok(()),
        Outcome::Failed(error) => Err(error),
        Outcome::Pending(future) => future.await,
    }
}
