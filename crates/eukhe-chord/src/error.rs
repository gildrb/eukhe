//! Errors raised, rethrown, and reported by Chord services, replicated state,
//! and facets.
//!
//! TS throws `Error`, `TypeError`, `AggregateError`, and
//! `RemoteServiceError` values and rethrows application errors unchanged.
//! [`ChordError`] has one variant per TS error class plus
//! [`ChordError::External`] for application errors passed through. Messages
//! are the TS messages verbatim.

use std::error::Error as StdError;
use std::fmt;
use std::sync::Arc;

use crate::delta::{DeltaError, TrackerError};
use crate::services::errors::RemoteServiceError;

/// An error produced by application code: callbacks, listeners, remote
/// methods, and source contracts. Any error type converts into it with `?`.
pub type BoxError = Box<dyn StdError + Send + Sync + 'static>;

/// Receives isolated failures that TS passes to an `onError(error)` option.
///
/// TS reporters may throw, and Chord then rethrows the reporter failure
/// asynchronously. Rust reporters are infallible, so that path does not
/// exist.
pub type ErrorReporter = Arc<dyn Fn(ChordError) + Send + Sync>;

/// Every error Chord returns or reports.
#[derive(Clone, Debug, thiserror::Error)]
pub enum ChordError {
    /// A JS `Error` with the TS message.
    #[error("{0}")]
    Error(Arc<str>),
    /// A JS `TypeError` with the TS message.
    #[error("{0}")]
    TypeError(Arc<str>),
    /// A JS `AggregateError`.
    #[error(transparent)]
    Aggregate(#[from] AggregateError),
    /// A [`RemoteServiceError`] that may cross a service boundary.
    #[error(transparent)]
    RemoteService(#[from] RemoteServiceError),
    /// A tracker, change, or draft failure.
    #[error(transparent)]
    Tracker(#[from] TrackerError),
    /// An operation failed to validate or apply.
    #[error(transparent)]
    Delta(#[from] DeltaError),
    /// An application error (or a context abort reason) passed through
    /// unchanged, like a TS rethrow.
    #[error(transparent)]
    External(Arc<dyn StdError + Send + Sync + 'static>),
}

impl ChordError {
    /// A JS `new Error(message)`.
    #[must_use]
    pub fn error(message: impl Into<Arc<str>>) -> Self {
        Self::Error(message.into())
    }

    /// A JS `new TypeError(message)`.
    #[must_use]
    pub fn type_error(message: impl Into<Arc<str>>) -> Self {
        Self::TypeError(message.into())
    }

    /// Wrap a shared error (for example an [`crate::context::AbortReason`]),
    /// unwrapping it when it already is a [`ChordError`].
    #[must_use]
    pub fn from_shared(error: Arc<dyn StdError + Send + Sync + 'static>) -> Self {
        match error.downcast_ref::<ChordError>() {
            Some(chord) => chord.clone(),
            None => Self::External(error),
        }
    }

    /// The [`RemoteServiceError`], when this is one.
    #[must_use]
    pub fn remote_service_error(&self) -> Option<&RemoteServiceError> {
        match self {
            Self::RemoteService(error) => Some(error),
            Self::Error(_)
            | Self::TypeError(_)
            | Self::Aggregate(_)
            | Self::Tracker(_)
            | Self::Delta(_)
            | Self::External(_) => None,
        }
    }
}

impl From<BoxError> for ChordError {
    fn from(error: BoxError) -> Self {
        match error.downcast::<ChordError>() {
            Ok(chord) => *chord,
            Err(error) => Self::External(Arc::from(error)),
        }
    }
}

/// A JS `AggregateError`: one message over several collected failures.
#[derive(Clone, Debug)]
pub struct AggregateError {
    message: Arc<str>,
    errors: Arc<[ChordError]>,
}

impl AggregateError {
    /// A JS `new AggregateError(errors, message)`.
    #[must_use]
    pub fn new(errors: Vec<ChordError>, message: impl Into<Arc<str>>) -> Self {
        Self {
            message: message.into(),
            errors: errors.into(),
        }
    }

    /// The collected failures (`AggregateError.errors`).
    #[must_use]
    pub fn errors(&self) -> &[ChordError] {
        &self.errors
    }

    /// The message.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for AggregateError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl StdError for AggregateError {}

/// TS `throwCollectedErrors`: nothing, the single failure, or an aggregate.
pub(crate) fn collected(mut errors: Vec<ChordError>, message: &str) -> Result<(), ChordError> {
    match errors.len() {
        0 => Ok(()),
        1 => Err(errors.remove(0)),
        _ => Err(AggregateError::new(errors, message).into()),
    }
}

/// TS `reportErrorAsync`: an uncaught failure without an `onError` option.
///
/// TS rethrows it from a microtask, which makes it a process-level uncaught
/// exception. Rust logs it at error level instead of aborting the process.
pub(crate) fn report_uncaught(error: &ChordError) {
    #[cfg(test)]
    if crate::tests::capture_uncaught(error) {
        return;
    }
    tracing::error!(error = %error, "uncaught Chord error");
}

/// The default reporter: [`report_uncaught`].
pub(crate) fn uncaught_reporter() -> ErrorReporter {
    Arc::new(|error| report_uncaught(&error))
}
