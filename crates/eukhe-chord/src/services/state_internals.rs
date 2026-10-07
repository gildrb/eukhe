//! The exact publication stream behind every authoritative replicated state.
//!
//! TS registers it in a `WeakMap` keyed by the state object so that a
//! provider can find it on an implementation's members
//! (`getReplicatedStateInternals`). Rust states expose it explicitly as a
//! [`ReplicatedStateRef`].

use std::fmt;
use std::sync::Arc;

use crate::callback::Disposer;
use crate::context::Context;
use crate::delta::Op;
use crate::error::{BoxError, ChordError};
use crate::json::JsonValue;
use crate::types::ReplicatedState;

/// An exact source listener: `(ops, sequence, context)`. A failure is
/// collected by the publisher and returned to the committing caller.
pub(crate) type SourceListener =
    Arc<dyn Fn(&Arc<[Op]>, u64, &Context) -> Result<(), ChordError> + Send + Sync>;

/// One atomically captured publication: the immutable value and the
/// sequence that produced it.
#[derive(Clone, Debug, PartialEq)]
pub struct ReplicatedStateSnapshot {
    /// The immutable value.
    pub value: JsonValue,
    /// Its publication sequence.
    pub sequence: u64,
}

/// The publication stream of an authoritative replicated state.
pub(crate) trait ReplicatedStateInternals: Send + Sync {
    /// Atomically capture the immutable value and its matching publication
    /// sequence.
    fn snapshot(&self) -> ReplicatedStateSnapshot;
    /// Receive every later publication's exact operation batch.
    fn subscribe(&self, listener: SourceListener) -> Disposer;
}

/// A handle to an authoritative replicated state's exact publication stream.
///
/// A remote service exposes a state member through it. Created from a
/// [`MutableReplicatedState`](super::state::MutableReplicatedState) or an
/// [`AttachedReplicatedState`](super::state::AttachedReplicatedState); cold
/// remote replicas cannot be republished.
#[derive(Clone)]
pub struct ReplicatedStateRef {
    pub(crate) internals: Arc<dyn ReplicatedStateInternals>,
    /// The state itself, for process-local readers of an implementation.
    pub(crate) state: Arc<dyn ReplicatedState>,
}

impl ReplicatedStateRef {
    /// Atomically capture the immutable value and its publication sequence.
    #[must_use]
    pub fn snapshot(&self) -> ReplicatedStateSnapshot {
        self.internals.snapshot()
    }

    /// Receive every later publication's exact operation batch (the same
    /// `Arc` the commit produced), sequence, and context, synchronously
    /// during publication. A failure is returned to the committing caller
    /// (or reported, for attached states) after every listener ran.
    pub fn subscribe<F, E>(&self, listener: F) -> Disposer
    where
        F: Fn(&Arc<[Op]>, u64, &Context) -> Result<(), E> + Send + Sync + 'static,
        E: Into<BoxError>,
    {
        self.internals
            .subscribe(Arc::new(move |ops, sequence, context| {
                listener(ops, sequence, context).map_err(|error| ChordError::from(error.into()))
            }))
    }
}

impl fmt::Debug for ReplicatedStateRef {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ReplicatedStateRef")
            .field("snapshot", &self.internals.snapshot())
            .finish_non_exhaustive()
    }
}
