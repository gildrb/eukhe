//! Immutable revision tracking with overlay drafts (`delta/tracker.ts`):
//! [`Tracker`], [`Change`], [`Prepared`].

mod emit;
mod mutators;
mod ordered;
pub(crate) mod overlay;
mod pieces;
#[cfg(test)]
mod retention_tests;

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, Weak};

use overlay::{ContextState, Status};

use super::apply::{apply_immutable, apply_immutable_trusted};
use super::draft::Draft;
use super::ops::{DeltaError, Op};
use crate::json::JsonValue;

/// Tracker, change, and draft failures. Messages are the TS messages.
#[derive(Clone, Debug, PartialEq, thiserror::Error)]
pub enum TrackerError {
    /// The draft's change was prepared, aborted, adopted, or made stale.
    #[error("Cannot use a settled overlay")]
    SettledOverlay,
    /// A write while the change is being prepared.
    #[error("Prepared overlays are read-only")]
    PreparedReadOnly,
    /// `prepare()` after `prepare()` or `abort()`.
    #[error("Change has already been settled")]
    ChangeSettled,
    /// `adopt()` of another tracker's preparation.
    #[error("Prepared change belongs to a different tracker")]
    DifferentTracker,
    /// `adopt()` of an adopted preparation.
    #[error("Prepared change has already been used")]
    AlreadyUsed,
    /// `adopt()` of an aborted preparation.
    #[error("Prepared change has been aborted")]
    Aborted,
    /// `adopt()` of a preparation from an older revision.
    #[error("Prepared change is stale")]
    Stale,
    /// `adopt()` of a preparation that is not prepared.
    #[error("Prepared change is not ready")]
    NotReady,
    /// Writing past the next array index, or deleting an element.
    #[error("Overlay arrays cannot contain holes")]
    ArrayHoles,
    /// A `length` that is not an integer in `[0, 2^32)` (TS `RangeError`).
    #[error("Invalid array length")]
    InvalidArrayLength,
    /// A non-index, non-`length` key written on an array.
    #[error("Only array indices and length can be written")]
    OnlyIndicesAndLength,
    /// An array mutator on an object draft.
    #[error("Array mutator called on incompatible receiver")]
    IncompatibleReceiver,
    /// An internal piece-table lookup failed (TS `RangeError`).
    #[error("Array overlay index is out of range")]
    OverlayIndexOutOfRange,
    /// [`Draft::child`] of a key holding no object or array (Rust
    /// convenience; TS would read `undefined` or a primitive).
    #[error("Draft property {0} is not an object or array")]
    NotAContainer(String),
    /// A tracked or replacement root that is not an object or array (the TS
    /// type constraint `T extends object`).
    #[error("Tracked values must be objects or arrays")]
    RootNotContainer,
    /// Materializing the candidate failed.
    #[error(transparent)]
    Delta(#[from] DeltaError),
}

/// One change's overlay context, shared by its [`Change`], [`Prepared`], and
/// [`Draft`] handles.
#[derive(Debug)]
pub(crate) struct ContextCell {
    state: Mutex<ContextState>,
}

impl ContextCell {
    pub(crate) fn lock(&self) -> MutexGuard<'_, ContextState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

static NEXT_TRACKER_ID: AtomicU64 = AtomicU64::new(1);

#[derive(Debug)]
struct TrackerState {
    value: JsonValue,
    revision: u64,
    contexts: Vec<Weak<ContextCell>>,
    prune_budget: usize,
}

#[derive(Debug)]
struct TrackerInner {
    id: u64,
    state: Mutex<TrackerState>,
}

/// One revision sequence of an immutable JSON root.
///
/// ```
/// use eukhe_chord::delta::track;
/// use eukhe_chord::json::JsonValue;
/// let tracker = track(JsonValue::parse(r#"{"count":1}"#).unwrap()).unwrap();
/// let change = tracker.begin_change();
/// change.state().unwrap().set("count", 2).unwrap();
/// let prepared = change.prepare().unwrap();
/// tracker.adopt(&prepared).unwrap();
/// assert_eq!(tracker.value().to_string(), r#"{"count":2}"#);
/// assert_eq!(tracker.revision(), 1);
/// ```
#[derive(Clone, Debug)]
pub struct Tracker {
    inner: Arc<TrackerInner>,
}

/// Take immutable ownership of a JSON root in O(1) (`track`). The root must
/// be an object or array.
///
/// # Errors
///
/// The TS lifecycle errors listed on [`TrackerError`].
pub fn track(initial: JsonValue) -> Result<Tracker, TrackerError> {
    if !initial.is_container() {
        return Err(TrackerError::RootNotContainer);
    }
    Ok(Tracker {
        inner: Arc::new(TrackerInner {
            id: NEXT_TRACKER_ID.fetch_add(1, Ordering::Relaxed),
            state: Mutex::new(TrackerState {
                value: initial,
                revision: 0,
                contexts: Vec::new(),
                prune_budget: 256,
            }),
        }),
    })
}

impl Tracker {
    fn lock(&self) -> MutexGuard<'_, TrackerState> {
        self.inner
            .state
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    /// The latest adopted revision.
    #[must_use]
    pub fn value(&self) -> JsonValue {
        self.lock().value.clone()
    }

    /// Number of adoptions so far.
    #[must_use]
    pub fn revision(&self) -> u64 {
        self.lock().revision
    }

    /// Open an overlay draft over the current revision.
    #[must_use]
    pub fn begin_change(&self) -> Change {
        let mut tracker = self.lock();
        let value = tracker.value.clone();
        let state = ContextState::new(self.inner.id, tracker.revision, value.clone(), false, value);
        let cell = register(&mut tracker, state);
        Change {
            inner: Arc::new(Mutex::new(ChangeState {
                context: Some(cell),
                prepared_status: None,
                settled: false,
            })),
        }
    }

    /// Prepare a whole-root replacement. Takes `value` in O(1); a deeply equal
    /// value yields empty ops and keeps the current root.
    ///
    /// # Errors
    ///
    /// The TS lifecycle errors listed on [`TrackerError`].
    pub fn prepare_replace(&self, value: JsonValue) -> Result<Prepared, TrackerError> {
        if !value.is_container() {
            return Err(TrackerError::RootNotContainer);
        }
        let mut tracker = self.lock();
        let current = tracker.value.clone();
        let mut state = ContextState::new(
            self.inner.id,
            tracker.revision,
            value,
            true,
            current.clone(),
        );
        state.status = Status::Prepared;
        let cell = register(&mut tracker, state);
        let mut state = cell.lock();
        match materialize_prepared(&cell, &mut state, Some(&current)) {
            Ok(prepared) => Ok(prepared),
            Err(error) => {
                state.status = Status::Aborted;
                state.release();
                Err(error)
            }
        }
    }

    /// Adopt a preparation: an infallible pointer swap after the checks.
    /// Every competing open or prepared change becomes stale.
    ///
    /// # Errors
    ///
    /// The TS lifecycle errors listed on [`TrackerError`].
    pub fn adopt(&self, prepared: &Prepared) -> Result<(), TrackerError> {
        let mut tracker = self.lock();
        let cell = &prepared.inner.context;
        {
            let mut state = cell.lock();
            if state.owner != self.inner.id {
                return Err(TrackerError::DifferentTracker);
            }
            match state.status {
                Status::Consumed => return Err(TrackerError::AlreadyUsed),
                Status::Aborted => return Err(TrackerError::Aborted),
                Status::Stale => return Err(TrackerError::Stale),
                Status::Open => return Err(TrackerError::NotReady),
                Status::Prepared => {}
            }
            if state.base_revision != tracker.revision {
                state.status = Status::Stale;
                state.release();
                return Err(TrackerError::Stale);
            }
            if !tracker.value.strict_equals(&prepared.inner.base) {
                state.status = Status::Stale;
                return Err(TrackerError::Stale);
            }
            tracker.value = prepared.inner.value.clone();
            state.status = Status::Consumed;
        }
        tracker.revision += 1;
        invalidate(&mut tracker, cell);
        Ok(())
    }

    /// Live registered contexts (for retention tests).
    #[cfg(test)]
    pub(crate) fn registered_contexts(&self) -> usize {
        self.lock()
            .contexts
            .iter()
            .filter(|weak| weak.strong_count() > 0)
            .count()
    }
}

fn register(tracker: &mut TrackerState, mut state: ContextState) -> Arc<ContextCell> {
    state.registered = true;
    let cell = Arc::new(ContextCell {
        state: Mutex::new(state),
    });
    tracker.contexts.push(Arc::downgrade(&cell));
    tracker.prune_budget -= 1;
    if tracker.prune_budget == 0 {
        tracker.contexts.retain(|weak| {
            weak.upgrade()
                .is_some_and(|context| context.lock().registered)
        });
        tracker.prune_budget = tracker.contexts.len().max(256);
    }
    cell
}

/// Stale every competitor and drop its overlay in O(1) per context.
fn invalidate(tracker: &mut TrackerState, winner: &Arc<ContextCell>) {
    for weak in std::mem::take(&mut tracker.contexts) {
        let Some(context) = weak.upgrade() else {
            continue;
        };
        if Arc::ptr_eq(&context, winner) {
            continue;
        }
        let mut state = context.lock();
        if !state.registered {
            continue;
        }
        if matches!(state.status, Status::Open | Status::Prepared) {
            state.status = Status::Stale;
        }
        state.release();
    }
    tracker.prune_budget = 256;
}

fn abort_context(state: &mut ContextState) {
    if matches!(
        state.status,
        Status::Aborted | Status::Consumed | Status::Stale
    ) {
        return;
    }
    state.status = Status::Aborted;
    state.release();
}

fn ensure_operations(
    state: &mut ContextState,
    replacement_base: Option<&JsonValue>,
) -> Result<Arc<Vec<Op>>, TrackerError> {
    if let Some(ops) = &state.ops {
        return Ok(Arc::clone(ops));
    }
    state.assert_readable()?;
    let ops = if state.replacement {
        let root = state
            .root
            .map(|root| state.nodes[root].base.clone())
            .unwrap_or_default();
        let noop = replacement_base.is_some_and(|base| *base == root);
        if noop {
            Vec::new()
        } else {
            vec![Op::Replace(root)]
        }
    } else {
        state.emit_operations()
    };
    let ops = Arc::new(ops);
    state.ops = Some(Arc::clone(&ops));
    Ok(ops)
}

fn materialize_prepared(
    cell: &Arc<ContextCell>,
    state: &mut ContextState,
    replacement_base: Option<&JsonValue>,
) -> Result<Prepared, TrackerError> {
    let ops = ensure_operations(state, replacement_base)?;
    let base = state.base_value.clone().unwrap_or_default();
    // Payloads are detached from the overlay; the candidate shares them.
    let value = if ops.is_empty() {
        base.clone()
    } else if state.simple_object_materialization {
        match state.root {
            Some(root) => state.clone_node(root),
            None => return Err(TrackerError::SettledOverlay),
        }
    } else if ops
        .iter()
        .any(|op| matches!(op, Op::Splice(..) | Op::Move(..)))
    {
        apply_immutable(&base, &ops)?
    } else {
        apply_immutable_trusted(&base, &ops)?
    };
    let prepared = Prepared {
        inner: Arc::new(PreparedInner {
            context: Arc::clone(cell),
            base,
            value,
            ops,
            base_revision: state.base_revision,
        }),
    };
    state.release();
    Ok(prepared)
}

#[derive(Debug)]
struct ChangeState {
    context: Option<Arc<ContextCell>>,
    /// The settled context, kept only to abort its preparation.
    prepared_status: Option<Arc<ContextCell>>,
    settled: bool,
}

/// An open overlay draft over one revision (`Change`). Settle it with
/// [`Change::prepare`] or [`Change::abort`].
///
/// ```
/// use eukhe_chord::delta::track;
/// use eukhe_chord::json::JsonValue;
/// let tracker = track(JsonValue::parse(r#"{"values":[3,1,2]}"#).unwrap()).unwrap();
/// let change = tracker.begin_change();
/// change.state().unwrap().child("values").unwrap().sort().unwrap();
/// let prepared = change.prepare().unwrap();
/// assert_eq!(prepared.value().to_string(), r#"{"values":[1,2,3]}"#);
/// assert!(change.state().is_err()); // settled
/// ```
#[derive(Clone, Debug)]
pub struct Change {
    inner: Arc<Mutex<ChangeState>>,
}

impl Change {
    fn lock(&self) -> MutexGuard<'_, ChangeState> {
        self.inner.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// The root draft (`change.state`).
    ///
    /// # Errors
    ///
    /// The TS lifecycle errors listed on [`TrackerError`].
    pub fn state(&self) -> Result<Draft, TrackerError> {
        let change = self.lock();
        let Some(cell) = change.context.as_ref() else {
            return Err(TrackerError::SettledOverlay);
        };
        let state = cell.lock();
        match state.root {
            Some(root) => Ok(Draft::new(Arc::clone(cell), root, state.is_array(root))),
            None => Err(TrackerError::SettledOverlay),
        }
    }

    /// Materialize the candidate and its ops without changing authority.
    /// Draft handles are unusable afterwards.
    ///
    /// # Errors
    ///
    /// The TS lifecycle errors listed on [`TrackerError`].
    pub fn prepare(&self) -> Result<Prepared, TrackerError> {
        let mut change = self.lock();
        if change.settled {
            return Err(TrackerError::ChangeSettled);
        }
        let Some(cell) = change.context.clone() else {
            return Err(TrackerError::ChangeSettled);
        };
        let mut state = cell.lock();
        state.assert_writable()?;
        state.status = Status::Prepared;
        if !state.replacement {
            let ops = if state.dirty.is_empty() {
                Vec::new()
            } else {
                state.emit_operations()
            };
            state.ops = Some(Arc::new(ops));
        }
        let result = materialize_prepared(&cell, &mut state, None);
        change.context = None;
        change.settled = true;
        match result {
            Ok(prepared) => {
                drop(state);
                change.prepared_status = Some(cell);
                Ok(prepared)
            }
            Err(error) => {
                state.status = Status::Aborted;
                state.release();
                Err(error)
            }
        }
    }

    /// Abort: revoke the draft, or stop a preparation from being adopted.
    /// Idempotent.
    pub fn abort(&self) {
        let mut change = self.lock();
        if change.settled {
            if let Some(cell) = change.prepared_status.take() {
                let mut state = cell.lock();
                if state.status == Status::Prepared {
                    state.status = Status::Aborted;
                }
            }
            return;
        }
        change.settled = true;
        if let Some(cell) = change.context.take() {
            abort_context(&mut cell.lock());
        }
    }
}

#[derive(Debug)]
struct PreparedInner {
    context: Arc<ContextCell>,
    base: JsonValue,
    value: JsonValue,
    ops: Arc<Vec<Op>>,
    base_revision: u64,
}

/// A materialized candidate revision and its exact op batch (`Prepared`).
/// `ops` is empty exactly when `value` is `base`.
#[derive(Clone, Debug)]
pub struct Prepared {
    inner: Arc<PreparedInner>,
}

impl Prepared {
    /// The revision the change started from.
    #[must_use]
    pub fn base(&self) -> &JsonValue {
        &self.inner.base
    }

    /// The candidate revision.
    #[must_use]
    pub fn value(&self) -> &JsonValue {
        &self.inner.value
    }

    /// The ops turning `base` into `value`.
    #[must_use]
    pub fn ops(&self) -> &[Op] {
        &self.inner.ops
    }

    /// The tracker revision of `base`.
    #[must_use]
    pub fn base_revision(&self) -> u64 {
        self.inner.base_revision
    }

    /// Prevent adoption. The candidate stays readable. Idempotent.
    pub fn abort(&self) {
        abort_context(&mut self.inner.context.lock());
    }
}
