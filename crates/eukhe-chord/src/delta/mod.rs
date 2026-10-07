//! Chord Delta: immutable JSON revisions and exact operation batches for
//! ordered replicas (port of `@earendil-works/chord/delta`).
//!
//! ```
//! use eukhe_chord::delta::{apply_immutable, track, Op};
//! use eukhe_chord::json::JsonValue;
//!
//! let tracker = track(JsonValue::parse(r#"{"output":"","entries":[]}"#).unwrap()).unwrap();
//! let change = tracker.begin_change();
//! let state = change.state().unwrap();
//! state.set("output", "done\n").unwrap();
//! state.child("entries").unwrap().push([JsonValue::parse(r#"{"id":1}"#).unwrap()]).unwrap();
//! let prepared = change.prepare().unwrap(); // draft handles are unusable from here on
//! assert_eq!(prepared.ops()[0], Op::Append(vec!["output".into()], "done\n".into()));
//! tracker.adopt(&prepared).unwrap();
//! assert!(tracker.value().strict_equals(prepared.value()));
//! let replica = apply_immutable(prepared.base(), prepared.ops()).unwrap();
//! assert_eq!(&replica, prepared.value());
//! ```
//!
//! # Ownership
//!
//! [`JsonValue`](crate::json::JsonValue) is immutable and `Arc`-shared, so the
//! TS mutation-rights table holds by construction: trackers, prepared
//! revisions, op payloads, and replicas share containers without any of them
//! being able to change another. Placing a value into a draft stores a fresh
//! alias-free copy; placing a [`Draft`] handle copies its current content.
//!
//! # Lifecycle
//!
//! [`Tracker::value`] is the latest adopted revision.
//! [`Tracker::begin_change`] opens an overlay draft over it.
//! [`Change::prepare`] materializes the candidate and ops without changing
//! authority; [`Tracker::adopt`] checks the preparation and swaps the root.
//! Adopting one change makes every competitor stale. Empty ops mean
//! `prepared.value()` is `prepared.base()`.
//!
//! # Operations
//!
//! | Tuple | [`Op`] | Meaning |
//! | --- | --- | --- |
//! | `["r", value]` | [`Op::Replace`] | Replace the complete value. |
//! | `["s", path, value]` | [`Op::Set`] | Set an object property or array element. |
//! | `["d", path]` | [`Op::Delete`] | Delete a property or remove an element. |
//! | `["a", path, text]` | [`Op::Append`] | Append to a string. |
//! | `["t", path, count]` | [`Op::Truncate`] | Remove `count` UTF-16 code units from a string's front. |
//! | `["p", path, index, remove, items]` | [`Op::Splice`] | Splice an array. |
//! | `["m", path, permutation]` | [`Op::Move`] | Reorder: `new[i] = old[permutation[i]]`. |
//!
//! Batches are exact but not canonical. The tracker never emits the
//! [`RESERVED_SEGMENTS`] as path segments; appliers and the decoder reject
//! them with [`UnsafePathError`].
//!
//! # Rust mapping notes
//!
//! - JS proxies become [`Draft`] handles with one method per proxy operation.
//! - `JsonRevisionValidator` (`revision-validator.ts`) has no runtime
//!   counterpart: every invariant it checks (finite numbers, dense plain
//!   containers, string keys, acyclic, no `undefined`) is enforced by the
//!   `JsonValue` type itself.
//! - A TS `undefined` applier target maps to `JsonValue::Null` (see [`apply`]).

mod apply;
mod codec;
mod diff;
mod draft;
mod ops;
mod overlap;
mod tracker;

pub use apply::{
    apply, apply_immutable, apply_immutable_batches, try_apply_immutable_batches, BatchError,
};
pub use codec::{decoder, encoder, Decoder, Encoder};
pub use diff::diff_revisions;
pub use draft::{Draft, DraftItem, Placement};
pub use ops::{
    assert_safe_json_path, assert_safe_path, assert_valid_op, assert_valid_wire_op,
    is_reserved_segment, path_json, DeltaError, Op, Path, PathError, Seg, UnresolvedPath,
    UnsafePathError, WireOp, WirePath, RESERVED_SEGMENTS,
};
pub use overlap::{overlap, overlap_with, DEFAULT_OVERLAP_CANDIDATES, DEFAULT_OVERLAP_PROBE};
pub use tracker::{track, Change, Prepared, Tracker, TrackerError};

/// Whether a batch begins with a replacement (`isBase`). Flush guarantees `r`
/// is first or absent, so this is exact.
#[must_use]
pub fn is_base(ops: &[Op]) -> bool {
    ops.first().is_some_and(Op::is_replace)
}

/// [`is_base`] for wire batches.
#[must_use]
pub fn is_wire_base(ops: &[WireOp]) -> bool {
    ops.first().is_some_and(WireOp::is_replace)
}
