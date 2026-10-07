//! Path interning between the tracker and a boundary (`encoder`/`decoder` of
//! `delta/index.ts`).
//!
//! One pair per independent state stream: every decoder must observe exactly
//! the batches encoded by its matching encoder, beginning with that state's
//! base. An `r` resets both dictionaries.

use std::collections::{HashMap, HashSet};

use super::ops::{
    assert_safe_path, DeltaError, Op, Path, PathError, UnresolvedPath, WireOp, WirePath,
};

/// Interns repeated paths of one ordered state stream.
///
/// ```
/// use eukhe_chord::delta::{decoder, encoder, Op, WireOp, WirePath};
/// let (mut enc, mut dec) = (encoder(), decoder());
/// let path = vec!["value".into()];
/// let wire = enc.encode(&[Op::Set(path.clone(), 1.into()), Op::Set(path.clone(), 2.into())]);
/// assert_eq!(wire[1], WireOp::Set(WirePath::Previous, 2.into()));
/// assert_eq!(dec.decode(&wire).unwrap()[1], Op::Set(path, 2.into()));
/// ```
#[derive(Debug, Default)]
pub struct Encoder {
    seen: HashSet<Path>,
    ids: HashMap<Path, u64>,
    next_id: u64,
}

/// A fresh [`Encoder`] (`encoder()`).
#[must_use]
pub fn encoder() -> Encoder {
    Encoder::default()
}

impl Encoder {
    /// Encode one batch. Interns a path on its second use (`["#", id, path]`
    /// then the id) and omits the path of an op repeating the previous op's
    /// path within the batch.
    pub fn encode(&mut self, ops: &[Op]) -> Vec<WireOp> {
        // Arity omission is scoped to a batch; ids are the only cross-batch state.
        let mut previous: Option<&Path> = None;
        let mut out = Vec::with_capacity(ops.len());
        for op in ops {
            let (path, short) = match op {
                Op::Replace(value) => {
                    out.push(WireOp::Replace(value.clone()));
                    // A base batch is a recovery point: what follows must be
                    // self-contained.
                    self.seen.clear();
                    self.ids.clear();
                    self.next_id = 0;
                    previous = None;
                    continue;
                }
                Op::Set(path, _)
                | Op::Delete(path)
                | Op::Append(path, _)
                | Op::Truncate(path, _)
                | Op::Splice(path, ..)
                | Op::Move(path, _) => (path, previous == Some(path)),
            };
            let reference = if short {
                WirePath::Previous
            } else if let Some(id) = self.ids.get(path) {
                WirePath::Id(*id)
            } else if self.seen.contains(path) {
                let id = self.next_id;
                self.next_id += 1;
                self.ids.insert(path.clone(), id);
                out.push(WireOp::Define(id, path.clone()));
                WirePath::Id(id)
            } else {
                self.seen.insert(path.clone());
                WirePath::Inline(path.clone())
            };
            out.push(match op {
                Op::Set(_, value) => WireOp::Set(reference, value.clone()),
                Op::Delete(_) => WireOp::Delete(reference),
                Op::Append(_, text) => WireOp::Append(reference, text.clone()),
                Op::Truncate(_, count) => WireOp::Truncate(reference, *count),
                Op::Splice(_, index, remove, items) => {
                    WireOp::Splice(reference, *index, *remove, items.clone())
                }
                Op::Move(_, permutation) => WireOp::Move(reference, permutation.clone()),
                Op::Replace(_) => continue,
            });
            if !short {
                previous = Some(path);
            }
        }
        out
    }
}

/// Restores [`Op`]s from the [`WireOp`]s of one stream.
#[derive(Debug, Default)]
pub struct Decoder {
    paths: HashMap<u64, Path>,
}

/// A fresh [`Decoder`] (`decoder()`).
#[must_use]
pub fn decoder() -> Decoder {
    Decoder::default()
}

impl Decoder {
    /// Validate and decode one batch. After an error, discard the decoder and
    /// recover from a later `r`.
    ///
    /// # Errors
    ///
    /// An unsafe path, an undefined path id, or a short form without a previous path.
    pub fn decode(&mut self, wire: &[WireOp]) -> Result<Vec<Op>, DeltaError> {
        let mut previous: Option<Path> = None;
        let mut out = Vec::with_capacity(wire.len());
        for op in wire {
            validate_wire_op(op)?;
            let reference = match op {
                WireOp::Define(id, path) => {
                    assert_safe_path(path)?;
                    self.paths.insert(*id, path.clone());
                    continue;
                }
                WireOp::Replace(value) => {
                    out.push(Op::Replace(value.clone()));
                    self.paths.clear();
                    previous = None;
                    continue;
                }
                WireOp::Set(reference, _)
                | WireOp::Delete(reference)
                | WireOp::Append(reference, _)
                | WireOp::Truncate(reference, _)
                | WireOp::Splice(reference, ..)
                | WireOp::Move(reference, _) => reference,
            };
            let path = match reference {
                WirePath::Previous => previous.clone().ok_or_else(|| PathError::path(&[]))?,
                WirePath::Id(id) => {
                    let resolved = self.paths.get(id).cloned().ok_or(PathError {
                        path: UnresolvedPath::Id(*id),
                    })?;
                    previous = Some(resolved.clone());
                    resolved
                }
                WirePath::Inline(path) => {
                    previous = Some(path.clone());
                    path.clone()
                }
            };
            let needs_path = !matches!(op, WireOp::Splice(..) | WireOp::Move(..));
            if needs_path && path.is_empty() {
                return Err(PathError::path(&path).into());
            }
            let decoded = match op {
                WireOp::Set(_, value) => Op::Set(path, value.clone()),
                WireOp::Delete(_) => Op::Delete(path),
                WireOp::Append(_, text) => Op::Append(path, text.clone()),
                WireOp::Truncate(_, count) => Op::Truncate(path, *count),
                WireOp::Splice(_, index, remove, items) => {
                    Op::Splice(path, *index, *remove, items.clone())
                }
                WireOp::Move(_, permutation) => Op::Move(path, permutation.clone()),
                WireOp::Replace(_) | WireOp::Define(..) => continue,
            };
            out.push(decoded);
        }
        Ok(out)
    }
}

/// What `assertValidWireOp` checks that the [`WireOp`] type cannot express:
/// safe inline and defined paths, bijective permutations.
fn validate_wire_op(op: &WireOp) -> Result<(), DeltaError> {
    let reference = match op {
        WireOp::Replace(_) => return Ok(()),
        WireOp::Define(_, path) => return Ok(assert_safe_path(path)?),
        WireOp::Set(reference, _)
        | WireOp::Delete(reference)
        | WireOp::Append(reference, _)
        | WireOp::Truncate(reference, _)
        | WireOp::Splice(reference, ..)
        | WireOp::Move(reference, _) => reference,
    };
    if let WirePath::Inline(path) = reference {
        assert_safe_path(path)?;
    }
    if let WireOp::Move(_, permutation) = op {
        let mut seen = vec![false; permutation.len()];
        for &index in permutation {
            if index >= permutation.len() || seen[index] {
                return Err(DeltaError::Type("m permutation is not a bijection"));
            }
            seen[index] = true;
        }
    }
    Ok(())
}
