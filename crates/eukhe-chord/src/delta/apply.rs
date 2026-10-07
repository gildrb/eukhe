//! Appliers: `apply`, `applyImmutable`, `applyImmutableBatches` (from
//! `delta/index.ts`) and the tracker's trusted materialization
//! (`apply-immutable-trusted.ts`).
//!
//! [`JsonValue`] containers are `Arc`-shared and copied on write, so every
//! applier leaves its inputs untouched and shares unchanged subtrees and op
//! payloads with its result, exactly what the immutable TS appliers do with
//! their owned-container sets.

use std::convert::Infallible;
use std::sync::Arc;

use super::ops::{validate_op, DeltaError, Op, PathError, Seg, UnsafePathError};
use crate::json::{canonical_array_index, utf16_skip, JsonValue};

/// Apply decoded ops to a replica the caller owns and return the result
/// (`apply`). `r` adopts its payload (an O(1) share).
///
/// TS `apply(undefined, ops)` maps to `apply(JsonValue::Null, ops)`: every
/// non-`r` op fails identically on both, and only an empty batch differs
/// (it returns `null` instead of `undefined`).
///
/// On error the partially applied replica is dropped; recover from a later
/// `r`.
///
/// # Errors
///
/// An invalid op ([`DeltaError::Type`], [`DeltaError::UnsafePath`]) or a path that does not resolve in the target ([`DeltaError::Path`]).
pub fn apply(target: JsonValue, ops: &[Op]) -> Result<JsonValue, DeltaError> {
    let mut root = target;
    for op in ops {
        validate_op(op)?;
        apply_op(&mut root, op)?;
    }
    Ok(root)
}

/// Apply one decoded batch without changing `target` (`applyImmutable`). The
/// result shares containers with `target` and the payloads of `ops`.
///
/// ```
/// use eukhe_chord::delta::{apply_immutable, Op};
/// use eukhe_chord::json::JsonValue;
/// let base = JsonValue::parse(r#"{"text":"a","stable":{}}"#).unwrap();
/// let next = apply_immutable(&base, &[Op::Append(vec!["text".into()], "b".into())]).unwrap();
/// assert_eq!(next.to_string(), r#"{"text":"ab","stable":{}}"#);
/// assert!(next["stable"].strict_equals(&base["stable"]));
/// ```
///
/// # Errors
///
/// An invalid op ([`DeltaError::Type`], [`DeltaError::UnsafePath`]) or a path that does not resolve in the target ([`DeltaError::Path`]).
pub fn apply_immutable(target: &JsonValue, ops: &[Op]) -> Result<JsonValue, DeltaError> {
    apply_immutable_batches(target, [ops])
}

/// Apply decoded batches as one final-result-only replay
/// (`applyImmutableBatches`).
///
/// # Errors
///
/// An invalid op ([`DeltaError::Type`], [`DeltaError::UnsafePath`]) or a path that does not resolve in the target ([`DeltaError::Path`]).
pub fn apply_immutable_batches<I>(target: &JsonValue, batches: I) -> Result<JsonValue, DeltaError>
where
    I: IntoIterator,
    I::Item: AsRef<[Op]>,
{
    try_apply_immutable_batches(target, batches.into_iter().map(Ok::<_, Infallible>)).map_err(
        |error| match error {
            BatchError::Delta(error) => error,
            BatchError::Source(never) => match never {},
        },
    )
}

/// A failure of [`try_apply_immutable_batches`]: an invalid op, or the batch
/// source's own error (the TS generator that throws while iterating).
#[derive(Debug, thiserror::Error)]
pub enum BatchError<E> {
    /// An op failed to validate or apply.
    #[error(transparent)]
    Delta(DeltaError),
    /// The batch source failed.
    #[error(transparent)]
    Source(E),
}

/// [`apply_immutable_batches`] over a fallible batch source. Stops at the first
/// error; nothing partial is exposed.
///
/// # Errors
///
/// An invalid op ([`DeltaError::Type`], [`DeltaError::UnsafePath`]) or a path that does not resolve in the target ([`DeltaError::Path`]).
pub fn try_apply_immutable_batches<I, B, E>(
    target: &JsonValue,
    batches: I,
) -> Result<JsonValue, BatchError<E>>
where
    I: IntoIterator<Item = Result<B, E>>,
    B: AsRef<[Op]>,
{
    let mut root = target.clone();
    for batch in batches {
        let batch = batch.map_err(BatchError::Source)?;
        for op in batch.as_ref() {
            validate_op(op).map_err(BatchError::Delta)?;
            if let Op::Replace(value) = op {
                root = value.clone();
                continue;
            }
            let path = op.path();
            let containers = match op {
                Op::Splice(..) | Op::Move(..) => path,
                _ => &path[..path.len() - 1],
            };
            check_copy_containers(&root, containers).map_err(BatchError::Delta)?;
            apply_op(&mut root, op).map_err(BatchError::Delta)?;
        }
    }
    Ok(root)
}

/// The checks `copyContainers` makes before copying the containers along
/// `path`, in its order.
fn check_copy_containers(root: &JsonValue, path: &[Seg]) -> Result<(), DeltaError> {
    if !root.is_container() {
        return Err(PathError::path(path).into());
    }
    let mut destination = root;
    for segment in path {
        if !has_own(destination, segment) {
            return Err(PathError::path(path).into());
        }
        let child = match (destination, segment) {
            (JsonValue::Array(_), Seg::Key(_)) => return Err(UnsafePathError::seg(segment).into()),
            (JsonValue::Array(items), Seg::Index(index)) => &items[*index],
            (JsonValue::Object(object), segment) => object
                .get(&segment.object_key())
                .unwrap_or(&crate::json::NULL),
            _ => return Err(PathError::path(path).into()),
        };
        if !child.is_container() {
            return Err(PathError::path(path).into());
        }
        destination = child;
    }
    Ok(())
}

/// `Object.hasOwn(container, segment)`; arrays own `length` and their
/// in-range canonical indices.
fn has_own(container: &JsonValue, segment: &Seg) -> bool {
    match (container, segment) {
        (JsonValue::Array(items), Seg::Index(index)) => *index < items.len(),
        (JsonValue::Array(items), Seg::Key(key)) => {
            &**key == "length"
                || canonical_array_index(key)
                    .is_some_and(|index| usize::try_from(index).is_ok_and(|at| at < items.len()))
        }
        (JsonValue::Object(object), segment) => object.contains_key(&segment.object_key()),
        _ => false,
    }
}

/// `resolveValue` + `resolve`: walk to the container at `path`, copying shared
/// containers on the way.
fn resolve_mut<'a>(root: &'a mut JsonValue, path: &[Seg]) -> Result<&'a mut JsonValue, DeltaError> {
    let mut node = root;
    for segment in path {
        node = match node {
            JsonValue::Array(items) => {
                let Seg::Index(index) = segment else {
                    return Err(UnsafePathError::seg(segment).into());
                };
                Arc::make_mut(items)
                    .get_mut(*index)
                    .ok_or_else(|| PathError::path(path))?
            }
            JsonValue::Object(object) => Arc::make_mut(object)
                .get_mut(&segment.object_key())
                .ok_or_else(|| PathError::path(path))?,
            _ => return Err(PathError::path(path).into()),
        };
    }
    if !node.is_container() {
        return Err(PathError::path(path).into());
    }
    Ok(node)
}

/// Apply one validated non-`r`-or-`r` op in place (`applyOps` body).
pub(crate) fn apply_op(root: &mut JsonValue, op: &Op) -> Result<(), DeltaError> {
    match op {
        Op::Replace(value) => {
            // Adopted, not copied.
            *root = value.clone();
            Ok(())
        }
        Op::Splice(path, index, remove, items) => {
            let target = if path.is_empty() {
                root
            } else {
                resolve_mut(root, path)?
            };
            let Some(array) = target.as_array_mut() else {
                return Err(PathError::path(path).into());
            };
            let start = (*index).min(array.len());
            let end = start + (*remove).min(array.len() - start);
            array.splice(start..end, items.iter().cloned());
            Ok(())
        }
        Op::Move(path, permutation) => {
            let target = if path.is_empty() {
                root
            } else {
                resolve_mut(root, path)?
            };
            let JsonValue::Array(items) = target else {
                return Err(PathError::path(path).into());
            };
            if items.len() != permutation.len() {
                return Err(PathError::path(path).into());
            }
            let previous = items.as_slice().to_vec();
            let array = Arc::make_mut(items);
            for (index, &from) in permutation.iter().enumerate() {
                array[index] = previous[from].clone();
            }
            Ok(())
        }
        Op::Set(path, _) | Op::Delete(path) | Op::Append(path, _) | Op::Truncate(path, _) => {
            let (key, parent_path) = path.split_last().ok_or(DeltaError::Type("path is empty"))?;
            let parent = resolve_mut(root, parent_path)?;
            if let JsonValue::Array(items) = parent {
                let Seg::Index(index) = key else {
                    return Err(UnsafePathError::seg(key).into());
                };
                // An index may address an element or append exactly one past
                // the end: anything further would make the array sparse.
                if *index > items.len() {
                    return Err(UnsafePathError::seg(key).into());
                }
            }
            apply_leaf(parent, key, path, op)
        }
    }
}

fn apply_leaf(parent: &mut JsonValue, key: &Seg, path: &[Seg], op: &Op) -> Result<(), DeltaError> {
    match op {
        Op::Set(_, value) => {
            write(parent, key, value.clone());
            Ok(())
        }
        Op::Delete(_) => {
            match parent {
                JsonValue::Array(items) => {
                    let Seg::Index(index) = key else {
                        return Err(PathError::path(path).into());
                    };
                    if *index >= items.len() {
                        return Err(PathError::path(path).into());
                    }
                    Arc::make_mut(items).remove(*index);
                }
                JsonValue::Object(object) => {
                    Arc::make_mut(object).remove(&key.object_key());
                }
                _ => return Err(PathError::path(path).into()),
            }
            Ok(())
        }
        Op::Append(_, text) => {
            let Some(current) = read(parent, key).and_then(JsonValue::as_str) else {
                return Err(PathError::path(path).into());
            };
            let next = format!("{current}{text}");
            write(parent, key, JsonValue::from(next));
            Ok(())
        }
        Op::Truncate(_, count) => {
            let Some(current) = read(parent, key).and_then(JsonValue::as_shared_str) else {
                return Err(PathError::path(path).into());
            };
            let next = JsonValue::from(utf16_skip(current, *count));
            write(parent, key, next);
            Ok(())
        }
        Op::Replace(_) | Op::Splice(..) | Op::Move(..) => Ok(()),
    }
}

fn read<'a>(parent: &'a JsonValue, key: &Seg) -> Option<&'a JsonValue> {
    match (parent, key) {
        (JsonValue::Array(items), Seg::Index(index)) => items.get(*index),
        (JsonValue::Object(object), key) => object.get(&key.object_key()),
        _ => None,
    }
}

/// Define `key` as an own data property.
fn write(parent: &mut JsonValue, key: &Seg, value: JsonValue) {
    match (parent, key) {
        (JsonValue::Array(items), Seg::Index(index)) => {
            let array = Arc::make_mut(items);
            if *index == array.len() {
                array.push(value);
            } else {
                array[*index] = value;
            }
        }
        (JsonValue::Object(object), key) => {
            Arc::make_mut(object).insert(key.object_key(), value);
        }
        _ => {}
    }
}

/// Apply self-produced trusted ops, copying each touched container once
/// (`applyImmutableTrusted`). Tracker ops always resolve; a violated
/// invariant surfaces as the applier's [`DeltaError`].
pub(crate) fn apply_immutable_trusted(
    target: &JsonValue,
    ops: &[Op],
) -> Result<JsonValue, DeltaError> {
    let mut root = target.clone();
    for op in ops {
        apply_op(&mut root, op)?;
    }
    Ok(root)
}
