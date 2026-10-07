//! Operation tuples, paths, errors, and their validators (the type and
//! assertion part of `delta/index.ts`).

use std::fmt;
use std::sync::Arc;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::json::{js_string, write_json, JsonNumber, JsonValue};

/// Segments that reach the JS prototype chain. The tracker never emits them as
/// path segments and every applier rejects them.
pub const RESERVED_SEGMENTS: [&str; 3] = ["__proto__", "constructor", "prototype"];

/// Whether `key` is one of [`RESERVED_SEGMENTS`].
#[must_use]
pub fn is_reserved_segment(key: &str) -> bool {
    RESERVED_SEGMENTS.contains(&key)
}

/// One path segment: an object key or a non-negative array index.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Seg {
    /// An object key (a JSON string segment).
    Key(Arc<str>),
    /// An array index (a JSON number segment). On an object it names the key
    /// `index.to_string()`.
    Index(usize),
}

impl Seg {
    /// The key this segment names on an object.
    #[must_use]
    pub fn object_key(&self) -> Arc<str> {
        match self {
            Self::Key(key) => Arc::clone(key),
            Self::Index(index) => Arc::from(index.to_string()),
        }
    }

    /// The segment as a JSON value (string or number).
    #[must_use]
    pub fn to_json(&self) -> JsonValue {
        match self {
            Self::Key(key) => JsonValue::String(Arc::clone(key)),
            Self::Index(index) => index_json(*index),
        }
    }
}

#[allow(clippy::cast_precision_loss)] // indices above 2^53 do not occur in JSON documents
fn index_json(index: usize) -> JsonValue {
    JsonValue::Number(JsonNumber::new(index as f64).unwrap_or_default())
}

impl From<&str> for Seg {
    fn from(value: &str) -> Self {
        Self::Key(Arc::from(value))
    }
}

impl From<String> for Seg {
    fn from(value: String) -> Self {
        Self::Key(Arc::from(value))
    }
}

impl From<Arc<str>> for Seg {
    fn from(value: Arc<str>) -> Self {
        Self::Key(value)
    }
}

impl From<usize> for Seg {
    fn from(value: usize) -> Self {
        Self::Index(value)
    }
}

impl fmt::Display for Seg {
    /// JS `String(segment)`.
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Key(key) => formatter.write_str(key),
            Self::Index(index) => write!(formatter, "{index}"),
        }
    }
}

/// A path from the root: object keys and array indices. Empty is the root.
pub type Path = Vec<Seg>;

/// Render a path as `JSON.stringify(path)`.
#[must_use]
pub fn path_json(path: &[Seg]) -> JsonValue {
    JsonValue::Array(Arc::new(path.iter().map(Seg::to_json).collect()))
}

/// One decoded operation. On the wire and on disk it is the TS tuple
/// (`["s", path, value]`, ...).
///
/// `r` is the only op that replaces the whole value; `s`/`d`/`a`/`t` need a
/// non-empty path; `p` and `m` may target the root array.
#[derive(Clone, Debug, PartialEq)]
pub enum Op {
    /// `["r", value]`: replace the complete value.
    Replace(JsonValue),
    /// `["s", path, value]`: set an object property or array element.
    Set(Path, JsonValue),
    /// `["d", path]`: delete an object property or remove an array element.
    Delete(Path),
    /// `["a", path, text]`: append to a string.
    Append(Path, String),
    /// `["t", path, count]`: remove `count` UTF-16 code units from a string's
    /// front.
    Truncate(Path, usize),
    /// `["p", path, index, remove, items]`: splice an array.
    Splice(Path, usize, usize, Vec<JsonValue>),
    /// `["m", path, permutation]`: reorder an array,
    /// `new[i] = old[permutation[i]]`.
    Move(Path, Vec<usize>),
}

impl Op {
    /// The verb letter.
    #[must_use]
    pub fn verb(&self) -> &'static str {
        match self {
            Self::Replace(_) => "r",
            Self::Set(..) => "s",
            Self::Delete(_) => "d",
            Self::Append(..) => "a",
            Self::Truncate(..) => "t",
            Self::Splice(..) => "p",
            Self::Move(..) => "m",
        }
    }

    /// Whether this is `r` (`isReplace`).
    #[must_use]
    pub fn is_replace(&self) -> bool {
        matches!(self, Self::Replace(_))
    }

    /// The op's path; empty for `r`.
    #[must_use]
    pub fn path(&self) -> &[Seg] {
        match self {
            Self::Replace(_) => &[],
            Self::Set(path, _)
            | Self::Delete(path)
            | Self::Append(path, _)
            | Self::Truncate(path, _)
            | Self::Splice(path, ..)
            | Self::Move(path, _) => path,
        }
    }

    /// The op as its JSON tuple.
    #[must_use]
    pub fn to_json(&self) -> JsonValue {
        let verb = JsonValue::from(self.verb());
        let items = match self {
            Self::Replace(value) => vec![verb, value.clone()],
            Self::Set(path, value) => vec![verb, path_json(path), value.clone()],
            Self::Delete(path) => vec![verb, path_json(path)],
            Self::Append(path, text) => vec![verb, path_json(path), JsonValue::from(text.as_str())],
            Self::Truncate(path, count) => vec![verb, path_json(path), index_json(*count)],
            Self::Splice(path, index, remove, items) => vec![
                verb,
                path_json(path),
                index_json(*index),
                index_json(*remove),
                JsonValue::Array(Arc::new(items.clone())),
            ],
            Self::Move(path, permutation) => {
                vec![verb, path_json(path), permutation_json(permutation)]
            }
        };
        JsonValue::Array(Arc::new(items))
    }

    /// Validate a decoded op tuple (`assertValidOp`) and build it. Integral
    /// counts and indices beyond `usize` saturate (TS keeps them as doubles;
    /// every applier clamps them the same way).
    ///
    /// # Errors
    ///
    /// The TS `TypeError` message for a malformed tuple, or [`UnsafePathError`] for an unsafe segment.
    pub fn from_json(op: &JsonValue) -> Result<Self, DeltaError> {
        assert_valid_op(op)?;
        let items = op.as_array().unwrap_or_default();
        let path = || segments(&items[1]);
        Ok(match items[0].as_str().unwrap_or_default() {
            "r" => Self::Replace(items[1].clone()),
            "s" => Self::Set(path(), items[2].clone()),
            "d" => Self::Delete(path()),
            "a" => Self::Append(path(), items[2].as_str().unwrap_or_default().to_owned()),
            "t" => Self::Truncate(path(), count(&items[2])),
            "p" => Self::Splice(
                path(),
                count(&items[2]),
                count(&items[3]),
                items[4].as_array().unwrap_or_default().to_vec(),
            ),
            _ => Self::Move(path(), permutation(&items[2])),
        })
    }
}

fn permutation_json(permutation: &[usize]) -> JsonValue {
    JsonValue::Array(Arc::new(
        permutation.iter().copied().map(index_json).collect(),
    ))
}

/// A validated non-negative integer as `usize`, saturating beyond the range.
fn count(value: &JsonValue) -> usize {
    value
        .as_number()
        .map_or(0, |number| number.as_usize().unwrap_or(usize::MAX))
}

fn segments(path: &JsonValue) -> Path {
    path.as_array()
        .unwrap_or_default()
        .iter()
        .map(|segment| match segment {
            JsonValue::String(key) => Seg::Key(Arc::clone(key)),
            other => Seg::Index(count(other)),
        })
        .collect()
}

fn permutation(value: &JsonValue) -> Vec<usize> {
    value
        .as_array()
        .unwrap_or_default()
        .iter()
        .map(count)
        .collect()
}

impl Serialize for Op {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.to_json().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Op {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = JsonValue::deserialize(deserializer)?;
        Self::from_json(&value).map_err(serde::de::Error::custom)
    }
}

/// The path slot of a [`WireOp`].
#[derive(Clone, Debug, PartialEq)]
pub enum WirePath {
    /// The path inline.
    Inline(Path),
    /// An id defined by an earlier `["#", id, path]`.
    Id(u64),
    /// The short form: reuse the previous op's path in this batch.
    Previous,
}

/// An operation as it crosses a boundary: paths may be interned ids or
/// omitted when repeating the previous op's path, and `["#", id, path]`
/// defines an id.
#[derive(Clone, Debug, PartialEq)]
pub enum WireOp {
    /// `["r", value]`.
    Replace(JsonValue),
    /// `["s", ref, value]` or `["s", value]`.
    Set(WirePath, JsonValue),
    /// `["d", ref]` or `["d"]`.
    Delete(WirePath),
    /// `["a", ref, text]` or `["a", text]`.
    Append(WirePath, String),
    /// `["t", ref, count]` or `["t", count]`.
    Truncate(WirePath, usize),
    /// `["p", ref, index, remove, items]` or `["p", index, remove, items]`.
    Splice(WirePath, usize, usize, Vec<JsonValue>),
    /// `["m", ref, permutation]` or `["m", permutation]`.
    Move(WirePath, Vec<usize>),
    /// `["#", id, path]`.
    Define(u64, Path),
}

impl WireOp {
    /// Whether this is `r`.
    #[must_use]
    pub fn is_replace(&self) -> bool {
        matches!(self, Self::Replace(_))
    }

    /// The op as its JSON tuple.
    #[must_use]
    pub fn to_json(&self) -> JsonValue {
        fn with_ref(verb: &str, path: &WirePath, rest: Vec<JsonValue>) -> JsonValue {
            let mut items = vec![JsonValue::from(verb)];
            match path {
                WirePath::Inline(path) => items.push(path_json(path)),
                WirePath::Id(id) => items.push(id_json(*id)),
                WirePath::Previous => {}
            }
            items.extend(rest);
            JsonValue::Array(Arc::new(items))
        }
        match self {
            Self::Replace(value) => JsonValue::from(vec![JsonValue::from("r"), value.clone()]),
            Self::Set(path, value) => with_ref("s", path, vec![value.clone()]),
            Self::Delete(path) => with_ref("d", path, Vec::new()),
            Self::Append(path, text) => with_ref("a", path, vec![JsonValue::from(text.as_str())]),
            Self::Truncate(path, count) => with_ref("t", path, vec![index_json(*count)]),
            Self::Splice(path, index, remove, items) => with_ref(
                "p",
                path,
                vec![
                    index_json(*index),
                    index_json(*remove),
                    JsonValue::Array(Arc::new(items.clone())),
                ],
            ),
            Self::Move(path, permutation) => {
                with_ref("m", path, vec![permutation_json(permutation)])
            }
            Self::Define(id, path) => {
                JsonValue::from(vec![JsonValue::from("#"), id_json(*id), path_json(path)])
            }
        }
    }

    /// Validate a wire op tuple (`assertValidWireOp`) and build it.
    ///
    /// # Errors
    ///
    /// The TS `TypeError` message for a malformed tuple, or [`UnsafePathError`] for an unsafe segment.
    pub fn from_json(op: &JsonValue) -> Result<Self, DeltaError> {
        assert_valid_wire_op(op)?;
        let items = op.as_array().unwrap_or_default();
        let verb = items[0].as_str().unwrap_or_default();
        let wire_path = |value: &JsonValue| match value {
            JsonValue::Number(number) => WirePath::Id(number.as_u64().unwrap_or(u64::MAX)),
            path => WirePath::Inline(segments(path)),
        };
        // Arity tells whether a ref is present: the short forms omit it.
        let short = (verb == "d" && items.len() == 1)
            || (verb != "d" && verb != "p" && items.len() == 2)
            || (verb == "p" && items.len() == 4);
        let (path, rest) = if short || verb == "r" || verb == "#" {
            (WirePath::Previous, &items[1..])
        } else {
            (wire_path(&items[1]), &items[2..])
        };
        Ok(match verb {
            "r" => Self::Replace(items[1].clone()),
            "#" => Self::Define(items[1].as_u64().unwrap_or(u64::MAX), segments(&items[2])),
            "s" => Self::Set(path, rest[0].clone()),
            "d" => Self::Delete(path),
            "a" => Self::Append(path, rest[0].as_str().unwrap_or_default().to_owned()),
            "t" => Self::Truncate(path, count(&rest[0])),
            "p" => Self::Splice(
                path,
                count(&rest[0]),
                count(&rest[1]),
                rest[2].as_array().unwrap_or_default().to_vec(),
            ),
            _ => Self::Move(path, permutation(&rest[0])),
        })
    }
}

#[allow(clippy::cast_precision_loss)] // ids above 2^53 do not occur
fn id_json(id: u64) -> JsonValue {
    JsonValue::Number(JsonNumber::new(id as f64).unwrap_or_default())
}

impl Serialize for WireOp {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.to_json().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for WireOp {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = JsonValue::deserialize(deserializer)?;
        Self::from_json(&value).map_err(serde::de::Error::custom)
    }
}

/// A path segment that reaches the prototype chain or is not a non-negative
/// integer index (`UnsafePathError`).
#[derive(Clone, Debug, PartialEq, thiserror::Error)]
#[error("unsafe path segment: {}", js_string(.segment))]
pub struct UnsafePathError {
    /// The offending segment as it appeared.
    pub segment: JsonValue,
}

impl UnsafePathError {
    pub(crate) fn seg(segment: &Seg) -> Self {
        Self {
            segment: segment.to_json(),
        }
    }
}

/// What a [`PathError`] could not resolve.
#[derive(Clone, Debug, PartialEq)]
pub enum UnresolvedPath {
    /// A path.
    Path(Path),
    /// An undefined path id.
    Id(u64),
}

/// A path that does not resolve in the target (`PathError`).
#[derive(Clone, Debug, PartialEq, thiserror::Error)]
#[error("unresolvable path: {}", unresolved_json(.path))]
pub struct PathError {
    /// The path or id.
    pub path: UnresolvedPath,
}

impl PathError {
    pub(crate) fn path(path: &[Seg]) -> Self {
        Self {
            path: UnresolvedPath::Path(path.to_vec()),
        }
    }
}

fn unresolved_json(path: &UnresolvedPath) -> String {
    let mut out = String::new();
    match path {
        UnresolvedPath::Path(path) => write_json(&mut out, &path_json(path)),
        UnresolvedPath::Id(id) => write_json(&mut out, &id_json(*id)),
    }
    out
}

/// Errors from validating, decoding, and applying operations.
#[derive(Clone, Debug, PartialEq, thiserror::Error)]
pub enum DeltaError {
    /// A malformed op (TS `TypeError`), with the TS message.
    #[error("{0}")]
    Type(&'static str),
    /// An unknown verb (TS `TypeError` `unknown op verb: …`).
    #[error("unknown op verb: {0}")]
    UnknownVerb(String),
    /// An unsafe segment.
    #[error(transparent)]
    UnsafePath(#[from] UnsafePathError),
    /// An unresolvable path.
    #[error(transparent)]
    Path(#[from] PathError),
}

fn is_non_negative_integer(value: &JsonValue) -> bool {
    value
        .as_number()
        .is_some_and(|number| number.is_integer() && number.get() >= 0.0)
}

/// Validate a path given as JSON (`assertSafePath`).
///
/// # Errors
///
/// The TS `TypeError` message for a malformed tuple, or [`UnsafePathError`] for an unsafe segment.
pub fn assert_safe_json_path(path: &[JsonValue]) -> Result<(), UnsafePathError> {
    for segment in path {
        match segment {
            JsonValue::String(key) if is_reserved_segment(key) => {
                return Err(UnsafePathError {
                    segment: segment.clone(),
                })
            }
            JsonValue::String(_) => {}
            other if is_non_negative_integer(other) => {}
            other => {
                return Err(UnsafePathError {
                    segment: other.clone(),
                })
            }
        }
    }
    Ok(())
}

/// Reject reserved keys in a typed path (`assertSafePath`).
///
/// # Errors
///
/// The TS `TypeError` message for a malformed tuple, or [`UnsafePathError`] for an unsafe segment.
pub fn assert_safe_path(path: &[Seg]) -> Result<(), UnsafePathError> {
    for segment in path {
        if let Seg::Key(key) = segment {
            if is_reserved_segment(key) {
                return Err(UnsafePathError::seg(segment));
            }
        }
    }
    Ok(())
}

fn assert_path_arg(path: &JsonValue, non_empty: bool) -> Result<(), DeltaError> {
    let Some(segments) = path.as_array() else {
        return Err(DeltaError::Type("path is not an array"));
    };
    if non_empty && segments.is_empty() {
        return Err(DeltaError::Type("path is empty"));
    }
    assert_safe_json_path(segments)?;
    Ok(())
}

fn assert_permutation(value: &JsonValue) -> Result<(), DeltaError> {
    let Some(items) = value.as_array() else {
        return Err(DeltaError::Type("m permutation is not an array"));
    };
    let mut seen = vec![false; items.len()];
    for item in items {
        let slot = item
            .as_number()
            .filter(|number| number.is_integer() && number.get() >= 0.0)
            .and_then(JsonNumber::as_usize)
            .filter(|index| *index < items.len());
        match slot {
            Some(index) if !seen[index] => seen[index] = true,
            _ => return Err(DeltaError::Type("m permutation is not a bijection")),
        }
    }
    Ok(())
}

fn verb_text(value: &JsonValue) -> String {
    js_string(value)
}

/// Verb, arity, and payload shape of a decoded op (`assertValidOp`): paths
/// inline, no `#`, no short forms. Payloads are not inspected.
///
/// # Errors
///
/// The TS `TypeError` message for a malformed tuple, or [`UnsafePathError`] for an unsafe segment.
pub fn assert_valid_op(op: &JsonValue) -> Result<(), DeltaError> {
    let items = match op.as_array() {
        Some(items) if !items.is_empty() => items,
        _ => return Err(DeltaError::Type("op is not a tuple")),
    };
    match items[0].as_str() {
        Some("r") => {
            if items.len() != 2 {
                return Err(DeltaError::Type("r arity"));
            }
        }
        Some("s") => {
            if items.len() != 3 {
                return Err(DeltaError::Type("s arity"));
            }
            assert_path_arg(&items[1], true)?;
        }
        Some("d") => {
            if items.len() != 2 {
                return Err(DeltaError::Type("d arity"));
            }
            assert_path_arg(&items[1], true)?;
        }
        Some("a") => {
            if items.len() != 3 || !items[2].is_string() {
                return Err(DeltaError::Type("a shape"));
            }
            assert_path_arg(&items[1], true)?;
        }
        Some("t") => {
            if items.len() != 3 || !is_non_negative_integer(&items[2]) {
                return Err(DeltaError::Type("t shape"));
            }
            assert_path_arg(&items[1], true)?;
        }
        Some("p") => {
            if items.len() != 5 {
                return Err(DeltaError::Type("p arity"));
            }
            assert_path_arg(&items[1], false)?;
            if !is_non_negative_integer(&items[2]) {
                return Err(DeltaError::Type("p index"));
            }
            if !is_non_negative_integer(&items[3]) {
                return Err(DeltaError::Type("p remove"));
            }
            if !items[4].is_array() {
                return Err(DeltaError::Type("p items"));
            }
        }
        Some("m") => {
            if items.len() != 3 {
                return Err(DeltaError::Type("m arity"));
            }
            assert_path_arg(&items[1], false)?;
            assert_permutation(&items[2])?;
        }
        // Silently skipping an unknown verb is how a newer producer's op vanishes.
        _ => return Err(DeltaError::UnknownVerb(verb_text(&items[0]))),
    }
    Ok(())
}

/// The same for the wire grammar (`assertValidWireOp`): ids and short forms
/// are legal.
///
/// # Errors
///
/// The TS `TypeError` message for a malformed tuple, or [`UnsafePathError`] for an unsafe segment.
#[allow(clippy::too_many_lines)] // one arm per verb, mirroring assertValidWireOp
pub fn assert_valid_wire_op(op: &JsonValue) -> Result<(), DeltaError> {
    let items = match op.as_array() {
        Some(items) if !items.is_empty() => items,
        _ => return Err(DeltaError::Type("op is not a tuple")),
    };
    let ok_ref = |reference: &JsonValue| -> Result<(), DeltaError> {
        if reference.is_number() {
            if !is_non_negative_integer(reference) {
                return Err(DeltaError::Type("bad path id"));
            }
            return Ok(());
        }
        // A string is not a path: unchecked it would resolve to the root.
        let Some(path) = reference.as_array() else {
            return Err(DeltaError::Type("path is not an array"));
        };
        assert_safe_json_path(path)?;
        Ok(())
    };
    let length = items.len();
    match items[0].as_str() {
        Some("r") => {
            if length != 2 {
                return Err(DeltaError::Type("r arity"));
            }
        }
        Some("s") => {
            if length == 3 {
                ok_ref(&items[1])?;
            } else if length != 2 {
                return Err(DeltaError::Type("s arity"));
            }
        }
        Some("d") => {
            if length == 2 {
                ok_ref(&items[1])?;
            } else if length != 1 {
                return Err(DeltaError::Type("d arity"));
            }
        }
        Some("a") => {
            if length == 3 {
                ok_ref(&items[1])?;
                if !items[2].is_string() {
                    return Err(DeltaError::Type("a value"));
                }
            } else if length == 2 {
                if !items[1].is_string() {
                    return Err(DeltaError::Type("a value"));
                }
            } else {
                return Err(DeltaError::Type("a arity"));
            }
        }
        Some("t") => {
            if length == 3 {
                ok_ref(&items[1])?;
                if !is_non_negative_integer(&items[2]) {
                    return Err(DeltaError::Type("t count"));
                }
            } else if length == 2 {
                if !is_non_negative_integer(&items[1]) {
                    return Err(DeltaError::Type("t count"));
                }
            } else {
                return Err(DeltaError::Type("t arity"));
            }
        }
        Some("p") => {
            let (index, remove, payload) = match length {
                5 => (&items[2], &items[3], &items[4]),
                4 => (&items[1], &items[2], &items[3]),
                _ => return Err(DeltaError::Type("p arity")),
            };
            if length == 5 {
                ok_ref(&items[1])?;
            }
            if !is_non_negative_integer(index) {
                return Err(DeltaError::Type("p index"));
            }
            if !is_non_negative_integer(remove) {
                return Err(DeltaError::Type("p remove"));
            }
            if !payload.is_array() {
                return Err(DeltaError::Type("p items"));
            }
        }
        Some("m") => {
            if length == 3 {
                ok_ref(&items[1])?;
            } else if length != 2 {
                return Err(DeltaError::Type("m arity"));
            }
            assert_permutation(&items[length - 1])?;
        }
        Some("#") => {
            let valid = length == 3 && is_non_negative_integer(&items[1]) && items[2].is_array();
            if !valid {
                return Err(DeltaError::Type("# shape"));
            }
            assert_safe_json_path(items[2].as_array().unwrap_or_default())?;
        }
        _ => return Err(DeltaError::UnknownVerb(verb_text(&items[0]))),
    }
    Ok(())
}

/// Validate a typed op before applying it: what the tuple type cannot
/// express (non-empty paths, safe keys, bijective permutations).
pub(crate) fn validate_op(op: &Op) -> Result<(), DeltaError> {
    match op {
        Op::Replace(_) => Ok(()),
        Op::Set(path, _) | Op::Delete(path) | Op::Append(path, _) | Op::Truncate(path, _) => {
            if path.is_empty() {
                return Err(DeltaError::Type("path is empty"));
            }
            assert_safe_path(path)?;
            Ok(())
        }
        Op::Splice(path, ..) => Ok(assert_safe_path(path)?),
        Op::Move(path, permutation) => {
            assert_safe_path(path)?;
            let mut seen = vec![false; permutation.len()];
            for &index in permutation {
                if index >= permutation.len() || seen[index] {
                    return Err(DeltaError::Type("m permutation is not a bijection"));
                }
                seen[index] = true;
            }
            Ok(())
        }
    }
}
