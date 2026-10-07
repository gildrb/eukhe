//! Strict JSON values with JS semantics (port of `json.ts` and the `JsonValue`
//! type of `types.ts`).
//!
//! [`JsonValue`] is persistent and immutable: cloning is O(1) and revisions
//! share unchanged subtrees through `Arc` containers. Mutation goes through
//! copy-on-write accessors ([`JsonValue::as_array_mut`],
//! [`JsonValue::as_object_mut`]) that never affect other holders.
//!
//! JS semantics kept:
//! - objects iterate in JS own-property order ([`JsonObject`]);
//! - numbers are finite doubles ([`JsonNumber`]) printed like `JSON.stringify`;
//! - `Display` is `JSON.stringify` output byte for byte;
//! - `==` is deep JSON equality ignoring key order; [`JsonValue::strict_equals`]
//!   is JS `===` (containers by identity).
//!
//! Not representable: `undefined`, prototypes (null-prototype objects are
//! plain objects here), and lone UTF-16 surrogates (Rust strings are UTF-8).
//!
//! `JsonRepresentation<T>` is a TS type-level mapping of an application type
//! to its strict-JSON shape. Its Rust meaning is the `serde` data model:
//! a typed record `T: Serialize` is converted with [`to_json`] and read back
//! with [`from_json`].
//!
//! ```
//! use eukhe_chord::json::{to_json, JsonValue};
//! #[derive(serde::Serialize)]
//! struct Usage { input: u32, label: Option<String> }
//! let value = to_json(&Usage { input: 3, label: None }).unwrap();
//! assert_eq!(value.to_string(), r#"{"input":3,"label":null}"#);
//! let parsed = JsonValue::parse(r#"{"b":1,"a":[true,null]}"#).unwrap();
//! assert_eq!(parsed["a"][0], JsonValue::Bool(true));
//! ```

mod display;
mod number;
mod object;
mod serialization;
mod utf16;

use std::fmt;
use std::sync::Arc;

pub use number::{JsonNumber, MAX_SAFE_INTEGER};
pub use object::{canonical_array_index, JsonObject};
pub use serialization::{from_json, to_json};
pub use utf16::{
    utf16_ceil_byte_offset, utf16_floor_byte_offset, utf16_len, utf16_prefix, utf16_skip,
    utf16_slice, utf16_suffix,
};

pub(crate) use display::{js_string, write_json};
pub(crate) use number::write_js_number;
pub(crate) use utf16::utf16_units;

/// Errors converting into or out of [`JsonValue`].
#[derive(Debug, thiserror::Error)]
pub enum JsonError {
    /// A float was NaN or infinite.
    #[error("Value contains a non-finite number and is not strict JSON")]
    NonFinite,
    /// An integer is beyond `Number.MAX_SAFE_INTEGER` and would lose precision.
    #[error("Value contains an integer beyond Number.MAX_SAFE_INTEGER and is not exact JSON")]
    UnsafeInteger,
    /// JSON text could not be parsed as strict JSON.
    #[error("{0}")]
    Parse(serde_json::Error),
    /// A typed value could not be serialized.
    #[error("{0}")]
    Serialize(String),
    /// A JSON value did not match the requested type.
    #[error("{0}")]
    Deserialize(serde_json::Error),
}

/// A strict JSON value. See the [module docs](self).
///
/// ```
/// use eukhe_chord::json::JsonValue;
/// let value = JsonValue::parse(r#"{"z":1,"1":2,"a":-0}"#).unwrap();
/// assert_eq!(value.to_string(), r#"{"1":2,"z":1,"a":0}"#);
/// let copy = value.clone(); // O(1), shares the object
/// assert!(copy.strict_equals(&value));
/// ```
#[derive(Clone, Default)]
pub enum JsonValue {
    /// `null`.
    #[default]
    Null,
    /// `true` / `false`.
    Bool(bool),
    /// A finite double.
    Number(JsonNumber),
    /// A string.
    String(Arc<str>),
    /// A dense array.
    Array(Arc<Vec<JsonValue>>),
    /// An object in JS own-property order.
    Object(Arc<JsonObject>),
}

/// The `null` value, for returning references to absent entries.
pub static NULL: JsonValue = JsonValue::Null;

impl JsonValue {
    /// Parse JSON text (`JSON.parse`), rejecting numbers that overflow to
    /// infinity. Lone surrogate escapes are rejected (not representable), and
    /// nesting deeper than `serde_json`'s recursion limit (128) fails where V8
    /// would only fail at its stack limit.
    ///
    /// # Errors
    ///
    /// [`JsonError::Parse`] for invalid JSON text or numbers beyond the double range.
    pub fn parse(text: &str) -> Result<Self, JsonError> {
        serde_json::from_str(text).map_err(JsonError::Parse)
    }

    /// An empty object.
    #[must_use]
    pub fn object() -> Self {
        Self::Object(Arc::new(JsonObject::new()))
    }

    /// An empty array.
    #[must_use]
    pub fn array() -> Self {
        Self::Array(Arc::new(Vec::new()))
    }

    /// Whether this is `null`.
    #[must_use]
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Null)
    }

    /// Whether this is a boolean.
    #[must_use]
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool(_))
    }

    /// Whether this is a number.
    #[must_use]
    pub fn is_number(&self) -> bool {
        matches!(self, Self::Number(_))
    }

    /// Whether this is a string.
    #[must_use]
    pub fn is_string(&self) -> bool {
        matches!(self, Self::String(_))
    }

    /// Whether this is an array.
    #[must_use]
    pub fn is_array(&self) -> bool {
        matches!(self, Self::Array(_))
    }

    /// Whether this is an object.
    #[must_use]
    pub fn is_object(&self) -> bool {
        matches!(self, Self::Object(_))
    }

    /// Whether this is an array or object.
    #[must_use]
    pub fn is_container(&self) -> bool {
        matches!(self, Self::Array(_) | Self::Object(_))
    }

    /// The boolean.
    #[must_use]
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(flag) => Some(*flag),
            _ => None,
        }
    }

    /// The number.
    #[must_use]
    pub fn as_number(&self) -> Option<JsonNumber> {
        match self {
            Self::Number(number) => Some(*number),
            _ => None,
        }
    }

    /// The number as a double.
    #[must_use]
    pub fn as_f64(&self) -> Option<f64> {
        self.as_number().map(JsonNumber::get)
    }

    /// The number as `u64`, only when exactly representable.
    #[must_use]
    pub fn as_u64(&self) -> Option<u64> {
        self.as_number().and_then(JsonNumber::as_u64)
    }

    /// The number as `i64`, only when exactly representable.
    #[must_use]
    pub fn as_i64(&self) -> Option<i64> {
        self.as_number().and_then(JsonNumber::as_i64)
    }

    /// The string.
    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(text) => Some(text),
            _ => None,
        }
    }

    /// The shared string.
    #[must_use]
    pub fn as_shared_str(&self) -> Option<&Arc<str>> {
        match self {
            Self::String(text) => Some(text),
            _ => None,
        }
    }

    /// The array items.
    #[must_use]
    pub fn as_array(&self) -> Option<&[JsonValue]> {
        match self {
            Self::Array(items) => Some(items),
            _ => None,
        }
    }

    /// The object.
    #[must_use]
    pub fn as_object(&self) -> Option<&JsonObject> {
        match self {
            Self::Object(object) => Some(object),
            _ => None,
        }
    }

    /// The array items for mutation, copying them first when shared.
    pub fn as_array_mut(&mut self) -> Option<&mut Vec<JsonValue>> {
        match self {
            Self::Array(items) => Some(Arc::make_mut(items)),
            _ => None,
        }
    }

    /// The object for mutation, copying it first when shared.
    pub fn as_object_mut(&mut self) -> Option<&mut JsonObject> {
        match self {
            Self::Object(object) => Some(Arc::make_mut(object)),
            _ => None,
        }
    }

    /// An object's own value for `key`.
    #[must_use]
    pub fn get(&self, key: &str) -> Option<&JsonValue> {
        self.as_object().and_then(|object| object.get(key))
    }

    /// An array's item at `index`.
    #[must_use]
    pub fn get_index(&self, index: usize) -> Option<&JsonValue> {
        self.as_array().and_then(|items| items.get(index))
    }

    /// JS `===`: containers compare by identity, primitives by value
    /// (`0 === -0`).
    #[must_use]
    pub fn strict_equals(&self, other: &JsonValue) -> bool {
        match (self, other) {
            (Self::Null, Self::Null) => true,
            (Self::Bool(left), Self::Bool(right)) => left == right,
            (Self::Number(left), Self::Number(right)) => left == right,
            (Self::String(left), Self::String(right)) => left == right,
            (Self::Array(left), Self::Array(right)) => Arc::ptr_eq(left, right),
            (Self::Object(left), Self::Object(right)) => Arc::ptr_eq(left, right),
            _ => false,
        }
    }

    /// The container allocation address, the identity JS compares.
    pub(crate) fn container_address(&self) -> Option<usize> {
        match self {
            Self::Array(items) => Some(Arc::as_ptr(items) as usize),
            Self::Object(object) => Some(Arc::as_ptr(object).cast::<u8>() as usize),
            _ => None,
        }
    }

    /// A weak handle to this container's allocation, for retention checks.
    #[cfg(test)]
    pub(crate) fn downgrade(&self) -> Option<WeakContainer> {
        match self {
            Self::Array(items) => Some(WeakContainer::Array(Arc::downgrade(items))),
            Self::Object(object) => Some(WeakContainer::Object(Arc::downgrade(object))),
            _ => None,
        }
    }
}

/// A weak container reference observing whether an allocation is released.
#[cfg(test)]
pub(crate) enum WeakContainer {
    Array(std::sync::Weak<Vec<JsonValue>>),
    Object(std::sync::Weak<JsonObject>),
}

#[cfg(test)]
impl WeakContainer {
    pub(crate) fn is_alive(&self) -> bool {
        match self {
            Self::Array(weak) => weak.strong_count() > 0,
            Self::Object(weak) => weak.strong_count() > 0,
        }
    }
}

impl PartialEq for JsonValue {
    /// Deep JSON equality ignoring object key order (`0 == -0`).
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Array(left), Self::Array(right)) => Arc::ptr_eq(left, right) || left == right,
            (Self::Object(left), Self::Object(right)) => Arc::ptr_eq(left, right) || left == right,
            _ => self.strict_equals(other),
        }
    }
}

impl fmt::Display for JsonValue {
    /// `JSON.stringify(value)`.
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut text = String::new();
        write_json(&mut text, self);
        formatter.write_str(&text)
    }
}

impl fmt::Debug for JsonValue {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, formatter)
    }
}

impl std::ops::Index<&str> for JsonValue {
    type Output = JsonValue;

    /// The object's value for `key`, or `null` when absent.
    fn index(&self, key: &str) -> &JsonValue {
        self.get(key).unwrap_or(&NULL)
    }
}

impl std::ops::Index<usize> for JsonValue {
    type Output = JsonValue;

    /// The array's item at `index`, or `null` when absent.
    fn index(&self, index: usize) -> &JsonValue {
        self.get_index(index).unwrap_or(&NULL)
    }
}

impl From<bool> for JsonValue {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}

macro_rules! exact_number_from {
    ($($source:ty),*) => {$(
        impl From<$source> for JsonValue {
            fn from(value: $source) -> Self {
                Self::Number(JsonNumber::from(value))
            }
        }
    )*};
}
exact_number_from!(i8, i16, i32, u8, u16, u32);

impl From<JsonNumber> for JsonValue {
    fn from(value: JsonNumber) -> Self {
        Self::Number(value)
    }
}

impl TryFrom<f64> for JsonValue {
    type Error = JsonError;

    /// Fails for NaN and the infinities.
    fn try_from(value: f64) -> Result<Self, JsonError> {
        JsonNumber::new(value)
            .map(Self::Number)
            .ok_or(JsonError::NonFinite)
    }
}

macro_rules! safe_integer_try_from {
    ($($source:ty),*) => {$(
        impl TryFrom<$source> for JsonValue {
            type Error = JsonError;

            /// Fails beyond `Number.MAX_SAFE_INTEGER`, where doubles lose integers.
            fn try_from(value: $source) -> Result<Self, JsonError> {
                to_json(&value)
            }
        }
    )*};
}
safe_integer_try_from!(i64, u64, isize, usize);

impl From<&str> for JsonValue {
    fn from(value: &str) -> Self {
        Self::String(Arc::from(value))
    }
}

impl From<String> for JsonValue {
    fn from(value: String) -> Self {
        Self::String(Arc::from(value))
    }
}

impl From<Arc<str>> for JsonValue {
    fn from(value: Arc<str>) -> Self {
        Self::String(value)
    }
}

impl From<JsonObject> for JsonValue {
    fn from(value: JsonObject) -> Self {
        Self::Object(Arc::new(value))
    }
}

impl<T: Into<JsonValue>> From<Vec<T>> for JsonValue {
    fn from(value: Vec<T>) -> Self {
        Self::Array(Arc::new(value.into_iter().map(Into::into).collect()))
    }
}

impl<T: Into<JsonValue>> From<Option<T>> for JsonValue {
    /// `None` is `null`.
    fn from(value: Option<T>) -> Self {
        value.map_or(Self::Null, Into::into)
    }
}

impl<K: Into<Arc<str>>, V: Into<JsonValue>> From<std::collections::BTreeMap<K, V>> for JsonValue {
    fn from(value: std::collections::BTreeMap<K, V>) -> Self {
        Self::Object(Arc::new(value.into_iter().collect()))
    }
}

impl<T: Into<JsonValue>> FromIterator<T> for JsonValue {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::Array(Arc::new(iter.into_iter().map(Into::into).collect()))
    }
}

/// Copy a value into an alias-free strict-JSON tree owned by the caller
/// (`copyJson`): every container is a fresh allocation, so a container placed
/// at two paths becomes two independent containers.
///
/// `copyJson`'s validation of JS values (cycles, accessors, symbols, sparse
/// arrays, `undefined`) has no Rust counterpart: [`JsonValue`] is strict by
/// construction. Its `omitUndefinedProperties` option maps to [`to_json`] of a
/// record whose optional fields use `skip_serializing_if`.
#[must_use]
pub fn copy_json(value: &JsonValue) -> JsonValue {
    match value {
        JsonValue::Array(items) => {
            JsonValue::Array(Arc::new(items.iter().map(copy_json).collect()))
        }
        JsonValue::Object(object) => JsonValue::Object(Arc::new(
            object
                .shared_iter()
                .map(|(key, value)| (Arc::clone(key), copy_json(value)))
                .collect(),
        )),
        primitive => primitive.clone(),
    }
}

/// Whether untrusted `serde_json` data is finite strict JSON (`isJsonValue`):
/// every number must be a finite double. Cycles, prototypes, accessors, and
/// `undefined` cannot occur in `serde_json::Value`.
#[must_use]
pub fn is_json_value(value: &serde_json::Value) -> bool {
    match value {
        serde_json::Value::Null | serde_json::Value::Bool(_) | serde_json::Value::String(_) => true,
        serde_json::Value::Number(number) => number.as_f64().is_some_and(f64::is_finite),
        serde_json::Value::Array(items) => items.iter().all(is_json_value),
        serde_json::Value::Object(map) => map.values().all(is_json_value),
    }
}
