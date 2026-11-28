//! The tag fields of wire JSON objects (`type`, `role`, ...), parsed into the
//! caller's enum of known tags.

use serde::de::value::{Error, StrDeserializer};
use serde::de::IntoDeserializer;
use serde::Deserialize;
use serde_json::Value as JsonValue;

/// `value.type` as `T` ([`wire_tag`]).
pub(crate) fn wire_type<'a, T: Deserialize<'a>>(value: &'a JsonValue) -> Option<T> {
    wire_tag(value, "type")
}

/// `value[key]` as `T`; `None` when the field is absent, not a string, or
/// not a tag `T` names.
pub(crate) fn wire_tag<'a, T: Deserialize<'a>>(value: &'a JsonValue, key: &str) -> Option<T> {
    value
        .get(key)
        .and_then(JsonValue::as_str)
        .and_then(parse_tag)
}

/// `tag` as `T`; `None` when `T` names no such tag.
pub(crate) fn parse_tag<'a, T: Deserialize<'a>>(tag: &'a str) -> Option<T> {
    let deserializer: StrDeserializer<'a, Error> = tag.into_deserializer();
    T::deserialize(deserializer).ok()
}
