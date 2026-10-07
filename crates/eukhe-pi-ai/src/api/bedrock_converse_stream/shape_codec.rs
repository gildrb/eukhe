//! Schema-driven JSON shaping of `ConverseStream` bodies, as the AWS SDK's
//! `awsRestJson1` codec does it (`JsonShapeSerializer2` for the request body,
//! `JsonShapeDeserializer2` for event payloads): structure members in schema
//! order, absent and `null` members dropped, unknown members dropped (kept
//! only behind a string `__type`), unknown union members as `$unknown`.
//!
//! Blobs are carried as base64 strings on both sides (the SDK's wire form);
//! TS hands `Uint8Array`s to `onPayload` and `onProviderStreamEvent`, which
//! JSON cannot represent. Received blobs are still validated like the SDK's
//! `fromBase64`.

// Blob validation failures are the thrown JS `TypeError`s (`ErrorObject`);
// cold path.
#![allow(clippy::result_large_err)]

use std::sync::LazyLock;

use eukhe_types::pi_ai::{JsonObject, JsonValue};
use regex::Regex;

use crate::utils::diagnostics::ErrorObject;

/// The SDK's `BASE64_REGEX`.
static BASE64: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"^[A-Za-z0-9+/]*={0,2}$").unwrap_or_else(|_| unreachable!("static regex"))
});
/// A Smithy shape.
pub(crate) enum Shape {
    String,
    Number,
    Boolean,
    /// Bytes, carried as a base64 string.
    Blob,
    /// An open JSON document.
    Document,
    List(&'static Shape),
    Map(&'static Shape),
    Struct(&'static StructShape),
    Union(&'static StructShape),
}

/// The members of a structure or union shape, in schema order.
pub(crate) struct StructShape {
    /// The shape name (for error structures: the exception name).
    pub(crate) name: &'static str,
    pub(crate) members: &'static [(&'static str, Shape)],
}

impl StructShape {
    /// The shape of member `name`.
    pub(crate) fn member(&self, name: &str) -> Option<&'static Shape> {
        self.members
            .iter()
            .find(|(member, _)| *member == name)
            .map(|(_, shape)| shape)
    }
}

/// `JsonShapeSerializer2.writeValue` for a structure root.
pub(crate) fn serialize_struct(shape: &StructShape, union: bool, value: &JsonObject) -> JsonObject {
    let mut out = JsonObject::new();
    for (name, member) in shape.members {
        match value.get(*name) {
            None | Some(JsonValue::Null) => {}
            Some(item) => {
                out.insert((*name).to_owned(), serialize(member, item));
            }
        }
    }
    if out.is_empty() && union {
        if let Some(JsonValue::Array(unknown)) = value.get("$unknown") {
            if let [JsonValue::String(key), item, ..] = unknown.as_slice() {
                out.insert(key.clone(), item.clone());
            } else if let [JsonValue::String(key)] = unknown.as_slice() {
                out.insert(key.clone(), JsonValue::Null);
            }
        }
    } else if matches!(value.get("__type"), Some(JsonValue::String(_))) {
        for (key, item) in value {
            if !out.contains_key(key) {
                out.insert(key.clone(), item.clone());
            }
        }
    }
    out
}

/// `JsonShapeSerializer2.writeValue` for a nested value.
fn serialize(shape: &Shape, value: &JsonValue) -> JsonValue {
    match (shape, value) {
        (Shape::Struct(members), JsonValue::Object(object)) => {
            JsonValue::Object(serialize_struct(members, false, object))
        }
        (Shape::Union(members), JsonValue::Object(object)) => {
            JsonValue::Object(serialize_struct(members, true, object))
        }
        (Shape::List(item_shape), JsonValue::Array(items)) => JsonValue::Array(
            items
                .iter()
                .filter(|item| !item.is_null())
                .map(|item| serialize(item_shape, item))
                .collect(),
        ),
        (Shape::Map(value_shape), JsonValue::Object(entries)) => JsonValue::Object(
            entries
                .iter()
                .filter(|(_, item)| !item.is_null())
                .map(|(key, item)| (key.clone(), serialize(value_shape, item)))
                .collect(),
        ),
        // Documents, scalars, blobs (already base64), and values whose JSON
        // type does not match the shape are written as they are.
        _ => value.clone(),
    }
}
/// `JsonShapeDeserializer2._readStruct`.
///
/// # Errors
///
/// The SDK's `fromBase64` `TypeError` for a malformed blob.
pub(crate) fn deserialize_struct(
    shape: &StructShape,
    union: bool,
    record: &JsonObject,
) -> Result<JsonObject, ErrorObject> {
    let mut out = JsonObject::new();
    let mut unmarked: Vec<&String> = record.keys().filter(|key| *key != "__type").collect();
    for (name, member) in shape.members {
        unmarked.retain(|key| key.as_str() != *name);
        match record.get(*name) {
            None | Some(JsonValue::Null) => {}
            Some(item) => {
                out.insert((*name).to_owned(), deserialize(member, item)?);
            }
        }
    }
    if union {
        if let [key] = unmarked.as_slice() {
            if out.is_empty() {
                let item = record.get(key.as_str()).cloned().unwrap_or(JsonValue::Null);
                out.insert(
                    "$unknown".to_owned(),
                    JsonValue::Array(vec![JsonValue::String((*key).clone()), item]),
                );
            }
        }
    } else if matches!(record.get("__type"), Some(JsonValue::String(_))) {
        for (key, item) in record {
            if !out.contains_key(key) {
                out.insert(key.clone(), item.clone());
            }
        }
    }
    Ok(out)
}

/// `JsonShapeDeserializer2._read`.
fn deserialize(shape: &Shape, value: &JsonValue) -> Result<JsonValue, ErrorObject> {
    Ok(match (shape, value) {
        (Shape::Struct(members), JsonValue::Object(object)) => {
            JsonValue::Object(deserialize_struct(members, false, object)?)
        }
        (Shape::Union(members), JsonValue::Object(object)) => {
            JsonValue::Object(deserialize_struct(members, true, object)?)
        }
        (Shape::List(item_shape), JsonValue::Array(items)) => JsonValue::Array(
            items
                .iter()
                .map(|item| deserialize(item_shape, item))
                .collect::<Result<_, _>>()?,
        ),
        (Shape::Map(value_shape), JsonValue::Object(entries)) => JsonValue::Object(
            entries
                .iter()
                .map(|(key, item)| Ok((key.clone(), deserialize(value_shape, item)?)))
                .collect::<Result<_, ErrorObject>>()?,
        ),
        (Shape::Blob, JsonValue::String(text)) => {
            // `fromBase64`: the length check counts UTF-16 code units.
            if !(crate::utils::js::utf16_len(text) * 3).is_multiple_of(4) {
                return Err(ErrorObject::named(
                    "TypeError",
                    "Incorrect padding on base64 string.",
                ));
            }
            if !BASE64.is_match(text) {
                return Err(ErrorObject::named("TypeError", "Invalid base64 string."));
            }
            value.clone()
        }
        _ => value.clone(),
    })
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::super::smithy_schema::{REQUEST, STREAM_OUTPUT};
    use super::*;

    fn object(value: JsonValue) -> JsonObject {
        match value {
            JsonValue::Object(object) => object,
            other => panic!("expected an object, got {other}"),
        }
    }

    #[test]
    fn serializes_members_in_schema_order_and_drops_unknown_keys() {
        let payload = object(json!({
            "modelId": "m",
            "inferenceConfig": {},
            "messages": [{
                "content": [
                    { "image": { "source": { "bytes": "AAE=" }, "format": "png" } },
                    { "cachePoint": { "type": "default", "ttl": null } },
                ],
                "role": "user",
                "extra": 1,
            }],
            "system": null,
        }));
        assert_eq!(
            JsonValue::Object(serialize_struct(REQUEST, false, &payload)),
            json!({
                "messages": [{
                    "role": "user",
                    "content": [
                        { "image": { "format": "png", "source": { "bytes": "AAE=" } } },
                        { "cachePoint": { "type": "default" } },
                    ],
                }],
                "inferenceConfig": {},
            })
        );
    }

    #[test]
    fn keeps_documents_verbatim() {
        let payload = object(json!({
            "additionalModelRequestFields": { "z": null, "a": [null, 1] },
        }));
        assert_eq!(
            JsonValue::Object(serialize_struct(REQUEST, false, &payload)),
            json!({ "additionalModelRequestFields": { "z": null, "a": [null, 1] } })
        );
    }

    #[test]
    fn deserializes_events_in_schema_order() {
        let event = object(json!({
            "contentBlockDelta": { "contentBlockIndex": 0, "delta": { "text": "hi" }, "p": "abc" },
        }));
        assert_eq!(
            deserialize_struct(STREAM_OUTPUT, true, &event).map(JsonValue::Object),
            Ok(
                json!({ "contentBlockDelta": { "delta": { "text": "hi" }, "contentBlockIndex": 0 } })
            )
        );
    }

    #[test]
    fn marks_unknown_union_members() {
        let event = object(json!({
            "contentBlockDelta": { "contentBlockIndex": 0, "delta": { "hologram": 1 } },
        }));
        assert_eq!(
            deserialize_struct(STREAM_OUTPUT, true, &event).map(JsonValue::Object),
            Ok(
                json!({ "contentBlockDelta": { "delta": { "$unknown": ["hologram", 1] }, "contentBlockIndex": 0 } })
            )
        );
    }

    #[test]
    fn validates_blobs_like_from_base64() {
        let event = object(json!({
            "contentBlockDelta": { "delta": { "reasoningContent": { "redactedContent": "AAE" } } },
        }));
        assert_eq!(
            deserialize_struct(STREAM_OUTPUT, true, &event),
            Err(ErrorObject::named(
                "TypeError",
                "Incorrect padding on base64 string."
            ))
        );
    }
}
