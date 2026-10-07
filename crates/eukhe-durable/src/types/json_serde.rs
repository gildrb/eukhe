//! Serde adapters for the shared JSON shapes of durable records.

use std::sync::Arc;

use eukhe_chord::json::{JsonObject, JsonValue};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// `Arc<JsonObject>` as a JSON object, shared without copying.
pub(crate) mod object {
    use super::{Arc, Deserialize, Deserializer, JsonObject, JsonValue, Serializer};

    pub(crate) fn serialize<S: Serializer>(
        value: &JsonObject,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serializer.collect_map(value.iter())
    }

    pub(crate) fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Arc<JsonObject>, D::Error> {
        super::into_object(JsonValue::deserialize(deserializer)?)
    }
}

/// `Option<Arc<JsonObject>>`; absent is `None`.
pub(crate) mod option_object {
    use super::{Arc, Deserialize, Deserializer, JsonObject, JsonValue, Serializer};

    #[expect(
        clippy::ref_option,
        reason = "serde `with` adapters receive `&Option<T>`"
    )]
    pub(crate) fn serialize<S: Serializer>(
        value: &Option<Arc<JsonObject>>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        match value {
            Some(object) => serializer.collect_map(object.iter()),
            None => serializer.serialize_none(),
        }
    }

    pub(crate) fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Option<Arc<JsonObject>>, D::Error> {
        super::into_object(JsonValue::deserialize(deserializer)?).map(Some)
    }
}

/// An optional field whose present value is kept even when it is `null`
/// (`Option<JsonValue>` would read `null` as absent). Use with
/// `#[serde(default)]`.
pub(crate) fn present<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    T::deserialize(deserializer).map(Some)
}

/// The object inside `value`, or a deserialization error.
pub(crate) fn into_object<E: serde::de::Error>(value: JsonValue) -> Result<Arc<JsonObject>, E> {
    match value {
        JsonValue::Object(object) => Ok(object),
        other => Err(E::custom(format!("expected a JSON object, found {other}"))),
    }
}

/// Serialize an `Arc<JsonObject>` field value inside a hand-written struct serializer.
pub(crate) struct ObjectRef<'a>(pub(crate) &'a JsonObject);

impl Serialize for ObjectRef<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_map(self.0.iter())
    }
}

/// Reject a field a TS union member declares `?: never`.
pub(crate) fn forbidden<E: serde::de::Error, T>(
    field: Option<&T>,
    name: &str,
    member: &str,
) -> Result<(), E> {
    if field.is_some() {
        return Err(E::custom(format!("{member} cannot carry `{name}`")));
    }
    Ok(())
}

/// Require a field a TS union member declares as present.
pub(crate) fn required<E: serde::de::Error, T>(
    field: Option<T>,
    name: &str,
    member: &str,
) -> Result<T, E> {
    field.ok_or_else(|| E::custom(format!("{member} requires `{name}`")))
}
