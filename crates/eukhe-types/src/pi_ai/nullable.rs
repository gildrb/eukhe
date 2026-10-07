//! Serde helper for TS fields typed `T | null` that are also optional: the
//! outer `Option` is presence, the inner one is the explicit `null`.
//! Use with `#[serde(default, skip_serializing_if = "Option::is_none", with = "nullable")]`.

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Serialize a present field: `Some(None)` as `null`, `Some(Some(v))` as `v`.
///
/// # Errors
///
/// Returns the serializer's error.
// serde's `with` contract passes the field by reference.
#[allow(clippy::ref_option)]
pub fn serialize<S: Serializer, T: Serialize>(
    value: &Option<Option<T>>,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    match value {
        Some(Some(inner)) => inner.serialize(serializer),
        Some(None) | None => serializer.serialize_none(),
    }
}

/// Deserialize a present field; absence is handled by `#[serde(default)]`.
///
/// # Errors
///
/// Returns the deserializer's error.
pub fn deserialize<'de, D: Deserializer<'de>, T: Deserialize<'de>>(
    deserializer: D,
) -> Result<Option<Option<T>>, D::Error> {
    Option::<T>::deserialize(deserializer).map(Some)
}
