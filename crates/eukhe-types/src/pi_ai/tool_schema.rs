//! TS `TSchema` as a tool's `parameters`: the JSON Schema sent on the wire,
//! plus — for schemas built with `eukhe_pi_ai::typebox::Type` — the
//! non-enumerable markers `TypeBox` attaches to every node (`~kind`,
//! `~optional`, `~readonly`, `~unsafe`).
//!
//! The markers never reach the wire (`JSON.stringify` skips non-enumerable
//! properties), but `Value.Convert` dispatches on `~kind`, so tool argument
//! validation converts `TypeBox`-built schemas and leaves plain JSON schemas
//! alone, exactly like the TS.

use std::ops::Deref;

use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::JsonValue;

/// A tool parameter schema.
///
/// Equality compares the wire JSON and the `TypeBox` view: a `TypeBox`-built
/// schema and the same JSON parsed from the wire are different values,
/// because argument validation treats them differently.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ToolSchema {
    json: JsonValue,
    typebox: Option<JsonValue>,
}

impl ToolSchema {
    /// A `TypeBox`-built schema: `json` is the serialized schema, `typebox`
    /// the same document with each node's non-enumerable markers as keys.
    #[must_use]
    pub fn from_typebox(json: JsonValue, typebox: JsonValue) -> Self {
        Self {
            json,
            typebox: Some(typebox),
        }
    }

    /// The JSON Schema as serialized (`JSON.stringify(parameters)`).
    #[must_use]
    pub fn json(&self) -> &JsonValue {
        &self.json
    }

    /// The JSON Schema as serialized, by value.
    #[must_use]
    pub fn into_json(self) -> JsonValue {
        self.json
    }

    /// The `TypeBox` view (markers inline), for `TypeBox`-built schemas.
    #[must_use]
    pub fn typebox(&self) -> Option<&JsonValue> {
        self.typebox.as_ref()
    }
}

impl Deref for ToolSchema {
    type Target = JsonValue;

    fn deref(&self) -> &JsonValue {
        &self.json
    }
}

/// A plain JSON Schema (no `TypeBox` markers).
impl From<JsonValue> for ToolSchema {
    fn from(json: JsonValue) -> Self {
        Self {
            json,
            typebox: None,
        }
    }
}

impl From<ToolSchema> for JsonValue {
    fn from(schema: ToolSchema) -> Self {
        schema.json
    }
}

impl Serialize for ToolSchema {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.json.serialize(serializer)
    }
}

/// Parsed schemas are plain JSON: the markers do not survive serialization.
impl<'de> Deserialize<'de> for ToolSchema {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        JsonValue::deserialize(deserializer).map(Self::from)
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn serializes_only_the_wire_json() {
        let schema = ToolSchema::from_typebox(
            json!({ "type": "string" }),
            json!({ "type": "string", "~kind": "String" }),
        );
        assert_eq!(
            serde_json::to_string(&schema).ok().as_deref(),
            Some(r#"{"type":"string"}"#)
        );
        assert_eq!(schema.get("type"), Some(&json!("string")));
        assert_eq!(
            schema.typebox(),
            Some(&json!({ "type": "string", "~kind": "String" }))
        );
    }

    #[test]
    fn round_trip_drops_the_typebox_view() {
        let schema = ToolSchema::from_typebox(
            json!({ "type": "string" }),
            json!({ "type": "string", "~kind": "String" }),
        );
        let parsed: ToolSchema =
            serde_json::from_value(serde_json::to_value(&schema).unwrap_or_default())
                .unwrap_or_default();
        assert_eq!(parsed, ToolSchema::from(json!({ "type": "string" })));
        assert_ne!(parsed, schema);
        assert_eq!(parsed.typebox(), None);
    }
}
