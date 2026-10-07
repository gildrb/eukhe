//! Port of `src/utils/typebox-helpers.ts`.

use eukhe_types::pi_ai::JsonObject;
use serde_json::json;

use crate::typebox::{TSchema, Type};

/// Creates a string enum schema compatible with Google's API and other
/// providers that don't support `anyOf`/`const` patterns:
/// `Type.Unsafe({ type: "string", enum: values, description?, default? })`.
///
/// As in the TS (`options?.description && ...`), an empty `description` or
/// `default` is omitted.
///
/// ```
/// use eukhe_pi_ai::utils::typebox_helpers::string_enum;
///
/// let schema = string_enum(&["add", "subtract"], Some("The operation to perform"), None);
/// assert_eq!(
///     schema.json(),
///     &serde_json::json!({
///         "type": "string",
///         "enum": ["add", "subtract"],
///         "description": "The operation to perform"
///     })
/// );
/// ```
#[must_use]
pub fn string_enum(values: &[&str], description: Option<&str>, default: Option<&str>) -> TSchema {
    let mut schema = JsonObject::new();
    schema.insert("type".to_owned(), json!("string"));
    schema.insert("enum".to_owned(), json!(values));
    if let Some(description) = description.filter(|description| !description.is_empty()) {
        schema.insert("description".to_owned(), json!(description));
    }
    if let Some(default) = default.filter(|default| !default.is_empty()) {
        schema.insert("default".to_owned(), json!(default));
    }
    Type::unsafe_(schema)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_enum_without_options_is_type_and_enum() {
        let schema = string_enum(&["a", "b"], None, None);
        assert_eq!(
            serde_json::to_string(schema.json()).expect("serializes"),
            r#"{"type":"string","enum":["a","b"]}"#
        );
        assert_eq!(
            schema.typebox(),
            &json!({ "type": "string", "enum": ["a", "b"], "~unsafe": null })
        );
    }

    #[test]
    fn string_enum_writes_description_then_default() {
        let schema = string_enum(&["a", "b"], Some("pick one"), Some("b"));
        assert_eq!(
            serde_json::to_string(schema.json()).expect("serializes"),
            r#"{"type":"string","enum":["a","b"],"description":"pick one","default":"b"}"#
        );
    }

    #[test]
    fn string_enum_omits_empty_options() {
        assert_eq!(
            string_enum(&["a"], Some(""), Some("")).json(),
            &json!({ "type": "string", "enum": ["a"] })
        );
    }
}
