//! Structured agent output: the JSON value at the end of an answer, and a
//! validator for the JSON Schema subset workflow scripts use (`type`,
//! `enum`, `const`, `required`, `properties`, `additionalProperties:
//! false`, `items`, `minItems`, `maxItems`). Other keywords are ignored.

use serde_json::Value;

/// The JSON value an answer ends with: its last fenced block that parses
/// (```` ```json ```` or a bare fence), else the whole answer, else the
/// span from its first `{` or `[` to its last `}` or `]`.
pub(crate) fn extract_json(answer: &str) -> Option<Value> {
    let mut blocks = Vec::new();
    let mut rest = answer;
    while let Some(open) = rest.find("```") {
        let after = &rest[open + 3..];
        let body_start = after.find('\n').map_or(after.len(), |line| line + 1);
        let body = &after[body_start..];
        let Some(close) = body.find("```") else {
            break;
        };
        blocks.push(&body[..close]);
        rest = &body[close + 3..];
    }
    for block in blocks.iter().rev() {
        if let Ok(value) = serde_json::from_str(block.trim()) {
            return Some(value);
        }
    }
    if let Ok(value) = serde_json::from_str(answer.trim()) {
        return Some(value);
    }
    let start = answer.find(['{', '['])?;
    let end = answer.rfind(['}', ']'])?;
    (start < end)
        .then(|| serde_json::from_str(&answer[start..=end]).ok())
        .flatten()
}

/// The first place a value does not match a schema: its path (`$`,
/// `$.key`, `$[0]`, ...) and why.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
#[error("{path}: {reason}")]
pub(crate) struct SchemaMismatch {
    pub(crate) path: String,
    pub(crate) reason: MismatchReason,
}

/// Why a value does not match its schema.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub(crate) enum MismatchReason {
    /// `type` names one type; the value has another.
    #[error("expected {expected}, got {got}")]
    Type { expected: String, got: &'static str },
    /// `type` lists types; the value has none of them.
    #[error("expected one of {}, got {got}", JsonList(.expected))]
    AnyType {
        expected: Vec<Value>,
        got: &'static str,
    },
    /// The value is not one of `enum`.
    #[error("{value} is not one of {}", JsonList(.options))]
    NotInEnum {
        value: Box<Value>,
        options: Vec<Value>,
    },
    /// The value is not `const`.
    #[error("expected {expected}")]
    NotConst { expected: Box<Value> },
    /// An object lacks a `required` property.
    #[error("missing required property {key}")]
    MissingRequired { key: String },
    /// An object has a property `properties` does not name, under
    /// `additionalProperties: false`.
    #[error("unexpected property {key}")]
    UnexpectedProperty { key: String },
    /// An array is shorter than `minItems`.
    #[error("expected at least {min} items")]
    TooFewItems { min: u64 },
    /// An array is longer than `maxItems`.
    #[error("expected at most {max} items")]
    TooManyItems { max: u64 },
}

/// Values shown as one compact JSON array.
struct JsonList<'a>(&'a [Value]);

impl std::fmt::Display for JsonList<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("[")?;
        for (index, item) in self.0.iter().enumerate() {
            if index > 0 {
                f.write_str(",")?;
            }
            write!(f, "{item}")?;
        }
        f.write_str("]")
    }
}

/// Check `value` against `schema`; the first mismatch, with its path.
///
/// # Errors
///
/// The first mismatch.
pub(crate) fn validate(value: &Value, schema: &Value) -> Result<(), SchemaMismatch> {
    check(value, schema, "$")
}

fn type_name(value: &Value) -> &'static str {
    match value {
        Value::Null => "null",
        Value::Bool(_) => "boolean",
        Value::Number(_) => "number",
        Value::String(_) => "string",
        Value::Array(_) => "array",
        Value::Object(_) => "object",
    }
}

fn has_type(value: &Value, name: &str) -> bool {
    match name {
        "integer" => value.as_i64().is_some() || value.as_u64().is_some(),
        other => type_name(value) == other,
    }
}

fn check(value: &Value, schema: &Value, path: &str) -> Result<(), SchemaMismatch> {
    let Value::Object(schema) = schema else {
        return Ok(());
    };
    let mismatch = |reason| {
        Err(SchemaMismatch {
            path: path.to_owned(),
            reason,
        })
    };
    match schema.get("type") {
        Some(Value::String(name)) if !has_type(value, name) => {
            return mismatch(MismatchReason::Type {
                expected: name.clone(),
                got: type_name(value),
            });
        }
        Some(Value::Array(names))
            if !names
                .iter()
                .filter_map(Value::as_str)
                .any(|name| has_type(value, name)) =>
        {
            return mismatch(MismatchReason::AnyType {
                expected: names.clone(),
                got: type_name(value),
            });
        }
        Some(_) | None => {}
    }
    if let Some(Value::Array(options)) = schema.get("enum") {
        if !options.contains(value) {
            return mismatch(MismatchReason::NotInEnum {
                value: Box::new(value.clone()),
                options: options.clone(),
            });
        }
    }
    if let Some(expected) = schema.get("const") {
        if expected != value {
            return mismatch(MismatchReason::NotConst {
                expected: Box::new(expected.clone()),
            });
        }
    }
    match value {
        Value::Object(object) => {
            if let Some(Value::Array(required)) = schema.get("required") {
                for key in required.iter().filter_map(Value::as_str) {
                    if !object.contains_key(key) {
                        return mismatch(MismatchReason::MissingRequired {
                            key: key.to_owned(),
                        });
                    }
                }
            }
            let properties = schema.get("properties").and_then(Value::as_object);
            for (key, item) in object {
                match properties.and_then(|properties| properties.get(key)) {
                    Some(property) => check(item, property, &format!("{path}.{key}"))?,
                    None => {
                        if schema.get("additionalProperties") == Some(&Value::Bool(false)) {
                            return mismatch(MismatchReason::UnexpectedProperty {
                                key: key.clone(),
                            });
                        }
                    }
                }
            }
        }
        Value::Array(items) => {
            let length = items.len() as u64;
            if let Some(min) = schema.get("minItems").and_then(Value::as_u64) {
                if length < min {
                    return mismatch(MismatchReason::TooFewItems { min });
                }
            }
            if let Some(max) = schema.get("maxItems").and_then(Value::as_u64) {
                if length > max {
                    return mismatch(MismatchReason::TooManyItems { max });
                }
            }
            if let Some(item_schema) = schema.get("items") {
                for (index, item) in items.iter().enumerate() {
                    check(item, item_schema, &format!("{path}[{index}]"))?;
                }
            }
        }
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn the_last_fenced_block_wins() {
        let answer = "first ```json\n{\"a\":1}\n``` then\n```json\n{\"a\":2}\n```";
        assert_eq!(extract_json(answer), Some(json!({"a": 2})));
        assert_eq!(
            extract_json("Result: {\"ok\": true}."),
            Some(json!({"ok": true}))
        );
        assert_eq!(extract_json("no json here"), None);
    }

    #[test]
    fn validates_the_subset() {
        let schema = json!({
            "type": "object",
            "required": ["findings"],
            "properties": {
                "findings": {
                    "type": "array",
                    "items": {
                        "type": "object",
                        "required": ["severity"],
                        "properties": { "severity": { "enum": ["high", "low"] } }
                    }
                }
            }
        });
        assert_eq!(
            validate(&json!({"findings": [{"severity": "high"}]}), &schema)
                .map_err(|e| e.to_string()),
            Ok(())
        );
        assert_eq!(
            validate(&json!({"findings": [{"severity": "mid"}]}), &schema)
                .map_err(|e| e.to_string()),
            Err("$.findings[0].severity: \"mid\" is not one of [\"high\",\"low\"]".to_owned())
        );
        assert_eq!(
            validate(&json!({}), &schema).map_err(|e| e.to_string()),
            Err("$: missing required property findings".to_owned())
        );
    }
}
