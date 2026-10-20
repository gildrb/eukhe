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

/// Check `value` against `schema`; the first mismatch, with its path.
///
/// # Errors
///
/// The first mismatch, as `<path>: <reason>`.
pub(crate) fn validate(value: &Value, schema: &Value) -> Result<(), String> {
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

fn check(value: &Value, schema: &Value, path: &str) -> Result<(), String> {
    let Value::Object(schema) = schema else {
        return Ok(());
    };
    match schema.get("type") {
        Some(Value::String(name)) if !has_type(value, name) => {
            return Err(format!("{path}: expected {name}, got {}", type_name(value)));
        }
        Some(Value::Array(names))
            if !names
                .iter()
                .filter_map(Value::as_str)
                .any(|name| has_type(value, name)) =>
        {
            return Err(format!(
                "{path}: expected one of {}, got {}",
                Value::Array(names.clone()),
                type_name(value)
            ));
        }
        Some(_) | None => {}
    }
    if let Some(Value::Array(options)) = schema.get("enum") {
        if !options.contains(value) {
            return Err(format!(
                "{path}: {value} is not one of {}",
                Value::Array(options.clone())
            ));
        }
    }
    if let Some(expected) = schema.get("const") {
        if expected != value {
            return Err(format!("{path}: expected {expected}"));
        }
    }
    match value {
        Value::Object(object) => {
            if let Some(Value::Array(required)) = schema.get("required") {
                for key in required.iter().filter_map(Value::as_str) {
                    if !object.contains_key(key) {
                        return Err(format!("{path}: missing required property {key}"));
                    }
                }
            }
            let properties = schema.get("properties").and_then(Value::as_object);
            for (key, item) in object {
                match properties.and_then(|properties| properties.get(key)) {
                    Some(property) => check(item, property, &format!("{path}.{key}"))?,
                    None => {
                        if schema.get("additionalProperties") == Some(&Value::Bool(false)) {
                            return Err(format!("{path}: unexpected property {key}"));
                        }
                    }
                }
            }
        }
        Value::Array(items) => {
            let length = items.len() as u64;
            if let Some(min) = schema.get("minItems").and_then(Value::as_u64) {
                if length < min {
                    return Err(format!("{path}: expected at least {min} items"));
                }
            }
            if let Some(max) = schema.get("maxItems").and_then(Value::as_u64) {
                if length > max {
                    return Err(format!("{path}: expected at most {max} items"));
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
            validate(&json!({"findings": [{"severity": "high"}]}), &schema),
            Ok(())
        );
        assert_eq!(
            validate(&json!({"findings": [{"severity": "mid"}]}), &schema),
            Err("$.findings[0].severity: \"mid\" is not one of [\"high\",\"low\"]".to_owned())
        );
        assert_eq!(
            validate(&json!({}), &schema),
            Err("$: missing required property findings".to_owned())
        );
    }
}
