//! JSON parsing for provider streams: `JSON.parse` with string-literal repair,
//! and best-effort parsing of incomplete streaming JSON.

mod js_json;
mod partial;

use eukhe_types::pi_ai::{JsonObject, JsonValue};

/// JS `JSON.parse(text)` without repair.
pub(crate) use js_json::parse as js_json_parse;
pub use js_json::JsonSyntaxError;

use crate::utils::js::js_trim;

const VALID_JSON_ESCAPES: &[u8] = b"\"\\/bfnrtu";

/// Escape one raw control character (U+0000..U+001F) inside a string literal.
fn push_escaped_control(byte: u8, repaired: &mut Vec<u8>) {
    match byte {
        0x08 => repaired.extend_from_slice(b"\\b"),
        0x0C => repaired.extend_from_slice(b"\\f"),
        b'\n' => repaired.extend_from_slice(b"\\n"),
        b'\r' => repaired.extend_from_slice(b"\\r"),
        b'\t' => repaired.extend_from_slice(b"\\t"),
        _ => repaired.extend_from_slice(format!("\\u{byte:04x}").as_bytes()),
    }
}

/// Repair malformed JSON string literals by escaping raw control characters
/// inside strings and doubling backslashes before invalid escape characters.
#[must_use]
pub fn repair_json(json: &str) -> String {
    let bytes = json.as_bytes();
    let mut repaired: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut in_string = false;
    let mut index = 0;
    while index < bytes.len() {
        let byte = bytes[index];
        if !in_string {
            repaired.push(byte);
            if byte == b'"' {
                in_string = true;
            }
            index += 1;
            continue;
        }
        if byte == b'"' {
            repaired.push(byte);
            in_string = false;
            index += 1;
            continue;
        }
        if byte == b'\\' {
            let Some(&next) = bytes.get(index + 1) else {
                repaired.extend_from_slice(b"\\\\");
                index += 1;
                continue;
            };
            if next == b'u' {
                let digits = bytes.get(index + 2..index + 6);
                if let Some(digits) =
                    digits.filter(|digits| digits.iter().all(u8::is_ascii_hexdigit))
                {
                    repaired.extend_from_slice(b"\\u");
                    repaired.extend_from_slice(digits);
                    index += 6;
                    continue;
                }
            }
            if VALID_JSON_ESCAPES.contains(&next) {
                repaired.push(b'\\');
                repaired.push(next);
                index += 2;
                continue;
            }
            repaired.extend_from_slice(b"\\\\");
            index += 1;
            continue;
        }
        if byte <= 0x1F {
            push_escaped_control(byte, &mut repaired);
        } else {
            repaired.push(byte);
        }
        index += 1;
    }
    // Only ASCII bytes were inserted, between whole UTF-8 sequences.
    String::from_utf8(repaired)
        .unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned())
}

/// JS `JSON.parse(text)` (no reviver).
///
/// # Errors
///
/// The `SyntaxError` for malformed JSON.
pub fn json_parse(text: &str) -> Result<JsonValue, JsonSyntaxError> {
    js_json::parse(text)
}

/// `JSON.parse(json)`, retried once on the repaired text when repair changes it.
///
/// # Errors
///
/// The `SyntaxError` of the original text when repair changes nothing,
/// otherwise the error of the repaired text.
pub fn parse_json_with_repair(json: &str) -> Result<JsonValue, JsonSyntaxError> {
    js_json::parse(json).or_else(|error| {
        let repaired = repair_json(json);
        if repaired == json {
            Err(error)
        } else {
            js_json::parse(&repaired)
        }
    })
}

/// Parse potentially incomplete JSON during streaming. Always returns a
/// value: `{}` for empty input or when nothing can be recovered.
#[must_use]
pub fn parse_streaming_json(partial_json: Option<&str>) -> JsonValue {
    let Some(partial_json) = partial_json.filter(|json| !js_trim(json).is_empty()) else {
        return JsonValue::Object(JsonObject::new());
    };
    if let Ok(value) = parse_json_with_repair(partial_json) {
        return value;
    }
    let recovered =
        partial::parse(partial_json).or_else(|_| partial::parse(&repair_json(partial_json)));
    match recovered {
        Ok(JsonValue::Null) | Err(_) => JsonValue::Object(JsonObject::new()),
        Ok(value) => value,
    }
}

/// [`parse_streaming_json`] for tool-call arguments, typed `JsonObject`.
///
/// TS stores whatever the parse yields; a non-object result (only possible
/// for non-object argument JSON such as `[1]` or `"x"`) cannot be a
/// `JsonObject` and becomes `{}`.
#[must_use]
pub fn parse_streaming_json_object(partial_json: Option<&str>) -> JsonObject {
    match parse_streaming_json(partial_json) {
        JsonValue::Object(object) => object,
        JsonValue::Null
        | JsonValue::Bool(_)
        | JsonValue::Number(_)
        | JsonValue::String(_)
        | JsonValue::Array(_) => JsonObject::new(),
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn repairs_control_characters_and_invalid_escapes() {
        assert_eq!(repair_json("{\"a\":\"x\ny\"}"), "{\"a\":\"x\\ny\"}");
        assert_eq!(repair_json(r#"{"a":"C:\path"}"#), r#"{"a":"C:\\path"}"#);
        assert_eq!(repair_json(r#"{"a":"\u00e9\q"}"#), r#"{"a":"\u00e9\\q"}"#);
        assert_eq!(repair_json("\"\u{1}\""), "\"\\u0001\"");
        assert_eq!(repair_json("\"ab\\"), "\"ab\\\\");
        assert_eq!(
            parse_json_with_repair(r#"{"a":"C:\path"}"#).unwrap(),
            json!({"a": "C:\\path"})
        );
    }

    #[test]
    fn parses_streaming_json() {
        assert_eq!(parse_streaming_json(None), json!({}));
        assert_eq!(parse_streaming_json(Some("  ")), json!({}));
        assert_eq!(
            parse_streaming_json(Some(r#"{"path": "a.t"#)),
            json!({"path": "a.t"})
        );
        assert_eq!(parse_streaming_json(Some("null")), JsonValue::Null);
        assert_eq!(parse_streaming_json_object(Some("[1]")), JsonObject::new());
    }
}
