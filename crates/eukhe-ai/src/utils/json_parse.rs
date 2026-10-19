//! JSON parsing for provider streams: `JSON.parse` with string-literal repair
//! and a relaxed dialect, best-effort parsing of incomplete streaming JSON,
//! and the final parse of tool-call arguments.

mod js_json;
mod partial;
mod relaxed;

use std::borrow::Cow;

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

/// The output buffer of a repair: on the first change, `bytes[..at]` (the
/// unchanged prefix) is copied once; later splices append the untouched run
/// since the previous one. `copied` ends past the replaced byte at `at`.
fn splice<'a>(
    repaired: &'a mut Option<Vec<u8>>,
    bytes: &[u8],
    copied: &mut usize,
    at: usize,
) -> &'a mut Vec<u8> {
    let out = repaired.get_or_insert_with(|| Vec::with_capacity(bytes.len() + 8));
    out.extend_from_slice(&bytes[*copied..at]);
    *copied = at + 1;
    out
}

/// Repair malformed JSON string literals by escaping raw control characters
/// inside strings and doubling backslashes before invalid escape characters.
/// Borrows `json` when nothing needs repair.
#[must_use]
pub fn repair_json(json: &str) -> Cow<'_, str> {
    let bytes = json.as_bytes();
    let mut repaired = None;
    let mut copied = 0;
    let mut in_string = false;
    let mut index = 0;
    while index < bytes.len() {
        let byte = bytes[index];
        if !in_string || byte == b'"' {
            in_string ^= byte == b'"';
            index += 1;
            continue;
        }
        if byte == b'\\' {
            let Some(&next) = bytes.get(index + 1) else {
                splice(&mut repaired, bytes, &mut copied, index).extend_from_slice(b"\\\\");
                index += 1;
                continue;
            };
            let unicode_escape = next == b'u'
                && bytes
                    .get(index + 2..index + 6)
                    .is_some_and(|digits| digits.iter().all(u8::is_ascii_hexdigit));
            if unicode_escape {
                index += 6;
            } else if VALID_JSON_ESCAPES.contains(&next) {
                index += 2;
            } else {
                splice(&mut repaired, bytes, &mut copied, index).extend_from_slice(b"\\\\");
                index += 1;
            }
            continue;
        }
        if byte <= 0x1F {
            push_escaped_control(byte, splice(&mut repaired, bytes, &mut copied, index));
        }
        index += 1;
    }
    let Some(mut repaired) = repaired else {
        return Cow::Borrowed(json);
    };
    repaired.extend_from_slice(&bytes[copied..]);
    // Only ASCII bytes were inserted, between whole UTF-8 sequences.
    Cow::Owned(
        String::from_utf8(repaired)
            .unwrap_or_else(|error| String::from_utf8_lossy(error.as_bytes()).into_owned()),
    )
}

/// JS `JSON.parse(text)` (no reviver).
///
/// # Errors
///
/// The `SyntaxError` for malformed JSON.
pub fn json_parse(text: &str) -> Result<JsonValue, JsonSyntaxError> {
    js_json::parse(text)
}

/// `JSON.parse(json)`, retried once on the repaired text when repair changes
/// it, then read in the relaxed dialect of omp's `parseJsonWithRepair`
/// (`packages/utils/src/json-parse.ts:296-302`): single quotes, unquoted
/// keys, comments, Python literals, stray commas, barewords. Truncated input
/// and trailing characters are rejected.
///
/// # Errors
///
/// When the relaxed dialect rejects `json` too: the `SyntaxError` of the
/// original text when repair changes nothing, otherwise the error of the
/// repaired text.
pub fn parse_json_with_repair(json: &str) -> Result<JsonValue, JsonSyntaxError> {
    js_json::parse(json)
        .or_else(|error| match repair_json(json) {
            Cow::Borrowed(_) => Err(error),
            Cow::Owned(repaired) => js_json::parse(&repaired),
        })
        .or_else(|error| relaxed::parse(json).ok_or(error))
}

/// The key of the parse error in the arguments of a call whose final
/// argument JSON does not parse (omp `tool-call-arguments.ts:44-49`).
pub const PARSE_ERROR_KEY: &str = "__parseError";

/// The key of the raw argument text, bounded, next to [`PARSE_ERROR_KEY`].
pub const RAW_JSON_KEY: &str = "__rawJson";

/// The most characters of raw argument text kept next to the parse error
/// (omp `INVALID_ARGUMENTS_RAW_LIMIT`).
pub const INVALID_ARGUMENTS_RAW_LIMIT: usize = 512;

/// The final arguments of a tool call (omp `parseToolCallArguments`,
/// `packages/ai/src/utils/tool-call-arguments.ts:5-13`). Empty text is `{}`
/// (a call of a tool without arguments). Text that
/// [`parse_json_with_repair`] cannot read, or that is not a JSON object,
/// becomes `{ __parseError, __rawJson }`: the error and at most
/// [`INVALID_ARGUMENTS_RAW_LIMIT`] characters of the text. No key of a
/// truncated call is kept, so a half-formed call never runs; the harness
/// shows the model the error and its own text instead. The streaming
/// preview of the same text ([`parse_streaming_json_object`]) auto-closes
/// it; a final parse must not.
#[must_use]
pub fn parse_tool_call_arguments(json: Option<&str>) -> JsonObject {
    let Some(json) = json.filter(|json| !js_trim(json).is_empty()) else {
        return JsonObject::new();
    };
    let error = match parse_json_with_repair(json) {
        Ok(JsonValue::Object(object)) => return object,
        Ok(
            JsonValue::Array(_)
            | JsonValue::String(_)
            | JsonValue::Number(_)
            | JsonValue::Bool(_)
            | JsonValue::Null,
        ) => "Tool call arguments are not a JSON object".to_owned(),
        Err(error) => error.message,
    };
    // Bounded like omp's `boundRawToolArguments`.
    let raw = match json.char_indices().nth(INVALID_ARGUMENTS_RAW_LIMIT) {
        Some((cut, _)) => {
            let (kept, dropped) = json.split_at(cut);
            let dropped = dropped.chars().count();
            format!("{kept}… [truncated {dropped} chars]")
        }
        None => json.to_owned(),
    };
    JsonObject::from_iter([
        (PARSE_ERROR_KEY.to_owned(), JsonValue::String(error)),
        (RAW_JSON_KEY.to_owned(), JsonValue::String(raw)),
    ])
}

/// Whether `JSON.parse` could accept `json` (or its repair, which keeps the
/// first and last non-whitespace bytes of a container or string): an
/// object, array, or string must end with its closing delimiter. Streaming
/// tool arguments almost never do until complete, so the strict parses
/// are skipped for every intermediate delta.
fn may_be_complete(json: &str) -> bool {
    let trimmed = json.trim_matches([' ', '\t', '\n', '\r']).as_bytes();
    match trimmed.first() {
        Some(b'{') => trimmed.last() == Some(&b'}'),
        Some(b'[') => trimmed.last() == Some(&b']'),
        Some(b'"') => trimmed.len() > 1 && trimmed.last() == Some(&b'"'),
        Some(_) | None => true,
    }
}

/// Parse potentially incomplete JSON during streaming. Always returns a
/// value: `{}` for empty input or when nothing can be recovered.
#[must_use]
pub fn parse_streaming_json(partial_json: Option<&str>) -> JsonValue {
    let Some(partial_json) = partial_json.filter(|json| !js_trim(json).is_empty()) else {
        return JsonValue::Object(JsonObject::new());
    };
    if may_be_complete(partial_json) {
        if let Ok(value) = parse_json_with_repair(partial_json) {
            return value;
        }
    }
    let recovered = partial::parse(partial_json).or_else(|error| match repair_json(partial_json) {
        Cow::Borrowed(_) => Err(error),
        Cow::Owned(repaired) => partial::parse(&repaired),
    });
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

    #[test]
    fn repairs_the_relaxed_dialect_after_the_strict_parses() {
        assert_eq!(
            parse_json_with_repair("{'path': 'a.rs', case: True, skip: None,}"),
            Ok(json!({"path": "a.rs", "case": true, "skip": null}))
        );
        assert_eq!(
            parse_json_with_repair(r#"{"a": 1"#),
            Err(JsonSyntaxError {
                message: "Expected ',' or '}' after property value in JSON at position 7 (line 1 column 8)"
                    .to_owned()
            })
        );
    }

    #[test]
    fn final_tool_call_arguments_keep_the_parse_error_and_the_raw_text() {
        let invalid = |error: &str, raw: &str| {
            JsonObject::from_iter([
                (PARSE_ERROR_KEY.to_owned(), json!(error)),
                (RAW_JSON_KEY.to_owned(), json!(raw)),
            ])
        };
        assert_eq!(parse_tool_call_arguments(None), JsonObject::new());
        assert_eq!(parse_tool_call_arguments(Some(" \n")), JsonObject::new());
        assert_eq!(
            parse_tool_call_arguments(Some("{path: 'a.rs'}")),
            JsonObject::from_iter([("path".to_owned(), json!("a.rs"))])
        );
        // The streaming preview auto-closes a truncated call; the final
        // parse keeps none of its keys.
        assert_eq!(
            parse_streaming_json_object(Some(r#"{"path": "a.rs", "text": "x"#)),
            JsonObject::from_iter([
                ("path".to_owned(), json!("a.rs")),
                ("text".to_owned(), json!("x")),
            ])
        );
        assert_eq!(
            parse_tool_call_arguments(Some(r#"{"path": "a.rs", "text": "x"#)),
            invalid(
                "Unterminated string in JSON at position 27 (line 1 column 28)",
                r#"{"path": "a.rs", "text": "x"#
            )
        );
        assert_eq!(
            parse_tool_call_arguments(Some("[1]")),
            invalid("Tool call arguments are not a JSON object", "[1]")
        );
        let long = format!("{{\"text\": \"{}", "é".repeat(600));
        assert_eq!(
            parse_tool_call_arguments(Some(&long)),
            invalid(
                "Unterminated string in JSON at position 610 (line 1 column 611)",
                &format!("{}… [truncated 98 chars]", &long[..long.len() - 196])
            )
        );
    }
}
