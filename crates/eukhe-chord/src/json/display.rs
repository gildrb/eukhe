//! `JSON.stringify` and JS `String(value)` renderings.

use std::fmt::Write as _;

use super::number::write_js_number;
use super::{JsonObject, JsonValue};

/// Append `JSON.stringify(value)`.
pub(crate) fn write_json(out: &mut String, value: &JsonValue) {
    match value {
        JsonValue::Null => out.push_str("null"),
        JsonValue::Bool(true) => out.push_str("true"),
        JsonValue::Bool(false) => out.push_str("false"),
        JsonValue::Number(number) => write_js_number(out, number.get()),
        JsonValue::String(text) => write_json_string(out, text),
        JsonValue::Array(items) => {
            out.push('[');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                write_json(out, item);
            }
            out.push(']');
        }
        JsonValue::Object(object) => write_object(out, object),
    }
}

pub(crate) fn write_object(out: &mut String, object: &JsonObject) {
    out.push('{');
    for (index, (key, value)) in object.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        write_json_string(out, key);
        out.push(':');
        write_json(out, value);
    }
    out.push('}');
}

/// Append a string quoted as `JSON.stringify` quotes it.
pub(crate) fn write_json_string(out: &mut String, text: &str) {
    out.push('"');
    for character in text.chars() {
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            control if u32::from(control) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", u32::from(control));
            }
            other => out.push(other),
        }
    }
    out.push('"');
}

/// JS `String(value)`: arrays join their elements with `,` (null as empty),
/// objects are `[object Object]`.
pub(crate) fn js_string(value: &JsonValue) -> String {
    let mut out = String::new();
    write_js_string(&mut out, value, /*top_level*/ true);
    out
}

fn write_js_string(out: &mut String, value: &JsonValue, top_level: bool) {
    match value {
        JsonValue::Null if top_level => out.push_str("null"),
        JsonValue::Null => {}
        JsonValue::Bool(flag) => out.push_str(if *flag { "true" } else { "false" }),
        JsonValue::Number(number) => write_js_number(out, number.get()),
        JsonValue::String(text) => out.push_str(text),
        JsonValue::Array(items) => {
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                write_js_string(out, item, /*top_level*/ false);
            }
        }
        JsonValue::Object(_) => out.push_str("[object Object]"),
    }
}
