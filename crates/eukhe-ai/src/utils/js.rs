//! JavaScript built-in semantics the TS utilities rely on: `String.prototype.trim`,
//! UTF-16 `length`, `Number.prototype.toString`, `String(value)`, JS object
//! key enumeration order, and `JSON.stringify`.

use eukhe_types::pi_ai::{JsonObject, JsonValue};

/// Whether `c` is removed by JS `String.prototype.trim` (`WhiteSpace` and
/// `LineTerminator` code points). Differs from [`char::is_whitespace`]: JS trims
/// U+FEFF and keeps U+0085.
#[must_use]
pub(crate) const fn is_js_whitespace(c: char) -> bool {
    matches!(
        c,
        '\t' | '\n' | '\u{000B}' | '\u{000C}' | '\r' | ' ' | '\u{00A0}' | '\u{1680}' | '\u{2000}'
            ..='\u{200A}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202F}'
                | '\u{205F}'
                | '\u{3000}'
                | '\u{FEFF}'
    )
}

/// JS `string.trim()`.
#[must_use]
pub(crate) fn js_trim(text: &str) -> &str {
    text.trim_matches(is_js_whitespace)
}

/// JS `string.length`: UTF-16 code units.
#[must_use]
pub(crate) fn utf16_len(text: &str) -> usize {
    text.chars().map(char::len_utf16).sum()
}

/// The longest prefix of `text` with at most `max_units` UTF-16 code units
/// that does not split a character (JS `text.slice(0, max_units)` without a
/// dangling surrogate).
#[must_use]
pub(crate) fn utf16_prefix(text: &str, max_units: usize) -> &str {
    let mut units = 0;
    for (index, c) in text.char_indices() {
        units += c.len_utf16();
        if units > max_units {
            return &text[..index];
        }
    }
    text
}

/// JS `Number.parseFloat(text)`: the longest decimal-literal prefix after
/// leading whitespace (`"1000ms"` → 1000, `"Infinity"` → ∞), `NaN` when none.
#[must_use]
pub(crate) fn js_parse_float(text: &str) -> f64 {
    let text = text.trim_start_matches(is_js_whitespace);
    let bytes = text.as_bytes();
    let mut end = 0;
    if let Some(b'+' | b'-') = bytes.first() {
        end = 1;
    }
    if text[end..].starts_with("Infinity") {
        return if bytes.first() == Some(&b'-') {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        };
    }
    let digits_start = end;
    while bytes.get(end).is_some_and(u8::is_ascii_digit) {
        end += 1;
    }
    let mut has_digits = end > digits_start;
    if bytes.get(end) == Some(&b'.') {
        let fraction_start = end + 1;
        let mut fraction_end = fraction_start;
        while bytes.get(fraction_end).is_some_and(u8::is_ascii_digit) {
            fraction_end += 1;
        }
        if has_digits || fraction_end > fraction_start {
            has_digits = true;
            end = fraction_end;
        }
    }
    if !has_digits {
        return f64::NAN;
    }
    if let Some(b'e' | b'E') = bytes.get(end) {
        let mut exponent_end = end + 1;
        if let Some(b'+' | b'-') = bytes.get(exponent_end) {
            exponent_end += 1;
        }
        let exponent_digits = exponent_end;
        while bytes.get(exponent_end).is_some_and(u8::is_ascii_digit) {
            exponent_end += 1;
        }
        if exponent_end > exponent_digits {
            end = exponent_end;
        }
    }
    text[..end].parse().unwrap_or(f64::NAN)
}

/// Largest magnitude below which an integral double is printed as an integer.
const MAX_EXACT_INTEGER: f64 = 9_007_199_254_740_992.0;

/// A JS number as JSON: integral values below 2^53 become integers (JS prints
/// `1`, not `1.0`); non-finite values become `null`, as `JSON.stringify` writes them.
#[must_use]
pub(crate) fn js_number_value(number: f64) -> JsonValue {
    if !number.is_finite() {
        return JsonValue::Null;
    }
    if number.fract() == 0.0 && number.abs() < MAX_EXACT_INTEGER {
        // The guard proves the conversion exact: whole value, |v| < 2^53.
        #[allow(clippy::cast_possible_truncation)]
        return JsonValue::from(number as i64);
    }
    serde_json::Number::from_f64(number).map_or(JsonValue::Null, JsonValue::Number)
}

/// ECMAScript `Number::toString(x)` (radix 10): the shortest round-trip
/// digits, in fixed notation for 1e-7 ≤ |x| < 1e21 and exponent notation
/// (`1e+21`, `1.5e-7`) otherwise.
#[must_use]
pub(crate) fn number_to_js_string(number: f64) -> String {
    if number.is_nan() {
        return "NaN".to_owned();
    }
    if number == 0.0 {
        return "0".to_owned();
    }
    if number.is_infinite() {
        return if number > 0.0 {
            "Infinity"
        } else {
            "-Infinity"
        }
        .to_owned();
    }
    if number < 0.0 {
        return format!("-{}", number_to_js_string(-number));
    }
    // `{:e}` prints the shortest round-trip digits: `d[.ddd]e<exp>`.
    let scientific = format!("{number:e}");
    let (mantissa, exponent) = scientific
        .split_once('e')
        .unwrap_or((scientific.as_str(), "0"));
    let digits: String = mantissa.chars().filter(char::is_ascii_digit).collect();
    let exponent: i32 = exponent.parse().unwrap_or(0);
    let k = i32::try_from(digits.len()).unwrap_or(i32::MAX);
    let n = exponent + 1;
    if k <= n && n <= 21 {
        let zeros = usize::try_from(n - k).unwrap_or(0);
        return format!("{digits}{}", "0".repeat(zeros));
    }
    if 0 < n && n <= 21 {
        let split = usize::try_from(n).unwrap_or(0);
        return format!("{}.{}", &digits[..split], &digits[split..]);
    }
    if -6 < n && n <= 0 {
        let zeros = usize::try_from(-n).unwrap_or(0);
        return format!("0.{}{digits}", "0".repeat(zeros));
    }
    let sign = if n - 1 < 0 { '-' } else { '+' };
    let magnitude = (n - 1).abs();
    if digits.len() == 1 {
        format!("{digits}e{sign}{magnitude}")
    } else {
        format!("{}.{}e{sign}{magnitude}", &digits[..1], &digits[1..])
    }
}

/// JS `String(value)` for a JSON value.
#[must_use]
pub(crate) fn js_to_string(value: &JsonValue) -> String {
    match value {
        JsonValue::Null => "null".to_owned(),
        JsonValue::Bool(flag) => flag.to_string(),
        JsonValue::Number(number) => number
            .as_i64()
            .map(|integer| integer.to_string())
            .or_else(|| number.as_u64().map(|integer| integer.to_string()))
            .unwrap_or_else(|| number_to_js_string(number.as_f64().unwrap_or(f64::NAN))),
        JsonValue::String(text) => text.clone(),
        JsonValue::Array(items) => items
            .iter()
            .map(|item| match item {
                JsonValue::Null => String::new(),
                other => js_to_string(other),
            })
            .collect::<Vec<_>>()
            .join(","),
        JsonValue::Object(_) => "[object Object]".to_owned(),
    }
}

/// The array index a JS property key denotes: a canonical decimal below
/// 2^32 - 1. JS objects enumerate such keys first, in ascending order.
#[must_use]
pub(crate) fn array_index_key(key: &str) -> Option<u32> {
    if key.is_empty()
        || (key.len() > 1 && key.starts_with('0'))
        || !key.bytes().all(|byte| byte.is_ascii_digit())
    {
        return None;
    }
    key.parse::<u32>().ok().filter(|index| *index != u32::MAX)
}

/// An object's entries in JS enumeration order: array-index keys first
/// (ascending), then the rest in insertion order.
#[must_use]
pub(crate) fn js_object_entries(map: &JsonObject) -> Vec<(&String, &JsonValue)> {
    let mut indexed: Vec<(u32, &String, &JsonValue)> = Vec::new();
    let mut named: Vec<(&String, &JsonValue)> = Vec::new();
    for (key, value) in map {
        match array_index_key(key) {
            Some(index) => indexed.push((index, key, value)),
            None => named.push((key, value)),
        }
    }
    indexed.sort_by_key(|(index, _, _)| *index);
    indexed
        .into_iter()
        .map(|(_, key, value)| (key, value))
        .chain(named)
        .collect()
}

/// JS `JSON.stringify(value)`.
#[must_use]
pub(crate) fn json_stringify(value: &JsonValue) -> String {
    let mut out = String::new();
    write_json(value, None, 0, &mut out);
    out
}

/// JS `JSON.stringify(value, null, 2)`.
#[must_use]
pub(crate) fn json_stringify_pretty(value: &JsonValue) -> String {
    let mut out = String::new();
    write_json(value, Some("  "), 0, &mut out);
    out
}

/// JS `JSON.stringify(value, null, indent)` with a string indent.
#[must_use]
pub(crate) fn json_stringify_indent(value: &JsonValue, indent: &str) -> String {
    let mut out = String::new();
    write_json(value, Some(indent), 0, &mut out);
    out
}

fn write_json(value: &JsonValue, indent: Option<&str>, depth: usize, out: &mut String) {
    match value {
        JsonValue::Null => out.push_str("null"),
        JsonValue::Bool(flag) => out.push_str(if *flag { "true" } else { "false" }),
        JsonValue::Number(number) => {
            if let Some(integer) = number.as_i64() {
                out.push_str(&integer.to_string());
            } else if let Some(integer) = number.as_u64() {
                out.push_str(&integer.to_string());
            } else {
                let float = number.as_f64().unwrap_or(f64::NAN);
                if float.is_finite() {
                    out.push_str(&number_to_js_string(float));
                } else {
                    out.push_str("null");
                }
            }
        }
        JsonValue::String(text) => out.push_str(&JsonValue::String(text.clone()).to_string()),
        JsonValue::Array(items) => {
            if items.is_empty() {
                out.push_str("[]");
                return;
            }
            out.push('[');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                newline_indent(indent, depth + 1, out);
                write_json(item, indent, depth + 1, out);
            }
            newline_indent(indent, depth, out);
            out.push(']');
        }
        JsonValue::Object(map) => {
            if map.is_empty() {
                out.push_str("{}");
                return;
            }
            out.push('{');
            for (index, (key, item)) in js_object_entries(map).into_iter().enumerate() {
                if index > 0 {
                    out.push(',');
                }
                newline_indent(indent, depth + 1, out);
                out.push_str(&JsonValue::String(key.clone()).to_string());
                out.push(':');
                if indent.is_some() {
                    out.push(' ');
                }
                write_json(item, indent, depth + 1, out);
            }
            newline_indent(indent, depth, out);
            out.push('}');
        }
    }
}

fn newline_indent(indent: Option<&str>, depth: usize, out: &mut String) {
    if let Some(indent) = indent {
        out.push('\n');
        for _ in 0..depth {
            out.push_str(indent);
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn prints_numbers_like_ecmascript() {
        // Expected strings computed with node.
        let cases = [
            (0.000_003, "0.000003"),
            (1e21, "1e+21"),
            (1.5e-7, "1.5e-7"),
            (123_456_789_012_345_680_000.0, "123456789012345680000"),
            (1e-7, "1e-7"),
            (0.1 + 0.2, "0.30000000000000004"),
            (-2.5e-10, "-2.5e-10"),
            (255.0, "255"),
            (1e300, "1e+300"),
        ];
        for (number, expected) in cases {
            assert_eq!(number_to_js_string(number), expected);
        }
    }

    #[test]
    fn parses_floats_like_number_parse_float() {
        let cases = [
            (" 12px", 12.0),
            ("1e3x", 1000.0),
            (".5", 0.5),
            ("-.5e-1", -0.05),
            ("Infinityx", f64::INFINITY),
            ("1e", 1.0),
            ("5.", 5.0),
        ];
        for (text, expected) in cases {
            assert!(
                (js_parse_float(text) - expected).abs() < 1e-12
                    || js_parse_float(text).is_infinite(),
                "{text}"
            );
        }
        assert!(js_parse_float("+-1").is_nan());
        assert!(js_parse_float("abc").is_nan());
    }

    #[test]
    fn stringifies_like_json_stringify() {
        let value = json!({ "b": 1, "2": 2, "10": 3, "01": 4, "a": [1.5, 1e21, null] });
        assert_eq!(
            json_stringify_pretty(&value),
            "{\n  \"2\": 2,\n  \"10\": 3,\n  \"b\": 1,\n  \"01\": 4,\n  \"a\": [\n    1.5,\n    1e+21,\n    null\n  ]\n}"
        );
        assert_eq!(
            json_stringify(&json!({ "x": [], "y": {} })),
            r#"{"x":[],"y":{}}"#
        );
        assert_eq!(js_trim("\u{FEFF} a \u{2028}"), "a");
        assert_eq!(utf16_len("a🙈"), 3);
        assert_eq!(utf16_prefix("a🙈b", 2), "a");
    }
}
