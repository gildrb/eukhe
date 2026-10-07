//! A port of JavaScript `JSON.parse` (without a reviver) producing
//! `serde_json` values with JS object semantics:
//!
//! - numbers are doubles: integral values below 2^53 become integers,
//!   out-of-range values (`1e400`) become `null` (JS `Infinity`, which
//!   `JSON.stringify` writes as `null`);
//! - duplicate keys keep the first position and the last value;
//! - array-index keys (`"0"`, `"1"`, ...) enumerate first in ascending order,
//!   like every JS object;
//! - lone surrogate escapes (`"\ud800"`), unrepresentable in a Rust string,
//!   become U+FFFD.
//!
//! Error messages are V8's (node v26) verbatim; positions and columns count
//! UTF-16 code units. Where V8 would put a lone surrogate into the message (an
//! unexpected astral character, or a context snippet cut inside a surrogate
//! pair), the message holds U+FFFD instead.

use eukhe_types::pi_ai::{JsonObject, JsonValue};

use crate::utils::js::{array_index_key, js_number_value, utf16_len};

/// A `SyntaxError` from `JSON.parse`.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{message}")]
pub struct JsonSyntaxError {
    pub message: String,
}

/// JS `JSON.parse(text)`.
pub(crate) fn parse(text: &str) -> Result<JsonValue, JsonSyntaxError> {
    let mut parser = Parser {
        text,
        bytes: text.as_bytes(),
        pos: 0,
    };
    parser.skip_whitespace();
    let value = parser.parse_value()?;
    parser.skip_whitespace();
    if parser.pos < parser.bytes.len() {
        return Err(parser.located("Unexpected non-whitespace character after JSON"));
    }
    Ok(value)
}

/// Reorder an object's keys like a JS object: array-index keys first, ascending.
pub(crate) fn js_object_order(map: JsonObject) -> JsonObject {
    if !map.keys().any(|key| array_index_key(key).is_some()) {
        return map;
    }
    let mut indexed: Vec<(u32, String, JsonValue)> = Vec::new();
    let mut named: Vec<(String, JsonValue)> = Vec::new();
    for (key, value) in map {
        match array_index_key(&key) {
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

/// Context characters V8 shows on each side of an unexpected token.
const MAX_CONTEXT_CHARACTERS: usize = 10;

/// Source length (UTF-16) from which V8 shows a context window instead of the
/// whole source.
const MIN_ORIGINAL_SOURCE_LENGTH_FOR_CONTEXT: usize = 21;

/// Sources V8 reports as a whole (`"undefined" is not valid JSON`): what
/// `JSON.parse` receives for common non-string arguments.
const SPECIAL_SOURCES: [&str; 4] = ["undefined", "NaN", "Infinity", "[object Object]"];

struct Parser<'a> {
    text: &'a str,
    bytes: &'a [u8],
    pos: usize,
}

impl Parser<'_> {
    fn position(&self) -> usize {
        utf16_len(&self.text[..self.pos.min(self.text.len())])
    }

    /// V8's `(line L column C)`: `\n`, `\r`, and `\r\n` each end a line; the
    /// column counts UTF-16 code units from the line start, 1-based.
    fn line_column(&self) -> (usize, usize) {
        let end = self.pos.min(self.bytes.len());
        let mut line = 1;
        let mut line_start = 0;
        let mut index = 0;
        while index < end {
            if self.bytes[index] == b'\r' && index + 1 < end && self.bytes[index + 1] == b'\n' {
                index += 1;
            }
            if let b'\r' | b'\n' = self.bytes[index] {
                line += 1;
                line_start = index + 1;
            }
            index += 1;
        }
        (line, 1 + utf16_len(&self.text[line_start..end]))
    }

    /// A V8 `<message> in JSON at position ...` error.
    fn error_at(&self, message: &str) -> JsonSyntaxError {
        self.located(&format!("{message} in JSON"))
    }

    /// `<lead> at position P (line L column C)`.
    fn located(&self, lead: &str) -> JsonSyntaxError {
        let (line, column) = self.line_column();
        JsonSyntaxError {
            message: format!(
                "{lead} at position {} (line {line} column {column})",
                self.position()
            ),
        }
    }

    /// V8's unexpected-token message for the character at the cursor, or the
    /// end-of-input message at the end of the source.
    fn unexpected(&self) -> JsonSyntaxError {
        if self.pos >= self.bytes.len() {
            return JsonSyntaxError {
                message: "Unexpected end of JSON input".to_owned(),
            };
        }
        if SPECIAL_SOURCES.contains(&self.text) {
            return JsonSyntaxError {
                message: format!("\"{}\" is not valid JSON", self.text),
            };
        }
        let units: Vec<u16> = self.text.encode_utf16().collect();
        let pos = self.position();
        let token = String::from_utf16_lossy(&units[pos..=pos]);
        let len = units.len();
        let message = if len < MIN_ORIGINAL_SOURCE_LENGTH_FOR_CONTEXT {
            format!(
                "Unexpected token '{token}', \"{}\" is not valid JSON",
                self.text
            )
        } else if pos < MAX_CONTEXT_CHARACTERS {
            let snippet = String::from_utf16_lossy(&units[..pos + MAX_CONTEXT_CHARACTERS]);
            format!("Unexpected token '{token}', \"{snippet}\"... is not valid JSON")
        } else if pos < len - MAX_CONTEXT_CHARACTERS {
            let snippet = String::from_utf16_lossy(
                &units[pos - MAX_CONTEXT_CHARACTERS..pos + MAX_CONTEXT_CHARACTERS],
            );
            format!("Unexpected token '{token}', ...\"{snippet}\"... is not valid JSON")
        } else {
            let snippet = String::from_utf16_lossy(&units[pos - MAX_CONTEXT_CHARACTERS..]);
            format!("Unexpected token '{token}', ...\"{snippet}\" is not valid JSON")
        };
        JsonSyntaxError { message }
    }

    fn skip_whitespace(&mut self) {
        while let Some(b' ' | b'\t' | b'\n' | b'\r') = self.bytes.get(self.pos) {
            self.pos += 1;
        }
    }

    fn parse_value(&mut self) -> Result<JsonValue, JsonSyntaxError> {
        match self.bytes.get(self.pos) {
            Some(b'{') => self.parse_object(),
            Some(b'[') => self.parse_array(),
            Some(b'"') => self.parse_string().map(JsonValue::String),
            Some(b't') => self.parse_literal("true", JsonValue::Bool(true)),
            Some(b'f') => self.parse_literal("false", JsonValue::Bool(false)),
            Some(b'n') => self.parse_literal("null", JsonValue::Null),
            Some(b'-' | b'0'..=b'9') => self.parse_number(),
            _ => Err(self.unexpected()),
        }
    }

    fn parse_literal(
        &mut self,
        literal: &str,
        value: JsonValue,
    ) -> Result<JsonValue, JsonSyntaxError> {
        for expected in literal.bytes() {
            if self.bytes.get(self.pos) != Some(&expected) {
                return Err(self.unexpected());
            }
            self.pos += 1;
        }
        Ok(value)
    }

    fn parse_number(&mut self) -> Result<JsonValue, JsonSyntaxError> {
        let start = self.pos;
        if self.bytes.get(self.pos) == Some(&b'-') {
            self.pos += 1;
        }
        match self.bytes.get(self.pos) {
            Some(b'0') => {
                self.pos += 1;
                if self.bytes.get(self.pos).is_some_and(u8::is_ascii_digit) {
                    return Err(self.error_at("Unexpected number"));
                }
            }
            Some(b'1'..=b'9') => self.skip_digits(),
            _ => return Err(self.error_at("No number after minus sign")),
        }
        if self.bytes.get(self.pos) == Some(&b'.') {
            self.pos += 1;
            if !self.bytes.get(self.pos).is_some_and(u8::is_ascii_digit) {
                return Err(self.error_at("Unterminated fractional number"));
            }
            self.skip_digits();
        }
        if let Some(b'e' | b'E') = self.bytes.get(self.pos) {
            self.pos += 1;
            if let Some(b'+' | b'-') = self.bytes.get(self.pos) {
                self.pos += 1;
            }
            if !self.bytes.get(self.pos).is_some_and(u8::is_ascii_digit) {
                return Err(self.error_at("Exponent part is missing a number"));
            }
            self.skip_digits();
        }
        let literal = &self.text[start..self.pos];
        let number: f64 = literal
            .parse()
            .map_err(|_| self.error_at(&format!("Unexpected number '{literal}'")))?;
        Ok(js_number_value(number))
    }

    fn skip_digits(&mut self) {
        while self.bytes.get(self.pos).is_some_and(u8::is_ascii_digit) {
            self.pos += 1;
        }
    }

    fn parse_string(&mut self) -> Result<String, JsonSyntaxError> {
        self.pos += 1;
        let mut out = String::new();
        let mut run_start = self.pos;
        loop {
            let Some(&byte) = self.bytes.get(self.pos) else {
                return Err(self.error_at("Unterminated string"));
            };
            match byte {
                b'"' => {
                    out.push_str(&self.text[run_start..self.pos]);
                    self.pos += 1;
                    return Ok(out);
                }
                b'\\' => {
                    out.push_str(&self.text[run_start..self.pos]);
                    self.parse_escape(&mut out)?;
                    run_start = self.pos;
                }
                0x00..=0x1F => return Err(self.error_at("Bad control character in string literal")),
                _ => self.pos += 1,
            }
        }
    }

    fn parse_escape(&mut self, out: &mut String) -> Result<(), JsonSyntaxError> {
        self.pos += 1;
        let Some(&escape) = self.bytes.get(self.pos) else {
            return Err(self.unexpected());
        };
        let simple = match escape {
            b'"' => Some('"'),
            b'\\' => Some('\\'),
            b'/' => Some('/'),
            b'b' => Some('\u{0008}'),
            b'f' => Some('\u{000C}'),
            b'n' => Some('\n'),
            b'r' => Some('\r'),
            b't' => Some('\t'),
            _ => None,
        };
        if let Some(c) = simple {
            out.push(c);
            self.pos += 1;
            return Ok(());
        }
        if escape != b'u' {
            return Err(self.error_at("Bad escaped character"));
        }
        self.pos += 1;
        let unit = self.hex4()?;
        if (0xD800..0xDC00).contains(&unit) && self.text[self.pos..].starts_with("\\u") {
            let saved = self.pos;
            self.pos += 2;
            match self.hex4() {
                Ok(low) if (0xDC00..0xE000).contains(&low) => {
                    let code =
                        0x10000 + ((u32::from(unit) - 0xD800) << 10) + (u32::from(low) - 0xDC00);
                    out.push(char::from_u32(code).unwrap_or('\u{FFFD}'));
                    return Ok(());
                }
                Ok(_) => self.pos = saved,
                Err(error) => return Err(error),
            }
        }
        out.push(char::from_u32(u32::from(unit)).unwrap_or('\u{FFFD}'));
        Ok(())
    }

    /// Four hex digits; a missing or non-hex digit is reported at its position.
    fn hex4(&mut self) -> Result<u16, JsonSyntaxError> {
        let mut unit = 0u16;
        for _ in 0..4 {
            let digit = match self.bytes.get(self.pos) {
                Some(&byte @ b'0'..=b'9') => byte - b'0',
                Some(&byte @ b'a'..=b'f') => byte - b'a' + 10,
                Some(&byte @ b'A'..=b'F') => byte - b'A' + 10,
                _ => return Err(self.error_at("Bad Unicode escape")),
            };
            unit = (unit << 4) | u16::from(digit);
            self.pos += 1;
        }
        Ok(unit)
    }

    fn parse_array(&mut self) -> Result<JsonValue, JsonSyntaxError> {
        self.pos += 1;
        let mut items = Vec::new();
        self.skip_whitespace();
        if self.bytes.get(self.pos) == Some(&b']') {
            self.pos += 1;
            return Ok(JsonValue::Array(items));
        }
        loop {
            self.skip_whitespace();
            items.push(self.parse_value()?);
            self.skip_whitespace();
            match self.bytes.get(self.pos) {
                Some(b',') => self.pos += 1,
                Some(b']') => {
                    self.pos += 1;
                    return Ok(JsonValue::Array(items));
                }
                _ => return Err(self.error_at("Expected ',' or ']' after array element")),
            }
        }
    }

    fn parse_object(&mut self) -> Result<JsonValue, JsonSyntaxError> {
        self.pos += 1;
        let mut map = JsonObject::new();
        self.skip_whitespace();
        if self.bytes.get(self.pos) == Some(&b'}') {
            self.pos += 1;
            return Ok(JsonValue::Object(map));
        }
        let mut first = true;
        loop {
            self.skip_whitespace();
            if self.bytes.get(self.pos) != Some(&b'"') {
                return Err(self.error_at(if first {
                    "Expected property name or '}'"
                } else {
                    "Expected double-quoted property name"
                }));
            }
            first = false;
            let key = self.parse_string()?;
            self.skip_whitespace();
            if self.bytes.get(self.pos) != Some(&b':') {
                return Err(self.error_at("Expected ':' after property name"));
            }
            self.pos += 1;
            self.skip_whitespace();
            let value = self.parse_value()?;
            map.insert(key, value);
            self.skip_whitespace();
            match self.bytes.get(self.pos) {
                Some(b',') => self.pos += 1,
                Some(b'}') => {
                    self.pos += 1;
                    return Ok(JsonValue::Object(js_object_order(map)));
                }
                _ => return Err(self.error_at("Expected ',' or '}' after property value")),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn parses_like_json_parse() {
        assert_eq!(
            parse(" {\"b\":1,\"1\":2.0,\"a\":[true,null,-0]} ").unwrap(),
            json!({"1": 2, "b": 1, "a": [true, null, 0]})
        );
        assert_eq!(parse("\"\\ud83d\\ude48\"").unwrap(), json!("🙈"));
        assert_eq!(parse("\"\\ud800x\"").unwrap(), json!("\u{FFFD}x"));
        assert_eq!(parse("1e400").unwrap(), JsonValue::Null);
        assert_eq!(parse("{\"a\":1,\"a\":2}").unwrap(), json!({"a": 2}));
    }

    /// `(input, message)`: messages captured from node v26 `JSON.parse(input)`.
    const NODE_V26_ERRORS: &[(&str, &str)] = &[
        ("", "Unexpected end of JSON input"),
        (" ", "Unexpected end of JSON input"),
        ("\n\r\t ", "Unexpected end of JSON input"),
        ("x", "Unexpected token 'x', \"x\" is not valid JSON"),
        (
            "<html>Forbidden",
            "Unexpected token '<', \"<html>Forbidden\" is not valid JSON",
        ),
        (
            "{\"a\":1",
            "Expected ',' or '}' after property value in JSON at position 6 (line 1 column 7)",
        ),
        ("undefined", "\"undefined\" is not valid JSON"),
        ("NaN", "\"NaN\" is not valid JSON"),
        ("Infinity", "\"Infinity\" is not valid JSON"),
        ("[object Object]", "\"[object Object]\" is not valid JSON"),
        ("nul", "Unexpected end of JSON input"),
        ("tru", "Unexpected end of JSON input"),
        ("nulL", "Unexpected token 'L', \"nulL\" is not valid JSON"),
        ("tx", "Unexpected token 'x', \"tx\" is not valid JSON"),
        ("[nul]", "Unexpected token ']', \"[nul]\" is not valid JSON"),
        (
            "{\"a\":t}",
            "Unexpected token '}', \"{\"a\":t}\" is not valid JSON",
        ),
        ("+1", "Unexpected token '+', \"+1\" is not valid JSON"),
        (".5", "Unexpected token '.', \".5\" is not valid JSON"),
        (",", "Unexpected token ',', \",\" is not valid JSON"),
        ("[1,]", "Unexpected token ']', \"[1,]\" is not valid JSON"),
        (
            "[1,,2]",
            "Unexpected token ',', \"[1,,2]\" is not valid JSON",
        ),
        (
            "{\"a\":{\"b\":}}",
            "Unexpected token '}', \"{\"a\":{\"b\":}}\" is not valid JSON",
        ),
        (
            "-",
            "No number after minus sign in JSON at position 1 (line 1 column 2)",
        ),
        (
            "-a",
            "No number after minus sign in JSON at position 1 (line 1 column 2)",
        ),
        (
            "[-]",
            "No number after minus sign in JSON at position 2 (line 1 column 3)",
        ),
        (
            "-Infinity",
            "No number after minus sign in JSON at position 1 (line 1 column 2)",
        ),
        (
            "01",
            "Unexpected number in JSON at position 1 (line 1 column 2)",
        ),
        (
            "-01",
            "Unexpected number in JSON at position 2 (line 1 column 3)",
        ),
        (
            "[00]",
            "Unexpected number in JSON at position 2 (line 1 column 3)",
        ),
        (
            "1.",
            "Unterminated fractional number in JSON at position 2 (line 1 column 3)",
        ),
        (
            "[1.a]",
            "Unterminated fractional number in JSON at position 3 (line 1 column 4)",
        ),
        (
            "1e",
            "Exponent part is missing a number in JSON at position 2 (line 1 column 3)",
        ),
        (
            "1e+",
            "Exponent part is missing a number in JSON at position 3 (line 1 column 4)",
        ),
        (
            "[1E-x]",
            "Exponent part is missing a number in JSON at position 4 (line 1 column 5)",
        ),
        (
            "{",
            "Expected property name or '}' in JSON at position 1 (line 1 column 2)",
        ),
        (
            "{,}",
            "Expected property name or '}' in JSON at position 1 (line 1 column 2)",
        ),
        (
            "{1:2}",
            "Expected property name or '}' in JSON at position 1 (line 1 column 2)",
        ),
        (
            "{\"a\":1,}",
            "Expected double-quoted property name in JSON at position 7 (line 1 column 8)",
        ),
        (
            "{\"a\":1,",
            "Expected double-quoted property name in JSON at position 7 (line 1 column 8)",
        ),
        (
            "{\"a\"",
            "Expected ':' after property name in JSON at position 4 (line 1 column 5)",
        ),
        (
            "{\"a\" 1}",
            "Expected ':' after property name in JSON at position 5 (line 1 column 6)",
        ),
        (
            "{\"a\" \"b\"}",
            "Expected ':' after property name in JSON at position 5 (line 1 column 6)",
        ),
        (
            "{\"a\":1 \"b\"}",
            "Expected ',' or '}' after property value in JSON at position 7 (line 1 column 8)",
        ),
        (
            "[1 2]",
            "Expected ',' or ']' after array element in JSON at position 3 (line 1 column 4)",
        ),
        (
            "[1,2",
            "Expected ',' or ']' after array element in JSON at position 4 (line 1 column 5)",
        ),
        ("[", "Unexpected end of JSON input"),
        ("{\"a\":", "Unexpected end of JSON input"),
        ("[\"a\",", "Unexpected end of JSON input"),
        (
            "\"a\nb\"",
            "Bad control character in string literal in JSON at position 2 (line 1 column 3)",
        ),
        (
            "\"\u{0}\"",
            "Bad control character in string literal in JSON at position 1 (line 1 column 2)",
        ),
        (
            "\"\\x\"",
            "Bad escaped character in JSON at position 2 (line 1 column 3)",
        ),
        ("\"\\", "Unexpected end of JSON input"),
        ("\"abc\\", "Unexpected end of JSON input"),
        (
            "\"\\\"",
            "Unterminated string in JSON at position 3 (line 1 column 4)",
        ),
        (
            "\"abc",
            "Unterminated string in JSON at position 4 (line 1 column 5)",
        ),
        (
            "{\"a",
            "Unterminated string in JSON at position 3 (line 1 column 4)",
        ),
        (
            "\"\\u",
            "Bad Unicode escape in JSON at position 3 (line 1 column 4)",
        ),
        (
            "\"\\u12",
            "Bad Unicode escape in JSON at position 5 (line 1 column 6)",
        ),
        (
            "\"\\u12\"",
            "Bad Unicode escape in JSON at position 5 (line 1 column 6)",
        ),
        (
            "\"\\u12G4\"",
            "Bad Unicode escape in JSON at position 5 (line 1 column 6)",
        ),
        (
            "\"\\ud800\\u12\"",
            "Bad Unicode escape in JSON at position 11 (line 1 column 12)",
        ),
        (
            "1 2",
            "Unexpected non-whitespace character after JSON at position 2 (line 1 column 3)",
        ),
        (
            "{\"a\":1}x",
            "Unexpected non-whitespace character after JSON at position 7 (line 1 column 8)",
        ),
        (
            "\"a\" \"b\"",
            "Unexpected non-whitespace character after JSON at position 4 (line 1 column 5)",
        ),
        (
            "[1]]",
            "Unexpected non-whitespace character after JSON at position 3 (line 1 column 4)",
        ),
        (
            "0x10",
            "Unexpected non-whitespace character after JSON at position 1 (line 1 column 2)",
        ),
        (
            "truex",
            "Unexpected non-whitespace character after JSON at position 4 (line 1 column 5)",
        ),
        (
            "[1,\n\n2 3]",
            "Expected ',' or ']' after array element in JSON at position 7 (line 3 column 3)",
        ),
        (
            "[1,\r\n2 3]",
            "Expected ',' or ']' after array element in JSON at position 7 (line 2 column 3)",
        ),
        (
            "[1,\r\r2 3]",
            "Expected ',' or ']' after array element in JSON at position 7 (line 3 column 3)",
        ),
        (
            "[1,\n\r2 3]",
            "Expected ',' or ']' after array element in JSON at position 7 (line 3 column 3)",
        ),
        (
            "\n\n  \r\n [1 2]",
            "Expected ',' or ']' after array element in JSON at position 10 (line 4 column 5)",
        ),
        (
            "[\n1\n,\r\n\"é😀\u{1}\"]",
            "Bad control character in string literal in JSON at position 11 (line 4 column 5)",
        ),
        (
            "{\"é\":1 2}",
            "Expected ',' or '}' after property value in JSON at position 7 (line 1 column 8)",
        ),
        (
            "\"😀\" x",
            "Unexpected non-whitespace character after JSON at position 5 (line 1 column 6)",
        ),
        ("é", "Unexpected token 'é', \"é\" is not valid JSON"),
        // V8 prints the lone high surrogate '\u{d83d}' where this has U+FFFD.
        (
            "😀",
            "Unexpected token '\u{fffd}', \"😀\" is not valid JSON",
        ),
        (
            "\u{feff}1",
            "Unexpected token '\u{feff}', \"\u{feff}1\" is not valid JSON",
        ),
        (
            "\u{a0}1",
            "Unexpected token '\u{a0}', \"\u{a0}1\" is not valid JSON",
        ),
        (
            "xaaaaaaaaaaaaaaaaaaa",
            "Unexpected token 'x', \"xaaaaaaaaaaaaaaaaaaa\" is not valid JSON",
        ),
        (
            "xaaaaaaaaaaaaaaaaaaaa",
            "Unexpected token 'x', \"xaaaaaaaaa\"... is not valid JSON",
        ),
        (
            "[}1111111111111111111",
            "Unexpected token '}', \"[}111111111\"... is not valid JSON",
        ),
        (
            "[1,1,1,1,},1,1,1,1,1,1,1,1,1,1",
            "Unexpected token '}', \"[1,1,1,1,},1,1,1,1,\"... is not valid JSON",
        ),
        (
            "[1,1,1,1,1,},1,1,1,1,1,1,1,1,1",
            "Unexpected token '}', ...\"1,1,1,1,1,},1,1,1,1,\"... is not valid JSON",
        ),
        (
            "[1,1,1,1,1,1,1,1,1,},1,1,1,1,1",
            "Unexpected token '}', ...\"1,1,1,1,1,},1,1,1,1,\"... is not valid JSON",
        ),
        (
            "[1,1,1,1,1,1,1,1,1,1,},1,1,1,1",
            "Unexpected token '}', ...\"1,1,1,1,1,},1,1,1,1\" is not valid JSON",
        ),
        (
            "[1,1,1,1,1,1,1,1,1,1,1,1,1,1,}",
            "Unexpected token '}', ...\"1,1,1,1,1,}\" is not valid JSON",
        ),
        (
            "[1,1,1,1,\"😀😀😀😀😀\",x]",
            "Unexpected token 'x', ...\"😀😀😀😀\",x]\" is not valid JSON",
        ),
        (
            "[1,1,1,1,1,1,\"éééééééé\",x,1,1,1,1,1,1,1,1,1,1,1]",
            "Unexpected token 'x', ...\"éééééééé\",x,1,1,1,1,\"... is not valid JSON",
        ),
        // V8 ends the snippet with the lone high surrogate '\u{d83d}' where this has U+FFFD.
        (
            "a😀😀😀😀😀😀😀😀😀😀😀",
            "Unexpected token 'a', \"a😀😀😀😀\u{fffd}\"... is not valid JSON",
        ),
        // V8 ends the snippet with the lone high surrogate '\u{d83d}' where this has U+FFFD.
        (
            "[1,\"😀😀😀😀😀😀😀😀\",x,\"😀😀😀😀😀😀😀😀\"]",
            "Unexpected token 'x', ...\"😀😀😀😀\",x,\"😀😀😀\u{fffd}\"... is not valid JSON",
        ),
    ];

    #[test]
    fn errors_match_node_v26() {
        for &(input, message) in NODE_V26_ERRORS {
            assert_eq!(
                parse(input).unwrap_err().message,
                message,
                "input {input:?}"
            );
        }
    }
}
