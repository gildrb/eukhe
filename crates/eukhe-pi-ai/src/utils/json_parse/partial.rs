//! Port of the `partial-json` 0.1.7 parser (`parse(text)` with the default
//! `Allow.ALL`): parses incomplete JSON produced by a streaming LLM. Every
//! `allow` check of the original is true under `Allow.ALL` and is folded in.
//!
//! JS-only results map to JSON like `JSON.stringify` writes them: `NaN` and
//! `±Infinity` become `null`. Property assignment semantics are kept: a
//! `__proto__` key never becomes an own property, and array-index keys
//! enumerate first.

use eukhe_types::pi_ai::{JsonObject, JsonValue};

use super::js_json::{self, js_object_order};
use crate::utils::js::js_trim;

/// Why a partial parse failed (`PartialJSON`, `MalformedJSON`, a nested
/// `SyntaxError`, or an empty input).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{0}")]
pub(crate) struct PartialParseError(String);

/// `partial-json`'s `parse(text)`.
pub(crate) fn parse(text: &str) -> Result<JsonValue, PartialParseError> {
    let trimmed = js_trim(text);
    if trimmed.is_empty() {
        return Err(PartialParseError(format!("{text} is empty")));
    }
    let mut parser = Parser {
        text: trimmed,
        bytes: trimmed.as_bytes(),
        index: 0,
    };
    parser.parse_any()
}

/// JS `String.prototype.substring(start, end)`: clamps to the length and
/// swaps reversed bounds. Indices here always sit on ASCII delimiters or the
/// string ends, so byte offsets equal UTF-16 offsets for slicing purposes.
fn substring(text: &str, start: usize, end: usize) -> &str {
    let start = start.min(text.len());
    let end = end.min(text.len());
    let (from, to) = if start > end {
        (end, start)
    } else {
        (start, end)
    };
    &text[from..to]
}

/// JS `text.lastIndexOf(needle)` mapped onto `substring`'s bounds: `-1` becomes 0.
fn last_index_of(text: &str, needle: char) -> usize {
    text.rfind(needle).unwrap_or(0)
}

fn json_parse(text: &str) -> Result<JsonValue, PartialParseError> {
    js_json::parse(text).map_err(|error| PartialParseError(error.to_string()))
}

struct Parser<'a> {
    text: &'a str,
    bytes: &'a [u8],
    index: usize,
}

impl Parser<'_> {
    fn partial(&self, message: &str) -> PartialParseError {
        PartialParseError(format!("{message} at position {}", self.index))
    }

    fn malformed(&self, message: &str) -> PartialParseError {
        PartialParseError(format!("{message} at position {}", self.index))
    }

    fn byte(&self) -> Option<u8> {
        self.bytes.get(self.index).copied()
    }

    fn rest(&self) -> &str {
        self.text.get(self.index..).unwrap_or("")
    }

    /// `jsonString.substring(index, index + n) === literal`, or a strict
    /// prefix of `literal` running to the end of the input.
    fn matches_literal(&self, literal: &str, min_remaining: usize) -> bool {
        let rest = self.rest();
        rest.starts_with(literal)
            || (min_remaining < rest.len()
                && rest.len() < literal.len()
                && literal.starts_with(rest))
    }

    fn parse_any(&mut self) -> Result<JsonValue, PartialParseError> {
        self.skip_blank();
        if self.index >= self.bytes.len() {
            return Err(self.partial("Unexpected end of input"));
        }
        match self.byte() {
            Some(b'"') => return self.parse_str(),
            Some(b'{') => return Ok(self.parse_obj()),
            Some(b'[') => return Ok(self.parse_arr()),
            _ => {}
        }
        let literals: [(&str, usize, JsonValue); 6] = [
            ("null", 0, JsonValue::Null),
            ("true", 0, JsonValue::Bool(true)),
            ("false", 0, JsonValue::Bool(false)),
            ("Infinity", 0, JsonValue::Null),
            ("-Infinity", 1, JsonValue::Null),
            ("NaN", 0, JsonValue::Null),
        ];
        for (literal, min_remaining, value) in literals {
            if self.matches_literal(literal, min_remaining) {
                self.index += literal.len();
                return Ok(value);
            }
        }
        self.parse_num()
    }

    fn parse_str(&mut self) -> Result<JsonValue, PartialParseError> {
        let start = self.index;
        let mut escape = false;
        self.index += 1;
        while self.index < self.bytes.len()
            && (self.bytes[self.index] != b'"' || (escape && self.bytes[self.index - 1] == b'\\'))
        {
            escape = if self.bytes[self.index] == b'\\' {
                !escape
            } else {
                false
            };
            self.index += 1;
        }
        let escape_offset = usize::from(escape);
        if self.byte() == Some(b'"') {
            self.index += 1;
            return json_parse(substring(self.text, start, self.index - escape_offset))
                .map_err(|error| self.malformed(&format!("SyntaxError: {error}")));
        }
        let closed = format!(
            "{}\"",
            substring(self.text, start, self.index - escape_offset)
        );
        json_parse(&closed).or_else(|_| {
            // Invalid escape sequence: drop everything from the last backslash.
            let fallback = format!(
                "{}\"",
                substring(self.text, start, last_index_of(self.text, '\\'))
            );
            json_parse(&fallback)
        })
    }

    fn parse_obj(&mut self) -> JsonValue {
        self.index += 1;
        self.skip_blank();
        let mut object = JsonObject::new();
        // Every failure inside returns the object built so far (`Allow.OBJ`).
        let _ = self.parse_obj_members(&mut object);
        JsonValue::Object(js_object_order(object))
    }

    /// The member loop of `parseObj`. `Ok(())` after the closing brace;
    /// `Err` when the input ended or failed early (the caller keeps `object`).
    fn parse_obj_members(&mut self, object: &mut JsonObject) -> Result<(), PartialParseError> {
        while self.byte() != Some(b'}') {
            self.skip_blank();
            if self.index >= self.bytes.len() {
                return Err(self.partial("Unexpected end of input"));
            }
            let key = match self.parse_str()? {
                JsonValue::String(key) => key,
                other => other.to_string(),
            };
            self.skip_blank();
            self.index += 1; // skip colon
            let value = self.parse_any()?;
            // `obj[key] = value`: assigning `__proto__` sets the prototype
            // (or is ignored), never an own property.
            if key != "__proto__" {
                object.insert(key, value);
            }
            self.skip_blank();
            if self.byte() == Some(b',') {
                self.index += 1;
            }
        }
        self.index += 1; // skip final brace
        Ok(())
    }

    fn parse_arr(&mut self) -> JsonValue {
        self.index += 1;
        let mut items = Vec::new();
        // Every failure inside returns the array built so far (`Allow.ARR`).
        let _ = self.parse_arr_items(&mut items);
        JsonValue::Array(items)
    }

    fn parse_arr_items(&mut self, items: &mut Vec<JsonValue>) -> Result<(), PartialParseError> {
        while self.byte() != Some(b']') {
            items.push(self.parse_any()?);
            self.skip_blank();
            if self.byte() == Some(b',') {
                self.index += 1;
            }
        }
        self.index += 1; // skip final bracket
        Ok(())
    }

    fn parse_num(&mut self) -> Result<JsonValue, PartialParseError> {
        if self.index == 0 {
            if self.text == "-" {
                return Err(self.malformed("Not sure what '-' is"));
            }
            return json_parse(self.text).or_else(|error| {
                json_parse(substring(self.text, 0, last_index_of(self.text, 'e')))
                    .map_err(|_| self.malformed(&format!("SyntaxError: {error}")))
            });
        }
        let start = self.index;
        if self.byte() == Some(b'-') {
            self.index += 1;
        }
        while self.byte().is_some_and(|byte| !b",]}".contains(&byte)) {
            self.index += 1;
        }
        let literal = substring(self.text, start, self.index);
        json_parse(literal).or_else(|_| {
            if literal == "-" {
                return Err(self.partial("Not sure what '-' is"));
            }
            json_parse(substring(self.text, start, last_index_of(self.text, 'e')))
                .map_err(|error| self.malformed(&format!("SyntaxError: {error}")))
        })
    }

    fn skip_blank(&mut self) {
        while let Some(b' ' | b'\n' | b'\r' | b'\t') = self.byte() {
            self.index += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn parses_incomplete_values() {
        assert_eq!(
            parse(r#"{"a": 1, "b": "hel"#).unwrap(),
            json!({"a": 1, "b": "hel"})
        );
        assert_eq!(parse(r#"{"a": [1, 2,"#).unwrap(), json!({"a": [1, 2]}));
        assert_eq!(parse(r#"{"a": tr"#).unwrap(), json!({"a": true}));
        assert_eq!(parse(r#"["x", nu"#).unwrap(), json!(["x", null]));
        assert_eq!(parse(r#"{"a": "x\u12"#).unwrap(), json!({"a": "x"}));
        assert_eq!(parse(r#"{"a": 12.5e"#).unwrap(), json!({"a": 12.5}));
        assert_eq!(
            parse(r#"{"__proto__": {"x": 1}, "b": 2}"#).unwrap(),
            json!({"b": 2})
        );
        assert_eq!(
            parse(r#"{"b": 1, "0": 2"#).unwrap(),
            json!({"0": 2, "b": 1})
        );
        assert!(parse("   ").is_err());
        assert!(parse("-").is_err());
    }
}
