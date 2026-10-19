//! A forgiving JSON dialect for the final parse of tool-call arguments: the
//! strict (final-parse) mode of omp's `RelaxedJson` over its `JsonLexer`
//! (`packages/utils/src/json-parse.ts:143-287`, `json-lexer.ts:187-467`).
//! It reads the malformations models commonly produce:
//!
//! - single-quoted strings and unquoted object keys;
//! - leading, doubled, and trailing commas, and `//` and `/* */` comments;
//! - Python literals `True`, `False`, `None`, and `0x` / `0b` numbers, a sign
//!   or a leading or trailing dot (JS `Number(token)`);
//! - raw control characters and invalid escapes (`\q` stays `\q`) in strings;
//! - an apostrophe inside a single-quoted string: a `'` closes the string
//!   only before a value terminator (`'it's'` is `it's`);
//! - an unquoted value (`{"path": src/main.rs}`), up to the next `,`, `}`,
//!   `]`, or line end.
//!
//! A truncated document, trailing characters, a non-finite number, and a
//! bareword that may swallow a sibling field (it holds `"`, `{`, `[`, or a
//! key-like `:`) are rejected: a final parse never accepts a half-formed
//! call. Objects keep `JSON.parse` semantics: a duplicate key keeps its first
//! position and its last value, array-index keys come first, and lone
//! surrogate escapes become U+FFFD.

use eukhe_types::pi_ai::{JsonObject, JsonValue};

use super::js_json::js_object_order;
use crate::utils::js::js_number_value;
use crate::utils::validation::js_value::string_to_number;

/// Keyword literals: JSON's and Python's (`json-lexer.ts:85-92`).
const KEYWORDS: [(&str, JsonValue); 6] = [
    ("true", JsonValue::Bool(true)),
    ("false", JsonValue::Bool(false)),
    ("null", JsonValue::Null),
    ("True", JsonValue::Bool(true)),
    ("False", JsonValue::Bool(false)),
    ("None", JsonValue::Null),
];

/// JS-only atoms a bareword never stands for: a tool must not run with a
/// non-finite or undefined argument read as a string (`json-lexer.ts:98-104`).
const NON_RECOVERABLE_BAREWORDS: [&str; 5] =
    ["NaN", "Infinity", "-Infinity", "+Infinity", "undefined"];

/// Whether an unquoted value is read as a string at this position: only
/// inside a container, never as the whole document.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Barewords {
    Recovered,
    Refused,
}

/// `text` in the relaxed dialect, or `None` when even the dialect rejects it.
pub(crate) fn parse(text: &str) -> Option<JsonValue> {
    let mut parser = Parser {
        text,
        bytes: text.as_bytes(),
        pos: 0,
    };
    parser.skip_insignificant();
    let value = parser.value(Barewords::Refused)?;
    parser.skip_insignificant();
    (parser.pos == parser.bytes.len()).then_some(value)
}

/// The index of the first byte at or after `index` that is not whitespace or
/// part of a `//` or `/* */` comment. An unterminated block comment runs to
/// the end; a lone `/` stays.
fn skip_insignificant(bytes: &[u8], mut index: usize) -> usize {
    loop {
        while let Some(b' ' | b'\t' | b'\n' | b'\r') = bytes.get(index) {
            index += 1;
        }
        if bytes.get(index) != Some(&b'/') {
            return index;
        }
        match bytes.get(index + 1) {
            Some(b'/') => {
                index += 2;
                while bytes.get(index).is_some_and(|&byte| byte != b'\n') {
                    index += 1;
                }
            }
            Some(b'*') => {
                index += 2;
                while index + 1 < bytes.len() && !(bytes[index] == b'*' && bytes[index + 1] == b'/')
                {
                    index += 1;
                }
                index = (index + 2).min(bytes.len());
            }
            Some(_) | None => return index,
        }
    }
}

/// Four hex digits at `index`, as a UTF-16 code unit.
fn hex4(bytes: &[u8], index: usize) -> Option<u16> {
    let digits = std::str::from_utf8(bytes.get(index..index + 4)?).ok()?;
    if !digits.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return None;
    }
    u16::from_str_radix(digits, 16).ok()
}

struct Parser<'a> {
    text: &'a str,
    bytes: &'a [u8],
    pos: usize,
}

impl Parser<'_> {
    fn skip_insignificant(&mut self) {
        self.pos = skip_insignificant(self.bytes, self.pos);
    }

    fn value(&mut self, barewords: Barewords) -> Option<JsonValue> {
        match *self.bytes.get(self.pos)? {
            b'{' => self.object(),
            b'[' => self.array(),
            quote @ (b'"' | b'\'') => self.string(quote).map(JsonValue::String),
            b'-' | b'+' | b'.' | b'0'..=b'9' => self.number(),
            _ => {
                if let Some(keyword) = self.keyword() {
                    return Some(keyword);
                }
                match barewords {
                    Barewords::Recovered => self.bareword().map(JsonValue::String),
                    Barewords::Refused => None,
                }
            }
        }
    }

    /// A string opened by `quote` at the cursor (`json-lexer.ts:228-357`). A
    /// double quote closes at the first unescaped `"`, as in JSON; a single
    /// quote closes only before a value terminator.
    fn string(&mut self, quote: u8) -> Option<String> {
        let mut out = String::new();
        let mut index = self.pos + 1;
        let mut run_start = index;
        while let Some(&byte) = self.bytes.get(index) {
            if byte == quote {
                if quote == b'"' || self.quote_closes(index + 1) {
                    out.push_str(&self.text[run_start..index]);
                    self.pos = index + 1;
                    return Some(out);
                }
                index += 1;
                continue;
            }
            if byte != b'\\' {
                index += 1;
                continue;
            }
            out.push_str(&self.text[run_start..index]);
            // A backslash at the end leaves the string unterminated.
            let escape = *self.bytes.get(index + 1)?;
            index += 2;
            match escape {
                b'"' => out.push('"'),
                b'\'' => out.push('\''),
                b'\\' => out.push('\\'),
                b'/' => out.push('/'),
                b'b' => out.push('\u{0008}'),
                b'f' => out.push('\u{000C}'),
                b'n' => out.push('\n'),
                b'r' => out.push('\r'),
                b't' => out.push('\t'),
                b'u' => match hex4(self.bytes, index) {
                    Some(unit) => {
                        index += 4;
                        let pairs = (0xD800..0xDC00).contains(&unit)
                            && self.bytes[index..].starts_with(b"\\u");
                        let low = hex4(self.bytes, index + 2)
                            .filter(|low| pairs && (0xDC00..0xE000).contains(low));
                        let code = match low {
                            Some(low) => {
                                index += 6;
                                0x10000
                                    + ((u32::from(unit) - 0xD800) << 10)
                                    + (u32::from(low) - 0xDC00)
                            }
                            None => u32::from(unit),
                        };
                        out.push(char::from_u32(code).unwrap_or('\u{FFFD}'));
                    }
                    // An invalid `\u` stays literal.
                    None => out.push_str("\\u"),
                },
                // An invalid escape keeps its backslash; the escaped
                // character, which may be multi-byte, starts the next run.
                _ => {
                    out.push('\\');
                    index -= 1;
                }
            }
            run_start = index;
        }
        None
    }

    /// Whether a single quote closes its string: the next significant byte
    /// ends a value, or the input ends (`json-lexer.ts:364-372`).
    fn quote_closes(&self, from: usize) -> bool {
        match self.bytes.get(skip_insignificant(self.bytes, from)) {
            Some(b',' | b'}' | b']' | b':') | None => true,
            Some(_) => false,
        }
    }

    /// A numeric token read with JS `Number(token)`; a non-finite or
    /// malformed token is rejected (`json-lexer.ts:380-391`).
    fn number(&mut self) -> Option<JsonValue> {
        let start = self.pos;
        while self
            .bytes
            .get(self.pos)
            .is_some_and(|&byte| byte.is_ascii_hexdigit() || b"+-.xX".contains(&byte))
        {
            self.pos += 1;
        }
        let number = string_to_number(&self.text[start..self.pos]);
        number.is_finite().then(|| js_number_value(number))
    }

    /// A keyword at the cursor that no identifier character continues
    /// (`Truex` is no keyword).
    fn keyword(&mut self) -> Option<JsonValue> {
        let rest = &self.bytes[self.pos..];
        let (word, value) = KEYWORDS.iter().find(|(word, _)| {
            rest.starts_with(word.as_bytes())
                && !rest
                    .get(word.len())
                    .is_some_and(|&byte| byte.is_ascii_alphanumeric() || b"_$".contains(&byte))
        })?;
        self.pos += word.len();
        Some(value.clone())
    }

    /// An unquoted value up to `,`, `}`, `]`, or a line end, trailing
    /// whitespace trimmed (`json-lexer.ts:437-461`).
    fn bareword(&mut self) -> Option<String> {
        let start = self.pos;
        let mut index = start;
        loop {
            // The end of the input first: a truncated value.
            match *self.bytes.get(index)? {
                b',' | b'}' | b']' | b'\n' | b'\r' => break,
                b'"' | b'{' | b'[' => return None,
                // A `:` before `/` or `\` is a URL or a Windows path.
                b':' if !matches!(self.bytes.get(index + 1), Some(b'/' | b'\\')) => return None,
                _ => index += 1,
            }
        }
        let word = self.text[start..index].trim_end_matches([' ', '\t']);
        if NON_RECOVERABLE_BAREWORDS.contains(&word) {
            return None;
        }
        self.pos = index;
        Some(word.to_owned())
    }

    /// An unquoted key: up to `:`, `,`, `}`, or whitespace; never empty.
    fn unquoted_key(&mut self) -> Option<String> {
        let start = self.pos;
        while self
            .bytes
            .get(self.pos)
            .is_some_and(|byte| !b":,} \t\n\r".contains(byte))
        {
            self.pos += 1;
        }
        (self.pos > start).then(|| self.text[start..self.pos].to_owned())
    }

    fn object(&mut self) -> Option<JsonValue> {
        self.pos += 1;
        let mut map = JsonObject::new();
        loop {
            self.skip_insignificant();
            let key = match *self.bytes.get(self.pos)? {
                b'}' => {
                    self.pos += 1;
                    return Some(JsonValue::Object(js_object_order(map)));
                }
                b',' => {
                    self.pos += 1;
                    continue;
                }
                quote @ (b'"' | b'\'') => self.string(quote)?,
                _ => self.unquoted_key()?,
            };
            self.skip_insignificant();
            if self.bytes.get(self.pos) != Some(&b':') {
                return None;
            }
            self.pos += 1;
            self.skip_insignificant();
            let value = self.value(Barewords::Recovered)?;
            map.insert(key, value);
            self.skip_insignificant();
            match self.bytes.get(self.pos) {
                Some(b',') => self.pos += 1,
                Some(b'}') => {}
                Some(_) | None => return None,
            }
        }
    }

    fn array(&mut self) -> Option<JsonValue> {
        self.pos += 1;
        let mut items = Vec::new();
        loop {
            self.skip_insignificant();
            match *self.bytes.get(self.pos)? {
                b']' => {
                    self.pos += 1;
                    return Some(JsonValue::Array(items));
                }
                b',' => {
                    self.pos += 1;
                    continue;
                }
                _ => {}
            }
            items.push(self.value(Barewords::Recovered)?);
            self.skip_insignificant();
            match self.bytes.get(self.pos) {
                Some(b',') => self.pos += 1,
                Some(b']') => {}
                Some(_) | None => return None,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn reads_the_relaxed_dialect() {
        assert_eq!(
            parse("{'path': 'a.rs', limit: 3, /* note */ case: True, skip: None,}"),
            Some(json!({"path": "a.rs", "limit": 3, "case": true, "skip": null}))
        );
        assert_eq!(
            parse("// lead\n[,1,,+2, .5, 0x10, 0b11,] // tail"),
            Some(json!([1, 2, 0.5, 16, 3]))
        );
        assert_eq!(
            parse("{\"text\": \"a\tb\\q\\u00e9\\ud83d\\ude00\\ud800\"}"),
            Some(json!({"text": "a\tb\\q\u{e9}\u{1F600}\u{FFFD}"}))
        );
        assert_eq!(
            parse("{'note': 'it's', 'path': C:\\dir\\é, 'url': http://x/y }"),
            Some(json!({"note": "it's", "path": "C:\\dir\\é", "url": "http://x/y"}))
        );
        assert_eq!(
            parse("{\"name\": , \"2\": 1, \"1\": 0, \"name\": 'n'}"),
            Some(json!({"1": 0, "2": 1, "name": "n"}))
        );
        assert_eq!(parse("'\\é'"), Some(json!("\\é")));
    }

    #[test]
    fn rejects_truncation_trailing_garbage_and_unsafe_barewords() {
        for text in [
            "",
            "{\"path\": \"a.rs\"",
            "{\"path\": \"a.rs",
            "{\"path\": \"a\\",
            "[1, 2",
            "{\"path\": a.rs",
            "{\"a\": 1} x",
            "{\"a\": 1}}",
            "{\"a\": foo \"b\": 2}",
            "{\"a\": 1 \"b\": 2}",
            "{\"a\": x: 1}",
            "{\"a\": NaN}",
            "{\"a\": -Infinity}",
            "{\"a\": 1e400}",
            "{\"a\": 1.2.3}",
            "{\"a\" 1}",
            "bare",
        ] {
            assert_eq!(parse(text), None, "{text:?}");
        }
    }
}
