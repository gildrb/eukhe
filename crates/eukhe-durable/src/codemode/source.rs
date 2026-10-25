//! Port of pi-codemode `source.ts`: the code mode source format, JavaScript
//! optionally preceded by one options line.
//!
//! ```js
//! // @options: {"max_output_tokens": 2000, "timeout_ms": 30000}
//! const text = await tools.read({ path: "package.json" });
//! text(JSON.parse(text).name);
//! ```
//!
//! The rule runs as the compiled Bend core
//! (`eukhe_bend::rules::codemode_source`; `bend/codemode_source.bend`,
//! `laws/codemode_source.bend`): every refusal and its text, which options
//! line is misplaced and its number, the JS `Object.keys` order of the keys
//! and the options set. This module reads the input's text facts: whether
//! it is blank, which lines after the first are options lines, whether the
//! text after the first newline is blank, and the first line's directive
//! as `serde_json` reads it (the JSON parse and the JS number facts stay
//! here). A script can be long: shipping it through the core would cost
//! far more than reading these facts.
//!
//! JS `trim()`/`trimStart()` become Rust `trim`/`trim_start`: both strip
//! Unicode `White_Space` (JS also strips U+FEFF, which is not `White_Space`).

use eukhe_bend::rules::codemode_source::{self, Answer, Directive, Facts, Field, Json, Num};
use serde_json::Value;

/// The first-line prefix of the options line.
pub const CODEMODE_OPTIONS_PREFIX: &str = "// @options:";

/// `Number.MAX_SAFE_INTEGER`.
const MAX_SAFE_INTEGER: u64 = (1 << 53) - 1;

/// Lark grammar for providers with grammar-constrained tool input. It only
/// fixes the shape of the options line; the options JSON and the code are
/// checked by [`parse_codemode_source`].
pub const CODEMODE_SOURCE_GRAMMAR: &str = r"
start: options_source | plain_source
options_source: OPTIONS_LINE NEWLINE SOURCE
plain_source: SOURCE

OPTIONS_LINE: /[ \t]*\/\/ @options:[^\r\n]*/
NEWLINE: /\r?\n/
SOURCE: /[\s\S]+/
";

/// The options of the options line.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CodemodeSourceOptions {
    /// `max_output_tokens`.
    pub max_output_tokens: Option<u64>,
    /// `timeout_ms`, in 1..=2147483647.
    pub timeout_ms: Option<u64>,
}

/// A parsed source: the code (from the newline after the options line, or
/// the whole input) and its options.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodemodeSource {
    /// The script.
    pub code: String,
    /// The options line's options.
    pub options: CodemodeSourceOptions,
}

/// Invalid source: empty input, invalid options, or a misplaced options
/// line.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{0}")]
pub struct CodemodeSourceError(pub String);

/// JS `Number.isSafeInteger(value) && value >= 0`. A JSON `1.0` is the
/// integer 1 in JS.
fn safe_integer(value: &Value) -> Option<u64> {
    let Value::Number(number) = value else {
        return None;
    };
    if let Some(integer) = number.as_u64() {
        return (integer <= MAX_SAFE_INTEGER).then_some(integer);
    }
    let float = number.as_f64()?;
    // `-0` passes `>= 0` in JS.
    #[expect(
        clippy::cast_precision_loss,
        reason = "2^53 - 1 is exactly representable as an `f64`"
    )]
    let max = MAX_SAFE_INTEGER as f64;
    #[expect(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "saturating cast, kept only when `float` is whole and in `0..=2^53 - 1`"
    )]
    let integer = float as u64;
    (float.fract() == 0.0 && (0.0..=max).contains(&float)).then_some(integer)
}

/// Whether `line` is an options line: its text after leading white space
/// starts with [`CODEMODE_OPTIONS_PREFIX`].
fn is_options_line(line: &str) -> bool {
    line.trim_start().starts_with(CODEMODE_OPTIONS_PREFIX)
}

/// Split an optional first-line `// @options: {...}` from the script.
///
/// # Errors
///
/// [`CodemodeSourceError`] for empty input, invalid options, and an options
/// line that is not the first line, which would otherwise be ignored
/// without notice; with the core's error for a key past its wire bound (8
/// Mi chars).
pub fn parse_codemode_source(input: &str) -> Result<CodemodeSource, CodemodeSourceError> {
    let mut lines = input.split('\n');
    let first = lines.next().unwrap_or_default();
    let options_lines: Vec<u64> = (1_u64..)
        .zip(lines)
        .filter(|(_, line)| is_options_line(line))
        .map(|(number, _)| number)
        .collect();
    let rest = input.find('\n').map_or("", |newline| &input[newline..]);
    let directive = first
        .trim_start()
        .strip_prefix(CODEMODE_OPTIONS_PREFIX)
        .map(str::trim);
    let parsed = directive.map(serde_json::from_str::<Value>);
    let invalid = match &parsed {
        Some(Err(error)) => error.to_string(),
        Some(Ok(_)) | None => String::new(),
    };
    let fields: Vec<Field<'_>> = match &parsed {
        Some(Ok(Value::Object(object))) => object
            .iter()
            .map(|(key, value)| Field {
                key,
                value: safe_integer(value).map_or(Num::NotSafe, Num::Safe),
            })
            .collect(),
        Some(Ok(_) | Err(_)) | None => Vec::new(),
    };
    let directive = directive
        .zip(parsed.as_ref())
        .map(|(text, parsed)| Directive {
            empty: text.is_empty(),
            json: match parsed {
                Err(_) => Json::Invalid(&invalid),
                Ok(Value::Object(_)) => Json::Object(&fields),
                Ok(_) => Json::NotObject,
            },
        });
    let facts = Facts {
        blank: input.trim().is_empty(),
        options_lines: &options_lines,
        rest_blank: rest.trim().is_empty(),
        directive,
    };
    match codemode_source::parse(&facts).map_err(|error| CodemodeSourceError(error.to_string()))? {
        Answer::Refused(text) => Err(CodemodeSourceError(text)),
        Answer::Plain => Ok(CodemodeSource {
            code: input.to_owned(),
            options: CodemodeSourceOptions::default(),
        }),
        Answer::Split {
            max_output_tokens,
            timeout_ms,
        } => Ok(CodemodeSource {
            code: rest.to_owned(),
            options: CodemodeSourceOptions {
                max_output_tokens,
                timeout_ms,
            },
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reaches_the_core() {
        assert_eq!(
            parse_codemode_source(
                "  // @options: {\"max_output_tokens\": 1.0, \"timeout_ms\": 1e3}\r\nreturn 1;"
            ),
            Ok(CodemodeSource {
                code: "\nreturn 1;".to_owned(),
                options: CodemodeSourceOptions {
                    max_output_tokens: Some(1),
                    timeout_ms: Some(1000),
                },
            })
        );
        assert_eq!(
            parse_codemode_source("x;\ny;\n  // @options: {}"),
            Err(CodemodeSourceError(
                "The // @options: line must be the first line of the input; found one on line 3"
                    .to_owned()
            ))
        );
    }

    #[test]
    fn safe_integers_are_js_safe_non_negative_integers() {
        let read = |json: &str| safe_integer(&serde_json::from_str(json).unwrap());
        assert_eq!(
            [
                "0",
                "-0",
                "1.0",
                "1e3",
                "9007199254740991",
                "9007199254740992",
                "-1",
                "1.5",
                "null",
                "\"1\""
            ]
            .map(read),
            [
                Some(0),
                Some(0),
                Some(1),
                Some(1000),
                Some(9_007_199_254_740_991),
                None,
                None,
                None,
                None,
                None
            ]
        );
    }

    #[test]
    fn invalid_json_keeps_serde_text() {
        let Err(CodemodeSourceError(message)) = parse_codemode_source("// @options: {\nx") else {
            panic!("expected an error");
        };
        assert!(message.starts_with(
            "@options must be valid JSON with supported fields `max_output_tokens` and `timeout_ms`: "
        ));
    }
}
