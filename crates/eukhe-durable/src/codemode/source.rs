//! Port of pi-codemode `source.ts`: the code mode source format, JavaScript
//! optionally preceded by one options line.
//!
//! ```js
//! // @options: {"max_output_tokens": 2000, "timeout_ms": 30000}
//! const text = await tools.read({ path: "package.json" });
//! text(JSON.parse(text).name);
//! ```
//!
//! JS `trim()`/`trimStart()` become Rust `trim`/`trim_start`: both strip
//! Unicode `White_Space` (JS also strips U+FEFF, which is not `White_Space`).

use serde_json::Value;

/// The first-line prefix of the options line.
pub const CODEMODE_OPTIONS_PREFIX: &str = "// @options:";

const SUPPORTED_FIELDS: [&str; 2] = ["max_output_tokens", "timeout_ms"];
const SUPPORTED_FIELDS_TEXT: &str = "`max_output_tokens` and `timeout_ms`";
/// Largest delay `setTimeout` supports, which bounds `timeout_ms`.
const MAX_TIMEOUT_MS: u64 = 2_147_483_647;
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

/// Whether `key` is an array index, which JS `Object.keys` lists first, in
/// numeric order.
fn array_index(key: &str) -> Option<u32> {
    if key != "0" && key.starts_with('0') {
        return None;
    }
    if !key.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    key.parse::<u32>().ok().filter(|index| *index != u32::MAX)
}

/// The first key of `Object.keys(fields)` that is not supported.
fn unsupported_key(fields: &serde_json::Map<String, Value>) -> Option<&str> {
    // Array indices come first in JS order and are never supported.
    let first_index = fields
        .keys()
        .filter_map(|key| array_index(key).map(|index| (index, key.as_str())))
        .min_by_key(|(index, _)| *index);
    if let Some((_, key)) = first_index {
        return Some(key);
    }
    fields
        .keys()
        .map(String::as_str)
        .find(|key| !SUPPORTED_FIELDS.contains(key))
}

fn not_an_object() -> CodemodeSourceError {
    CodemodeSourceError(format!(
        "@options must be a JSON object with supported fields {SUPPORTED_FIELDS_TEXT}"
    ))
}

fn parse_options(directive: &str) -> Result<CodemodeSourceOptions, CodemodeSourceError> {
    if directive.is_empty() {
        return Err(not_an_object());
    }
    // The detail is serde_json's error text, not V8's `JSON.parse` message.
    let value: Value = serde_json::from_str(directive).map_err(|error| {
        CodemodeSourceError(format!(
            "@options must be valid JSON with supported fields {SUPPORTED_FIELDS_TEXT}: {error}"
        ))
    })?;
    let Value::Object(fields) = value else {
        return Err(not_an_object());
    };
    if let Some(key) = unsupported_key(&fields) {
        return Err(CodemodeSourceError(format!(
            "@options only supports {SUPPORTED_FIELDS_TEXT}; got `{key}`"
        )));
    }
    let mut options = CodemodeSourceOptions::default();
    if let Some(value) = fields.get("max_output_tokens") {
        let tokens = safe_integer(value).ok_or_else(|| {
            CodemodeSourceError(
                "@options field `max_output_tokens` must be a non-negative safe integer".to_owned(),
            )
        })?;
        options.max_output_tokens = Some(tokens);
    }
    if let Some(value) = fields.get("timeout_ms") {
        let timeout = safe_integer(value)
            .filter(|timeout| (1..=MAX_TIMEOUT_MS).contains(timeout))
            .ok_or_else(|| {
                CodemodeSourceError(format!(
                    "@options field `timeout_ms` must be a positive integer up to {MAX_TIMEOUT_MS}"
                ))
            })?;
        options.timeout_ms = Some(timeout);
    }
    Ok(options)
}

/// Split an optional first-line `// @options: {...}` from the script.
///
/// # Errors
///
/// [`CodemodeSourceError`] for empty input, invalid options, and an options
/// line that is not the first line, which would otherwise be ignored
/// without notice.
pub fn parse_codemode_source(input: &str) -> Result<CodemodeSource, CodemodeSourceError> {
    if input.trim().is_empty() {
        return Err(CodemodeSourceError(
            "Expected JavaScript source text (non-empty). Provide JS only, optionally with a first line `// @options: {\"max_output_tokens\": 1000}`.".to_owned(),
        ));
    }
    let mut lines = input.split('\n');
    let first = lines.next().unwrap_or_default();
    if let Some(misplaced) =
        lines.position(|line| line.trim_start().starts_with(CODEMODE_OPTIONS_PREFIX))
    {
        return Err(CodemodeSourceError(format!(
            "The {CODEMODE_OPTIONS_PREFIX} line must be the first line of the input; found one on line {}",
            misplaced + 2
        )));
    }
    let first_line = first.strip_suffix('\r').unwrap_or(first);
    let trimmed = first_line.trim_start();
    let Some(directive) = trimmed.strip_prefix(CODEMODE_OPTIONS_PREFIX) else {
        return Ok(CodemodeSource {
            code: input.to_owned(),
            options: CodemodeSourceOptions::default(),
        });
    };
    let code = input.find('\n').map_or("", |newline| &input[newline..]);
    if code.trim().is_empty() {
        return Err(CodemodeSourceError(
            "The @options line must be followed by JavaScript source on subsequent lines"
                .to_owned(),
        ));
    }
    Ok(CodemodeSource {
        code: code.to_owned(),
        options: parse_options(directive.trim())?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn error(message: &str) -> Result<CodemodeSource, CodemodeSourceError> {
        Err(CodemodeSourceError(message.to_owned()))
    }

    #[test]
    fn plain_source_is_kept() {
        assert_eq!(
            parse_codemode_source("text(1);\nreturn 2;"),
            Ok(CodemodeSource {
                code: "text(1);\nreturn 2;".to_owned(),
                options: CodemodeSourceOptions::default(),
            })
        );
    }

    #[test]
    fn options_line_is_split() {
        assert_eq!(
            parse_codemode_source(
                "  // @options: {\"max_output_tokens\": 2000, \"timeout_ms\": 30000}\r\nreturn 1;"
            ),
            Ok(CodemodeSource {
                code: "\nreturn 1;".to_owned(),
                options: CodemodeSourceOptions {
                    max_output_tokens: Some(2000),
                    timeout_ms: Some(30000),
                },
            })
        );
        assert_eq!(
            parse_codemode_source(
                "// @options: {\"max_output_tokens\": 1.0, \"timeout_ms\": 1e3}\nx"
            ),
            Ok(CodemodeSource {
                code: "\nx".to_owned(),
                options: CodemodeSourceOptions {
                    max_output_tokens: Some(1),
                    timeout_ms: Some(1000),
                },
            })
        );
    }

    #[test]
    fn empty_input_fails() {
        assert_eq!(
            parse_codemode_source(" \n\t"),
            error("Expected JavaScript source text (non-empty). Provide JS only, optionally with a first line `// @options: {\"max_output_tokens\": 1000}`.")
        );
    }

    #[test]
    fn misplaced_options_line_fails() {
        assert_eq!(
            parse_codemode_source("x;\ny;\n  // @options: {}"),
            error("The // @options: line must be the first line of the input; found one on line 3")
        );
    }

    #[test]
    fn options_without_code_fail() {
        assert_eq!(
            parse_codemode_source("// @options: {}\n  \n"),
            error("The @options line must be followed by JavaScript source on subsequent lines")
        );
        assert_eq!(
            parse_codemode_source("// @options: {}"),
            error("The @options line must be followed by JavaScript source on subsequent lines")
        );
    }

    #[test]
    fn invalid_options_fail() {
        let object = "@options must be a JSON object with supported fields `max_output_tokens` and `timeout_ms`";
        assert_eq!(parse_codemode_source("// @options:\nx"), error(object));
        assert_eq!(parse_codemode_source("// @options: [1]\nx"), error(object));
        assert_eq!(parse_codemode_source("// @options: null\nx"), error(object));
        assert_eq!(
            parse_codemode_source("// @options: {\"timeout_ms\": 1, \"b\": 2, \"7\": 3}\nx"),
            error("@options only supports `max_output_tokens` and `timeout_ms`; got `7`")
        );
        assert_eq!(
            parse_codemode_source("// @options: {\"b\": 2, \"c\": 3}\nx"),
            error("@options only supports `max_output_tokens` and `timeout_ms`; got `b`")
        );
        let tokens = "@options field `max_output_tokens` must be a non-negative safe integer";
        assert_eq!(
            parse_codemode_source("// @options: {\"max_output_tokens\": -1}\nx"),
            error(tokens)
        );
        assert_eq!(
            parse_codemode_source("// @options: {\"max_output_tokens\": 1.5}\nx"),
            error(tokens)
        );
        assert_eq!(
            parse_codemode_source("// @options: {\"max_output_tokens\": null}\nx"),
            error(tokens)
        );
        assert_eq!(
            parse_codemode_source("// @options: {\"max_output_tokens\": 9007199254740992}\nx"),
            error(tokens)
        );
        let timeout = "@options field `timeout_ms` must be a positive integer up to 2147483647";
        assert_eq!(
            parse_codemode_source("// @options: {\"timeout_ms\": 0}\nx"),
            error(timeout)
        );
        assert_eq!(
            parse_codemode_source("// @options: {\"timeout_ms\": 2147483648}\nx"),
            error(timeout)
        );
        assert_eq!(
            parse_codemode_source("// @options: {\"timeout_ms\": 2147483647}\nx")
                .map(|source| source.options),
            Ok(CodemodeSourceOptions {
                max_output_tokens: None,
                timeout_ms: Some(2_147_483_647)
            })
        );
    }

    #[test]
    fn invalid_json_fails() {
        let Err(CodemodeSourceError(message)) = parse_codemode_source("// @options: {\nx") else {
            panic!("expected an error");
        };
        assert!(message.starts_with(
            "@options must be valid JSON with supported fields `max_output_tokens` and `timeout_ms`: "
        ));
    }
}
