//! A workflow script's leading `export const meta = { ... };`: a pure
//! literal (strings, numbers, booleans, `null`, arrays, objects; keys bare
//! or quoted; trailing commas), read without running the script. The
//! script the VM runs declares `const meta` with the same value.

use serde::{Deserialize, Serialize};
use serde_json::{Map, Number, Value};

/// What a script's `meta` declares.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct WorkflowMeta {
    pub(crate) name: String,
    pub(crate) description: String,
    /// Phase titles, in order.
    pub(crate) phases: Vec<String>,
}

/// A script split into its meta and the body the VM runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ParsedScript {
    pub(crate) meta: WorkflowMeta,
    /// The script with `export const meta = <literal>;` replaced by
    /// `const meta = <JSON>;`.
    pub(crate) body: String,
}

const META_PREFIX: &str = "export const meta";

/// Why a script's `meta` cannot be read.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum WorkflowMetaError {
    /// The script does not start with `export const meta`.
    #[error("a workflow script starts with `export const meta = {{ name, description, phases }}`")]
    MissingMeta,
    /// `export const meta` is not followed by `=`.
    #[error("`export const meta` must be assigned a literal")]
    NotAssigned,
    /// The literal is not pure; `shown` is the text where reading stopped.
    #[error("meta must be a pure literal: {problem} at `{shown}`")]
    NotPure {
        #[source]
        problem: LiteralProblem,
        shown: String,
    },
    /// The literal is not an object.
    #[error("meta must be an object")]
    NotObject,
    /// `name` or `description` is missing, blank, or not a string.
    #[error("meta.{key} must be a non-empty string")]
    NotNonEmptyString { key: &'static str },
    /// `phases` is missing or not an array.
    #[error("meta.phases must be an array")]
    PhasesNotArray,
    /// A `phases` object lacks a string `title`.
    #[error("each meta.phases item needs a string title")]
    PhaseWithoutTitle,
    /// A `phases` item is neither an object nor a string.
    #[error("each meta.phases item is {{ title }} or a string")]
    PhaseNotTitleOrString,
}

/// What makes a `meta` literal impure.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum LiteralProblem {
    #[error("an identifier or call is not a literal")]
    NotALiteral,
    #[error("the literal ends early")]
    EndsEarly,
    #[error("expected a key")]
    ExpectedKey,
    #[error("expected `:`")]
    ExpectedColon,
    #[error("expected `,` or `}}`")]
    ExpectedCommaOrBrace,
    #[error("expected `,` or `]`")]
    ExpectedCommaOrBracket,
    #[error("unterminated string")]
    UnterminatedString,
    #[error("a template substitution is not a literal")]
    TemplateSubstitution,
    /// Fewer than four characters follow `\u`.
    #[error("bad \\u")]
    ShortUnicodeEscape,
    /// The four characters after `\u` are not hex.
    #[error("bad \\u escape")]
    UnicodeEscapeHex(#[source] std::num::ParseIntError),
    /// The `\u` code is not a Unicode scalar value.
    #[error("bad \\u escape")]
    UnicodeEscapeScalar { code: u32 },
    /// The number does not parse.
    #[error("bad number")]
    Number(#[source] std::num::ParseFloatError),
    /// The number is not finite.
    #[error("bad number")]
    NonFiniteNumber,
}

/// Split `script` into its meta and body.
///
/// # Errors
///
/// The script does not start with `export const meta = { ... }` (comments
/// and blank lines may come first), the literal is not pure, or it lacks a
/// string `name`, a string `description`, or a `phases` array of
/// `{ title }` objects or strings.
pub(crate) fn parse_script(script: &str) -> Result<ParsedScript, WorkflowMetaError> {
    let start = skip_trivia(script, 0);
    if !script[start..].starts_with(META_PREFIX) {
        return Err(WorkflowMetaError::MissingMeta);
    }
    let mut parser = Parser {
        text: script,
        at: start + META_PREFIX.len(),
    };
    parser.trivia();
    if !parser.eat('=') {
        return Err(WorkflowMetaError::NotAssigned);
    }
    let value = parser.value()?;
    let mut end = parser.at;
    let after = skip_trivia(script, end);
    if script[after..].starts_with(';') {
        end = after + 1;
    }
    let meta = meta_of(&value)?;
    let body = format!("const meta = {value};{}", &script[end..]);
    Ok(ParsedScript { meta, body })
}

fn meta_of(value: &Value) -> Result<WorkflowMeta, WorkflowMetaError> {
    let Value::Object(object) = value else {
        return Err(WorkflowMetaError::NotObject);
    };
    let text = |key: &'static str| match object.get(key) {
        Some(Value::String(text)) if !text.trim().is_empty() => Ok(text.trim().to_owned()),
        Some(_) | None => Err(WorkflowMetaError::NotNonEmptyString { key }),
    };
    let name = text("name")?;
    let description = text("description")?;
    let Some(Value::Array(items)) = object.get("phases") else {
        return Err(WorkflowMetaError::PhasesNotArray);
    };
    let phases = items
        .iter()
        .map(|item| match item {
            Value::String(title) => Ok(title.clone()),
            Value::Object(phase) => match phase.get("title") {
                Some(Value::String(title)) => Ok(title.clone()),
                Some(_) | None => Err(WorkflowMetaError::PhaseWithoutTitle),
            },
            Value::Null | Value::Bool(_) | Value::Number(_) | Value::Array(_) => {
                Err(WorkflowMetaError::PhaseNotTitleOrString)
            }
        })
        .collect::<Result<Vec<String>, WorkflowMetaError>>()?;
    Ok(WorkflowMeta {
        name,
        description,
        phases,
    })
}

/// The index after the whitespace and comments from `at`.
fn skip_trivia(text: &str, at: usize) -> usize {
    let mut parser = Parser { text, at };
    parser.trivia();
    parser.at
}

struct Parser<'a> {
    text: &'a str,
    at: usize,
}

impl Parser<'_> {
    fn rest(&self) -> &str {
        &self.text[self.at..]
    }

    fn peek(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn eat(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.at += expected.len_utf8();
            true
        } else {
            false
        }
    }

    fn trivia(&mut self) {
        loop {
            let rest = self.rest();
            let trimmed = rest.trim_start();
            let skipped = rest.len() - trimmed.len();
            let comment = if let Some(comment) = trimmed.strip_prefix("//") {
                Some(2 + comment.find('\n').unwrap_or(comment.len()))
            } else {
                trimmed
                    .strip_prefix("/*")
                    .map(|comment| 2 + comment.find("*/").map_or(comment.len(), |end| end + 2))
            };
            self.at += skipped;
            match comment {
                Some(length) => self.at += length,
                None => return,
            }
        }
    }

    fn error(&self, problem: LiteralProblem) -> WorkflowMetaError {
        WorkflowMetaError::NotPure {
            problem,
            shown: self.rest().chars().take(24).collect(),
        }
    }

    fn value(&mut self) -> Result<Value, WorkflowMetaError> {
        self.trivia();
        match self.peek() {
            Some('{') => self.object(),
            Some('[') => self.array(),
            Some(quote @ ('"' | '\'' | '`')) => self.string(quote).map(Value::String),
            Some(c) if c == '-' || c.is_ascii_digit() => self.number(),
            Some(_) => {
                let word = self.word();
                match word.as_str() {
                    "true" => Ok(Value::Bool(true)),
                    "false" => Ok(Value::Bool(false)),
                    "null" => Ok(Value::Null),
                    _ => Err(self.error(LiteralProblem::NotALiteral)),
                }
            }
            None => Err(self.error(LiteralProblem::EndsEarly)),
        }
    }

    fn word(&mut self) -> String {
        let length = self
            .rest()
            .find(|c: char| !(c.is_alphanumeric() || c == '_' || c == '$'))
            .unwrap_or(self.rest().len());
        let word = self.rest()[..length].to_owned();
        self.at += length;
        word
    }

    fn object(&mut self) -> Result<Value, WorkflowMetaError> {
        self.eat('{');
        let mut object = Map::new();
        loop {
            self.trivia();
            if self.eat('}') {
                return Ok(Value::Object(object));
            }
            let key = match self.peek() {
                Some(quote @ ('"' | '\'')) => self.string(quote)?,
                Some(c) if c.is_alphabetic() || c == '_' || c == '$' => self.word(),
                Some(_) | None => return Err(self.error(LiteralProblem::ExpectedKey)),
            };
            self.trivia();
            if !self.eat(':') {
                return Err(self.error(LiteralProblem::ExpectedColon));
            }
            let value = self.value()?;
            object.insert(key, value);
            self.trivia();
            if self.eat(',') {
                continue;
            }
            if self.eat('}') {
                return Ok(Value::Object(object));
            }
            return Err(self.error(LiteralProblem::ExpectedCommaOrBrace));
        }
    }

    fn array(&mut self) -> Result<Value, WorkflowMetaError> {
        self.eat('[');
        let mut items = Vec::new();
        loop {
            self.trivia();
            if self.eat(']') {
                return Ok(Value::Array(items));
            }
            items.push(self.value()?);
            self.trivia();
            if self.eat(',') {
                continue;
            }
            if self.eat(']') {
                return Ok(Value::Array(items));
            }
            return Err(self.error(LiteralProblem::ExpectedCommaOrBracket));
        }
    }

    fn string(&mut self, quote: char) -> Result<String, WorkflowMetaError> {
        self.eat(quote);
        let mut out = String::new();
        loop {
            let Some(c) = self.peek() else {
                return Err(self.error(LiteralProblem::UnterminatedString));
            };
            self.at += c.len_utf8();
            if c == quote {
                return Ok(out);
            }
            if quote == '`' && c == '$' && self.peek() == Some('{') {
                return Err(self.error(LiteralProblem::TemplateSubstitution));
            }
            if c != '\\' {
                out.push(c);
                continue;
            }
            let Some(escaped) = self.peek() else {
                return Err(self.error(LiteralProblem::UnterminatedString));
            };
            self.at += escaped.len_utf8();
            out.push(match escaped {
                'n' => '\n',
                't' => '\t',
                'r' => '\r',
                'b' => '\u{8}',
                'f' => '\u{c}',
                '0' => '\0',
                'u' => {
                    let hex = self
                        .rest()
                        .get(..4)
                        .ok_or_else(|| self.error(LiteralProblem::ShortUnicodeEscape))?;
                    let code = u32::from_str_radix(hex, 16)
                        .map_err(|error| self.error(LiteralProblem::UnicodeEscapeHex(error)))?;
                    self.at += 4;
                    char::from_u32(code)
                        .ok_or_else(|| self.error(LiteralProblem::UnicodeEscapeScalar { code }))?
                }
                other => other,
            });
        }
    }

    fn number(&mut self) -> Result<Value, WorkflowMetaError> {
        let length = self
            .rest()
            .find(|c: char| !(c.is_ascii_digit() || matches!(c, '-' | '+' | '.' | 'e' | 'E')))
            .unwrap_or(self.rest().len());
        let text = &self.rest()[..length];
        let value = if let Ok(integer) = text.parse::<i64>() {
            Value::Number(integer.into())
        } else {
            let float: f64 = text
                .parse()
                .map_err(|error| self.error(LiteralProblem::Number(error)))?;
            Value::Number(
                Number::from_f64(float)
                    .ok_or_else(|| self.error(LiteralProblem::NonFiniteNumber))?,
            )
        };
        self.at += length;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_script_text(script: &str) -> Result<ParsedScript, String> {
        parse_script(script).map_err(|e| e.to_string())
    }

    #[test]
    fn a_literal_meta_parses_and_the_body_declares_it() {
        let script = "// review\nexport const meta = {\n  name: 'review',\n  description: \"Find bugs\",\n  phases: [{ title: 'Scan' }, 'Fix',],\n};\nreturn 1;";
        assert_eq!(
            parse_script_text(script),
            Ok(ParsedScript {
                meta: WorkflowMeta {
                    name: "review".to_owned(),
                    description: "Find bugs".to_owned(),
                    phases: vec!["Scan".to_owned(), "Fix".to_owned()],
                },
                body: "const meta = {\"name\":\"review\",\"description\":\"Find bugs\",\"phases\":[{\"title\":\"Scan\"},\"Fix\"]};\nreturn 1;".to_owned(),
            })
        );
    }

    #[test]
    fn a_call_or_identifier_is_not_a_literal() {
        assert_eq!(
            parse_script_text("export const meta = { name: makeName(), description: 'd', phases: [] };"),
            Err("meta must be a pure literal: an identifier or call is not a literal at `(), description: 'd', ph`".to_owned())
        );
        assert_eq!(
            parse_script_text("export const meta = { name: `a${x}`, description: 'd', phases: [] };"),
            Err("meta must be a pure literal: a template substitution is not a literal at `{x}`, description: 'd', `".to_owned())
        );
    }

    #[test]
    fn a_missing_field_or_meta_is_rejected() {
        assert_eq!(
            parse_script_text("export const meta = { name: 'a', phases: [] };"),
            Err("meta.description must be a non-empty string".to_owned())
        );
        assert_eq!(
            parse_script_text("return 1;"),
            Err(
                "a workflow script starts with `export const meta = { name, description, phases }`"
                    .to_owned()
            )
        );
    }
}
