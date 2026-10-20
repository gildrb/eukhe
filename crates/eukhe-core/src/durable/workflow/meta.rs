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

/// Split `script` into its meta and body.
///
/// # Errors
///
/// The script does not start with `export const meta = { ... }` (comments
/// and blank lines may come first), the literal is not pure, or it lacks a
/// string `name`, a string `description`, or a `phases` array of
/// `{ title }` objects or strings.
pub(crate) fn parse_script(script: &str) -> Result<ParsedScript, String> {
    let start = skip_trivia(script, 0);
    if !script[start..].starts_with(META_PREFIX) {
        return Err(
            "a workflow script starts with `export const meta = { name, description, phases }`"
                .to_owned(),
        );
    }
    let mut parser = Parser {
        text: script,
        at: start + META_PREFIX.len(),
    };
    parser.trivia();
    if !parser.eat('=') {
        return Err("`export const meta` must be assigned a literal".to_owned());
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

fn meta_of(value: &Value) -> Result<WorkflowMeta, String> {
    let Value::Object(object) = value else {
        return Err("meta must be an object".to_owned());
    };
    let text = |key: &str| match object.get(key) {
        Some(Value::String(text)) if !text.trim().is_empty() => Ok(text.trim().to_owned()),
        Some(_) | None => Err(format!("meta.{key} must be a non-empty string")),
    };
    let name = text("name")?;
    let description = text("description")?;
    let Some(Value::Array(items)) = object.get("phases") else {
        return Err("meta.phases must be an array".to_owned());
    };
    let phases = items
        .iter()
        .map(|item| match item {
            Value::String(title) => Ok(title.clone()),
            Value::Object(phase) => match phase.get("title") {
                Some(Value::String(title)) => Ok(title.clone()),
                Some(_) | None => Err("each meta.phases item needs a string title".to_owned()),
            },
            Value::Null | Value::Bool(_) | Value::Number(_) | Value::Array(_) => {
                Err("each meta.phases item is { title } or a string".to_owned())
            }
        })
        .collect::<Result<Vec<String>, String>>()?;
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

    fn error(&self, what: &str) -> String {
        let shown: String = self.rest().chars().take(24).collect();
        format!("meta must be a pure literal: {what} at `{shown}`")
    }

    fn value(&mut self) -> Result<Value, String> {
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
                    _ => Err(self.error("an identifier or call is not a literal")),
                }
            }
            None => Err(self.error("the literal ends early")),
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

    fn object(&mut self) -> Result<Value, String> {
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
                Some(_) | None => return Err(self.error("expected a key")),
            };
            self.trivia();
            if !self.eat(':') {
                return Err(self.error("expected `:`"));
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
            return Err(self.error("expected `,` or `}`"));
        }
    }

    fn array(&mut self) -> Result<Value, String> {
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
            return Err(self.error("expected `,` or `]`"));
        }
    }

    fn string(&mut self, quote: char) -> Result<String, String> {
        self.eat(quote);
        let mut out = String::new();
        loop {
            let Some(c) = self.peek() else {
                return Err(self.error("unterminated string"));
            };
            self.at += c.len_utf8();
            if c == quote {
                return Ok(out);
            }
            if quote == '`' && c == '$' && self.peek() == Some('{') {
                return Err(self.error("a template substitution is not a literal"));
            }
            if c != '\\' {
                out.push(c);
                continue;
            }
            let Some(escaped) = self.peek() else {
                return Err(self.error("unterminated string"));
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
                    let hex = self.rest().get(..4).ok_or_else(|| self.error("bad \\u"))?;
                    let code =
                        u32::from_str_radix(hex, 16).map_err(|_| self.error("bad \\u escape"))?;
                    self.at += 4;
                    char::from_u32(code).ok_or_else(|| self.error("bad \\u escape"))?
                }
                other => other,
            });
        }
    }

    fn number(&mut self) -> Result<Value, String> {
        let length = self
            .rest()
            .find(|c: char| !(c.is_ascii_digit() || matches!(c, '-' | '+' | '.' | 'e' | 'E')))
            .unwrap_or(self.rest().len());
        let text = &self.rest()[..length];
        let value = if let Ok(integer) = text.parse::<i64>() {
            Value::Number(integer.into())
        } else {
            let float: f64 = text.parse().map_err(|_| self.error("bad number"))?;
            Value::Number(Number::from_f64(float).ok_or_else(|| self.error("bad number"))?)
        };
        self.at += length;
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_literal_meta_parses_and_the_body_declares_it() {
        let script = "// review\nexport const meta = {\n  name: 'review',\n  description: \"Find bugs\",\n  phases: [{ title: 'Scan' }, 'Fix',],\n};\nreturn 1;";
        assert_eq!(
            parse_script(script),
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
            parse_script("export const meta = { name: makeName(), description: 'd', phases: [] };"),
            Err("meta must be a pure literal: an identifier or call is not a literal at `(), description: 'd', ph`".to_owned())
        );
        assert_eq!(
            parse_script("export const meta = { name: `a${x}`, description: 'd', phases: [] };"),
            Err("meta must be a pure literal: a template substitution is not a literal at `{x}`, description: 'd', `".to_owned())
        );
    }

    #[test]
    fn a_missing_field_or_meta_is_rejected() {
        assert_eq!(
            parse_script("export const meta = { name: 'a', phases: [] };"),
            Err("meta.description must be a non-empty string".to_owned())
        );
        assert_eq!(
            parse_script("return 1;"),
            Err(
                "a workflow script starts with `export const meta = { name, description, phases }`"
                    .to_owned()
            )
        );
    }
}
