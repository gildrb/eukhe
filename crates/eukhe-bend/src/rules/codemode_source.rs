//! What a code mode tool input is (`bend/codemode_source.bend`, entry
//! `bend/ffi_codemode_source.bend`; `laws/codemode_source.bend`): a
//! script, a script after a first-line options directive with the options
//! it sets, or a refusal and its text. The caller gives the input's text
//! facts ([`Facts`]): whether it is blank, which lines after the first are
//! options lines, whether the text from the first newline on is blank, and
//! the first line's directive as `serde_json` reads it, each field's value as
//! a JS safe non-negative integer or not one. The core decides every
//! refusal and its text, which options line is misplaced and its number,
//! the JS `Object.keys` order of the keys, and the options set.

use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, Entry, Error};

/// A directive field's value (`Src.Num`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Num {
    /// A JS safe non-negative integer (`Number.isSafeInteger(v) && v >= 0`).
    Safe(u64),
    /// Any other value.
    NotSafe,
}

/// A field of the directive's object (`Src.Field`).
#[derive(Clone, Copy, Debug)]
pub struct Field<'a> {
    /// Its key.
    pub key: &'a str,
    /// Its value.
    pub value: Num,
}

/// What `serde_json` reads from the directive (`Src.Json`).
#[derive(Clone, Copy, Debug)]
pub enum Json<'a> {
    /// Invalid JSON: `serde_json`'s error text.
    Invalid(&'a str),
    /// A value that is no object.
    NotObject,
    /// An object's fields, in order.
    Object(&'a [Field<'a>]),
}

/// The first line's directive: the text after `// @options:`, trimmed
/// (`Src.Dir`).
#[derive(Clone, Copy, Debug)]
pub struct Directive<'a> {
    /// The text is empty.
    pub empty: bool,
    /// What `serde_json` reads from it.
    pub json: Json<'a>,
}

/// The text facts of an input (`Src.Facts`).
#[derive(Clone, Copy, Debug)]
pub struct Facts<'a> {
    /// The input is blank (Rust `trim`).
    pub blank: bool,
    /// The 0-based numbers of the lines after the first whose text after
    /// leading white space starts with `// @options:`, in order.
    pub options_lines: &'a [u64],
    /// The text from the first newline on is blank (no newline: blank).
    pub rest_blank: bool,
    /// The first line's directive, when the first line is an options line.
    pub directive: Option<Directive<'a>>,
}

/// What an input is (`Src.Answer`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Answer {
    /// Refused, with the text the script's caller gets.
    Refused(String),
    /// The whole input is the script; no options.
    Plain,
    /// The script is the text from the first newline on; the options are
    /// the given `max_output_tokens` and `timeout_ms`, when set.
    Split {
        /// `max_output_tokens`.
        max_output_tokens: Option<u64>,
        /// `timeout_ms`.
        timeout_ms: Option<u64>,
    },
}

/// What the input with `facts` is (`Src.parse`).
///
/// # Errors
///
/// [`Error::Wire`] when a key or `serde_json`'s text is past
/// [`crate::wire::STR_MAX`] chars; else only from an inconsistent build
/// (see [`crate::expect_core`]).
pub fn parse(facts: &Facts<'_>) -> Result<Answer, Error> {
    let mut request = Writer::new();
    request.bool(facts.blank).count(facts.options_lines.len());
    for &line in facts.options_lines {
        request.nat(line);
    }
    request.bool(facts.rest_blank);
    let mut fields: &[Field<'_>] = &[];
    match facts.directive {
        None => {
            request.none();
        }
        Some(directive) => {
            request.some().bool(directive.empty);
            match directive.json {
                Json::Invalid(text) => {
                    request.tag(0).str(text);
                }
                Json::NotObject => {
                    request.tag(1);
                }
                Json::Object(object) => {
                    fields = object;
                    request.tag(2).count(object.len());
                    for field in object {
                        request.str(field.key);
                        match field.value {
                            Num::NotSafe => request.tag(0),
                            Num::Safe(n) => request.tag(1).nat(n.min(NAT_MAX)),
                        };
                    }
                }
            }
        }
    }
    let reply = call(Entry::CodemodeSource, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let answer = match reply.tag_of(3, "an answer")? {
        0 => Answer::Refused(reply.str()?.to_owned()),
        1 => Answer::Plain,
        _ => {
            let tokens = reply.bool()?;
            let timeout = reply.bool()?;
            Answer::Split {
                max_output_tokens: taken(fields, tokens, "max_output_tokens")?,
                timeout_ms: taken(fields, timeout, "timeout_ms")?,
            }
        }
    };
    reply.end()?;
    Ok(answer)
}

/// The value of the first field named `key`, when the core set it: the
/// integer the caller gave (unsaturated).
fn taken(fields: &[Field<'_>], set: bool, key: &str) -> Result<Option<u64>, WireError> {
    if !set {
        return Ok(None);
    }
    match fields.iter().find(|field| field.key == key) {
        Some(Field {
            value: Num::Safe(n),
            ..
        }) => Ok(Some(*n)),
        Some(Field {
            value: Num::NotSafe,
            ..
        })
        | None => Err(WireError::Malformed {
            at: 0,
            expected: "an option set from a safe integer",
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::{parse, Answer, Directive, Facts, Field, Json, Num};

    #[test]
    fn the_codec_carries_the_facts_through_the_core() {
        let fields = [
            Field {
                key: "max_output_tokens",
                value: Num::Safe(9_007_199_254_740_991),
            },
            Field {
                key: "timeout_ms",
                value: Num::Safe(30_000),
            },
        ];
        let facts = Facts {
            blank: false,
            options_lines: &[],
            rest_blank: false,
            directive: Some(Directive {
                empty: false,
                json: Json::Object(&fields),
            }),
        };
        assert_eq!(
            parse(&facts).unwrap(),
            Answer::Split {
                max_output_tokens: Some(9_007_199_254_740_991),
                timeout_ms: Some(30_000),
            }
        );
        let misplaced = Facts {
            options_lines: &[2],
            ..facts
        };
        assert_eq!(
            parse(&misplaced).unwrap(),
            Answer::Refused(
                "The // @options: line must be the first line of the input; found one on line 3"
                    .to_owned()
            )
        );
    }
}
