//! The pasted authorization input of the localhost-callback logins
//! (`bend/redirect_input.bend`, entry `bend/ffi_redirect_input.bend`;
//! `laws/redirect_input.bend`): the cleaned paste, the code and state it
//! carries (query values percent-decoded as `form_urlencoded` does), the
//! state check, and the user-facing texts of the paste loop. Rust sends the
//! text and reads the answer.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// Why a paste cannot complete the login.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fail {
    /// The input carries no authorization code.
    MissingCode,
    /// The echoed state is not the login's.
    StateMismatch,
    /// The authorization server answered an OAuth error (`error=`).
    Provider {
        error: String,
        description: Option<String>,
    },
}

/// A paste's code and the state it echoes (none when it carries none).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Pasted {
    pub code: String,
    pub state: Option<String>,
}

/// The question tags of the entry.
const CLEAN: u32 = 0;
const PARSE: u32 = 1;
const VERIFY: u32 = 2;
const TEXT: u32 = 3;
const NOTICE: u32 = 4;

/// One pasted token as typed: whitespace and zero-width chars dropped
/// anywhere, then wrapping quotes, backticks or angle brackets trimmed.
#[must_use]
pub fn clean(text: &str) -> String {
    expect_core(Entry::RedirectInput, text_call(CLEAN, text))
}

/// The code and state of a pasted callback address, query string,
/// `code#state` pair or bare code.
///
/// # Errors
///
/// No code ([`Fail::MissingCode`]) or an OAuth error ([`Fail::Provider`]).
pub fn parse(text: &str) -> Result<Pasted, Fail> {
    expect_core(Entry::RedirectInput, parse_call(text))
}

/// A paste's state checked against the login's own: a paste without one
/// takes the login's.
///
/// # Errors
///
/// [`Fail::StateMismatch`] when the paste echoes another state.
pub fn verify(code: &str, state: Option<&str>, expected: &str) -> Result<(String, String), Fail> {
    expect_core(Entry::RedirectInput, verify_call(code, state, expected))
}

/// The user-facing text of a failure.
#[must_use]
pub fn text(fail: &Fail) -> String {
    expect_core(Entry::RedirectInput, fail_text_call(fail))
}

/// The notice of a failed token exchange: the reason, then the two ways
/// forward.
#[must_use]
pub fn notice(error: &str) -> String {
    expect_core(Entry::RedirectInput, text_call(NOTICE, error))
}

fn text_call(tag: u32, text: &str) -> Result<String, Error> {
    let reply = call(
        Entry::RedirectInput,
        &Writer::new().tag(tag).str(text).finish()?,
    )?;
    let mut reader = Reader::reply(&reply)?;
    let answer = reader.str()?.to_string();
    reader.end()?;
    Ok(answer)
}

fn parse_call(text: &str) -> Result<Result<Pasted, Fail>, Error> {
    let reply = call(
        Entry::RedirectInput,
        &Writer::new().tag(PARSE).str(text).finish()?,
    )?;
    read_answer(&reply)
}

fn verify_call(
    code: &str,
    state: Option<&str>,
    expected: &str,
) -> Result<Result<(String, String), Fail>, Error> {
    let mut writer = Writer::new();
    writer.tag(VERIFY).str(code);
    match state {
        Some(state) => writer.some().str(state),
        None => writer.none(),
    };
    let reply = call(Entry::RedirectInput, &writer.str(expected).finish()?)?;
    Ok(match read_answer(&reply)? {
        Ok(Pasted {
            code,
            state: Some(state),
        }) => Ok((code, state)),
        Ok(Pasted { state: None, .. }) => {
            return Err(WireError::Malformed {
                at: 0,
                expected: "a verified state",
            }
            .into())
        }
        Err(fail) => Err(fail),
    })
}

fn fail_text_call(fail: &Fail) -> Result<String, Error> {
    let mut writer = Writer::new();
    writer.tag(TEXT);
    match fail {
        Fail::MissingCode => writer.tag(0),
        Fail::StateMismatch => writer.tag(1),
        Fail::Provider { error, description } => {
            writer.tag(2).str(error);
            match description {
                Some(description) => writer.some().str(description),
                None => writer.none(),
            }
        }
    };
    let reply = call(Entry::RedirectInput, &writer.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let text = reader.str()?.to_string();
    reader.end()?;
    Ok(text)
}

fn read_answer(reply: &str) -> Result<Result<Pasted, Fail>, Error> {
    let mut reader = Reader::reply(reply)?;
    let answer = if reader.tag_of(2, "a paste answer")? == 0 {
        Ok(Pasted {
            code: reader.str()?.to_string(),
            state: maybe_str(&mut reader)?,
        })
    } else {
        Err(match reader.tag_of(3, "a paste failure")? {
            0 => Fail::MissingCode,
            1 => Fail::StateMismatch,
            // `tag_of` answers a tag below 3: this is 2.
            _ => Fail::Provider {
                error: reader.str()?.to_string(),
                description: maybe_str(&mut reader)?,
            },
        })
    };
    reader.end()?;
    Ok(answer)
}

fn maybe_str(reader: &mut Reader<'_>) -> Result<Option<String>, WireError> {
    Ok(if reader.maybe()? {
        Some(reader.str()?.to_string())
    } else {
        None
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The answers come from the compiled core: a wrapped address with a
    /// percent-encoded code, an OAuth error, the state check and a notice.
    #[test]
    fn the_core_reads_a_pasted_redirect() {
        assert_eq!(
            parse(" \"http://localhost:1/cb?code=a%2Bb%20c&state=s\"\n"),
            Ok(Pasted {
                code: "a+b c".to_string(),
                state: Some("s".to_string()),
            })
        );
        assert_eq!(
            parse("error=access_denied&error_description=no+way"),
            Err(Fail::Provider {
                error: "access_denied".to_string(),
                description: Some("no way".to_string()),
            })
        );
        assert_eq!(verify("c", Some("s"), "t"), Err(Fail::StateMismatch));
        assert_eq!(
            verify("c", None, "t"),
            Ok(("c".to_string(), "t".to_string()))
        );
        assert_eq!(
            notice(" 400. "),
            "Login did not complete: 400. Paste the address again, or open the login link again and sign in."
        );
    }
}
