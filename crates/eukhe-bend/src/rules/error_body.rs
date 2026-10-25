//! What a provider's HTTP error shows its user (`bend/error_body.bend`,
//! entry `bend/ffi_error_body.bend`; `laws/error_body.bend`): the body,
//! the first usable one of the three places an SDK keeps it, trimmed as JS
//! trims, none when empty and cut to 4000 UTF-16 code units; the display
//! string of the status, the body, the message and a provider's prefix;
//! and the cut of a text to a cap.

use crate::wire::{Reader, Writer, NAT_MAX, STR_MAX};
use crate::{call, expect_core, Entry, Error};

/// What one place of a provider error holds, as the core reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Probe<'a> {
    /// Nothing there, or a value that is neither a JSON string nor a plain
    /// JSON object with a key (a number, an empty object, a stream, an
    /// instance).
    Nothing,
    /// A JSON string.
    Text(&'a str),
    /// A plain JSON object with at least one key, serialized.
    Object(&'a str),
}

/// What the display string is made of.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shown<'a> {
    /// The message already carries the body (no body: it does).
    pub carried: bool,
    /// The HTTP status, rendered as JS renders the JSON number.
    pub status: Option<&'a str>,
    pub body: Option<&'a str>,
    /// The provider's prefix (`OpenAI API error`).
    pub prefix: Option<&'a str>,
    pub message: &'a str,
}

/// A text as the wire carries it: its first [`STR_MAX`] chars.
fn wire_text(text: &str) -> &str {
    text.char_indices()
        .nth(STR_MAX)
        .map_or(text, |(end, _)| &text[..end])
}

fn put_text(writer: &mut Writer, text: Option<&str>) {
    match text {
        Some(text) => {
            writer.some().str(wire_text(text));
        }
        None => {
            writer.none();
        }
    }
}

fn put_probe(writer: &mut Writer, probe: Probe<'_>) {
    match probe {
        Probe::Nothing => {
            writer.tag(0);
        }
        Probe::Text(text) => {
            writer.tag(1).str(wire_text(text));
        }
        Probe::Object(text) => {
            writer.tag(2).str(wire_text(text));
        }
    }
}

fn ask<T>(
    request: &mut Writer,
    read: impl FnOnce(&mut Reader<'_>) -> Result<T, Error>,
) -> Result<T, Error> {
    let reply = call(Entry::ErrorBody, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let answer = read(&mut reader)?;
    reader.end()?;
    Ok(answer)
}

/// The body of a provider error whose places hold `body` (Mistral's
/// `body`), `error` (`openai`'s parsed `error`) and `response`
/// (Bedrock's `$response.body`).
#[must_use]
pub fn body(body: Probe<'_>, error: Probe<'_>, response: Probe<'_>) -> Option<String> {
    let mut request = Writer::new();
    request.tag(0);
    put_probe(&mut request, body);
    put_probe(&mut request, error);
    put_probe(&mut request, response);
    expect_core(
        Entry::ErrorBody,
        ask(&mut request, |reader| {
            Ok(if reader.maybe()? {
                Some(reader.str()?.to_owned())
            } else {
                None
            })
        }),
    )
}

/// The display string of a provider error.
#[must_use]
pub fn show(parts: &Shown<'_>) -> String {
    let mut request = Writer::new();
    request.tag(1).bool(parts.carried);
    put_text(&mut request, parts.status);
    put_text(&mut request, parts.body);
    put_text(&mut request, parts.prefix);
    request.str(wire_text(parts.message));
    expect_core(
        Entry::ErrorBody,
        ask(&mut request, |reader| Ok(reader.str()?.to_owned())),
    )
}

/// `text` cut to `cap` UTF-16 code units, with a marker that counts the
/// units cut.
#[must_use]
pub fn truncate(text: &str, cap: usize) -> String {
    let mut request = Writer::new();
    request
        .tag(2)
        .str(wire_text(text))
        .nat(u64::try_from(cap).map_or(NAT_MAX, |cap| cap.min(NAT_MAX)));
    expect_core(
        Entry::ErrorBody,
        ask(&mut request, |reader| Ok(reader.str()?.to_owned())),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The body, its trim and its cap, and the display string come from
    /// the compiled core.
    #[test]
    fn the_core_shows_the_error() {
        assert_eq!(
            (
                body(
                    Probe::Object("{\"x\":1}"),
                    Probe::Object(" {\"error\":\"waf\"} "),
                    Probe::Nothing,
                ),
                show(&Shown {
                    carried: false,
                    status: Some("403"),
                    body: Some("{\"error\":\"waf\"}"),
                    prefix: Some("OpenAI API error"),
                    message: "403 status code (no body)",
                }),
                truncate("abcdef", 3),
            ),
            (
                Some("{\"error\":\"waf\"}".to_owned()),
                "OpenAI API error (403): {\"error\":\"waf\"}".to_owned(),
                "abc... [truncated 3 chars]".to_owned(),
            )
        );
    }
}
