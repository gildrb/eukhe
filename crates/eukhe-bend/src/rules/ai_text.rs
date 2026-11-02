//! Texts the eukhe-ai providers read (`bend/ai_text.bend`, entry
//! `bend/ffi_ai_text.bend`; `laws/ai_text.bend`): a Gemini id's major
//! version, an API version in a URL path, a base64 data URL, and the event
//! boundaries and lines of a server-sent event stream. Each is an explicit
//! rule stated in plain words in the laws.

use crate::wire::{Reader, Writer, STR_MAX};
use crate::{call, expect_core, Entry, Error};

/// The digits of a Gemini id's major version: the run of ASCII digits
/// after a leading `gemini-` or `gemini-live-`.
#[must_use]
pub fn gemini_major(id: &str) -> Option<String> {
    let mut request = Writer::new();
    request.tag(0).str(wire_text(id));
    expect_core(Entry::AiText, maybe_str(&mut request))
}

/// Whether one `/`-separated part of `text` is an API version: `v`, one or
/// more digits, then nothing or `beta` and any digits.
#[must_use]
pub fn api_version(text: &str) -> bool {
    let mut request = Writer::new();
    request.tag(1).str(wire_text(text));
    expect_core(Entry::AiText, bool_answer(&mut request))
}

/// A base64 data URL (`data:<mime>;base64,<data>`, a mime without `;`, data
/// without a line terminator): its mime and data.
#[must_use]
pub fn data_url(text: &str) -> Option<(&str, &str)> {
    let mut request = Writer::new();
    let chunks = chunks(text);
    request.tag(2).count(chunks.len());
    for chunk in chunks {
        request.str(chunk);
    }
    let mime_chars = expect_core(Entry::AiText, maybe_nat(&mut request))?;
    let body = text.strip_prefix("data:")?;
    let mime_end = char_offset(body, mime_chars)?;
    let data = body[mime_end..].strip_prefix(";base64,")?;
    Some((&body[..mime_end], data))
}

/// The first event boundary of an event-stream `buffer` (a line break,
/// `\r\n` else `\r` or `\n`, right after another): its byte range.
#[must_use]
pub fn event_boundary(buffer: &str) -> Option<std::ops::Range<usize>> {
    let mut request = Writer::new();
    request.tag(3).str(wire_text(buffer));
    let (start, len) = expect_core(Entry::AiText, maybe_span(&mut request))?;
    let begin = char_offset(buffer, start)?;
    let end = begin + char_offset(&buffer[begin..], len)?;
    Some(begin..end)
}

/// `raw` split at each line break (`\r\n` as one, else `\r` or `\n`).
#[must_use]
pub fn lines(raw: &str) -> Vec<String> {
    let mut request = Writer::new();
    request.tag(4).str(wire_text(raw));
    expect_core(Entry::AiText, strs_answer(&mut request))
}

/// The byte offset of char `n` of `text` (its length at `n` = the char
/// count).
fn char_offset(text: &str, n: u64) -> Option<usize> {
    let n = usize::try_from(n).ok()?;
    text.char_indices()
        .map(|(at, _)| at)
        .chain(std::iter::once(text.len()))
        .nth(n)
}

fn reply(request: &mut Writer) -> Result<String, Error> {
    Ok(call(Entry::AiText, &request.finish()?)?)
}

fn maybe_str(request: &mut Writer) -> Result<Option<String>, Error> {
    let reply = reply(request)?;
    let mut reader = Reader::reply(&reply)?;
    let found = if reader.maybe()? {
        Some(reader.str()?.to_owned())
    } else {
        None
    };
    reader.end()?;
    Ok(found)
}

fn bool_answer(request: &mut Writer) -> Result<bool, Error> {
    let reply = reply(request)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = reader.bool()?;
    reader.end()?;
    Ok(verdict)
}

fn maybe_nat(request: &mut Writer) -> Result<Option<u64>, Error> {
    let reply = reply(request)?;
    let mut reader = Reader::reply(&reply)?;
    let found = if reader.maybe()? {
        Some(reader.nat()?)
    } else {
        None
    };
    reader.end()?;
    Ok(found)
}

fn maybe_span(request: &mut Writer) -> Result<Option<(u64, u64)>, Error> {
    let reply = reply(request)?;
    let mut reader = Reader::reply(&reply)?;
    let found = if reader.maybe()? {
        Some((reader.nat()?, reader.nat()?))
    } else {
        None
    };
    reader.end()?;
    Ok(found)
}

fn strs_answer(request: &mut Writer) -> Result<Vec<String>, Error> {
    let reply = reply(request)?;
    let mut reader = Reader::reply(&reply)?;
    let n = reader.count()?;
    let texts = (0..n)
        .map(|_| reader.str().map(str::to_owned))
        .collect::<Result<Vec<_>, _>>()?;
    reader.end()?;
    Ok(texts)
}

/// `text` cut into runs of at most [`STR_MAX`] chars, in order.
fn chunks(text: &str) -> Vec<&str> {
    let mut chunks = Vec::new();
    let mut rest = text;
    while let Some((end, _)) = rest.char_indices().nth(STR_MAX) {
        chunks.push(&rest[..end]);
        rest = &rest[end..];
    }
    if !rest.is_empty() {
        chunks.push(rest);
    }
    chunks
}

/// A text as the wire carries it: its first [`STR_MAX`] chars.
fn wire_text(text: &str) -> &str {
    text.char_indices()
        .nth(STR_MAX)
        .map_or(text, |(end, _)| &text[..end])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_core_reads_versions_and_data_urls() {
        assert_eq!(
            [
                gemini_major("gemini-2.5-pro"),
                gemini_major("gemini-live-3x"),
                gemini_major("gemini-x")
            ],
            [Some("2".to_owned()), Some("3".to_owned()), None]
        );
        assert_eq!(
            [
                api_version("/v1beta/models"),
                api_version("/v1beta2"),
                api_version("/vbeta"),
                api_version("/v1x/")
            ],
            [true, true, false, false]
        );
        assert_eq!(
            data_url("data:image/png;base64,QUJD"),
            Some(("image/png", "QUJD"))
        );
        assert_eq!(data_url("data:é;base64,QQ"), Some(("é", "QQ")));
        assert_eq!(data_url("data:;base64,QQ"), None);
        assert_eq!(data_url("data:a;base64,Q\nQ"), None);
    }

    #[test]
    fn the_core_splits_event_streams() {
        assert_eq!(event_boundary("é\n\r\nb"), Some(2..5));
        assert_eq!(event_boundary("a\r\n"), None);
        assert_eq!(event_boundary("a\r\n\r"), Some(1..4));
        assert_eq!(lines("a\r\nb\rc\n"), ["a", "b", "c", ""]);
        assert_eq!(lines(""), [""]);
    }
}
