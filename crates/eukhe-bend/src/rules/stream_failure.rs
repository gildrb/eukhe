//! The cause of a failed provider stream and the message a user reads for
//! it (`bend/stream_failure.bend`, entry `bend/ffi_stream_failure.bend`;
//! `laws/stream_failure.bend`): the cause from the provider's error type
//! (searched lowered by `bend/text_pat.bend`) and the HTTP status, the
//! message that names the cause, the type, the status, the provider's
//! short message and the request id, and the failures of streams that
//! ended without their terminal marker, went silent or repeated.

use eukhe_types::pi_ai::StreamFailureKind;

use crate::wire::{Reader, WireError, Writer, NAT_MAX, STR_MAX};
use crate::{call, expect_core, Entry, Error};

/// The content block a dropped stream was inside.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Block {
    Thinking,
    Text,
    ToolCall,
    /// No block had opened yet.
    None,
}

/// What a message names besides its cause.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Qualified<'a> {
    pub kind: StreamFailureKind,
    pub provider_error_type: Option<&'a str>,
    pub status: Option<u16>,
    pub detail: Option<&'a str>,
    pub request_id: Option<&'a str>,
}

/// The facts of an HTTP error the cause comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HttpFacts<'a> {
    pub message: &'a str,
    pub status: Option<u16>,
    /// The body's `error.type` (or `code`).
    pub body_type: Option<&'a str>,
    /// The body's `error.message`.
    pub body_message: Option<&'a str>,
    /// The error's own wire code.
    pub code: Option<&'a str>,
    /// The SDK's error class name.
    pub sdk_name: Option<&'a str>,
    pub request_id: Option<&'a str>,
}

/// The cause of an HTTP error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HttpCause {
    pub kind: StreamFailureKind,
    pub provider_error_type: Option<String>,
    /// The user's message; `None` when the cause is unknown and the raw
    /// message stays.
    pub message: Option<String>,
}

const fn kind_tag(kind: StreamFailureKind) -> u32 {
    match kind {
        StreamFailureKind::Refusal => 0,
        StreamFailureKind::Safety => 1,
        StreamFailureKind::PaymentRequired => 2,
        StreamFailureKind::Overloaded => 3,
        StreamFailureKind::RateLimit => 4,
        StreamFailureKind::ServerError => 5,
        StreamFailureKind::Auth => 6,
        StreamFailureKind::Permission => 7,
        StreamFailureKind::InvalidRequest => 8,
        StreamFailureKind::MalformedResponse => 9,
        StreamFailureKind::StreamDrop => 10,
        StreamFailureKind::StreamStalled => 11,
        StreamFailureKind::StreamRepeating => 12,
        StreamFailureKind::Unknown => 13,
    }
}

const KINDS: [StreamFailureKind; 14] = [
    StreamFailureKind::Refusal,
    StreamFailureKind::Safety,
    StreamFailureKind::PaymentRequired,
    StreamFailureKind::Overloaded,
    StreamFailureKind::RateLimit,
    StreamFailureKind::ServerError,
    StreamFailureKind::Auth,
    StreamFailureKind::Permission,
    StreamFailureKind::InvalidRequest,
    StreamFailureKind::MalformedResponse,
    StreamFailureKind::StreamDrop,
    StreamFailureKind::StreamStalled,
    StreamFailureKind::StreamRepeating,
    StreamFailureKind::Unknown,
];

fn read_kind(reader: &mut Reader<'_>) -> Result<StreamFailureKind, Error> {
    let tag = reader.tag_of(14, "a stream failure kind")?;
    Ok(
        KINDS[usize::try_from(tag).map_err(|_| WireError::Malformed {
            at: 0,
            expected: "a stream failure kind",
        })?],
    )
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

fn put_status(writer: &mut Writer, status: Option<u16>) {
    match status {
        Some(status) => {
            writer.some().nat(u64::from(status));
        }
        None => {
            writer.none();
        }
    }
}

fn read_text(reader: &mut Reader<'_>) -> Result<Option<String>, Error> {
    Ok(if reader.maybe()? {
        Some(reader.str()?.to_owned())
    } else {
        None
    })
}

fn ask<T>(
    request: &mut Writer,
    read: impl FnOnce(&mut Reader<'_>) -> Result<T, Error>,
) -> Result<T, Error> {
    let reply = call(Entry::StreamFailure, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let answer = read(&mut reader)?;
    reader.end()?;
    Ok(answer)
}

fn text_reply(request: &mut Writer) -> Result<String, Error> {
    ask(request, |reader| Ok(reader.str()?.to_owned()))
}

/// The cause of a failure of the provider error type (when there is none,
/// the text the caller gives instead) and the HTTP status.
#[must_use]
pub fn classify(provider_error_type: Option<&str>, status: Option<u16>) -> StreamFailureKind {
    let mut request = Writer::new();
    request.tag(0);
    put_text(&mut request, provider_error_type);
    put_status(&mut request, status);
    expect_core(Entry::StreamFailure, ask(&mut request, read_kind))
}

/// The user's message: `Provider overloaded (overloaded_error, 529):
/// <detail> [request_id: <id>]`.
#[must_use]
pub fn message(parts: &Qualified<'_>) -> String {
    let mut request = Writer::new();
    request.tag(1).tag(kind_tag(parts.kind));
    put_text(&mut request, parts.provider_error_type);
    put_status(&mut request, parts.status);
    put_text(&mut request, parts.detail);
    put_text(&mut request, parts.request_id);
    expect_core(Entry::StreamFailure, text_reply(&mut request))
}

/// The cause, provider error type and message of an HTTP error.
#[must_use]
pub fn http(facts: &HttpFacts<'_>) -> HttpCause {
    let mut request = Writer::new();
    request.tag(2).str(wire_text(facts.message));
    put_status(&mut request, facts.status);
    put_text(&mut request, facts.body_type);
    put_text(&mut request, facts.body_message);
    put_text(&mut request, facts.code);
    put_text(&mut request, facts.sdk_name);
    put_text(&mut request, facts.request_id);
    expect_core(
        Entry::StreamFailure,
        ask(&mut request, |reader| {
            Ok(HttpCause {
                kind: read_kind(reader)?,
                provider_error_type: read_text(reader)?,
                message: read_text(reader)?,
            })
        }),
    )
}

/// The cause and message of a stream that ended with the provider stop
/// reason `raw` (None: none) that maps to an error.
#[must_use]
pub fn from_stop(raw: Option<&str>, request_id: Option<&str>) -> (StreamFailureKind, String) {
    let mut request = Writer::new();
    request.tag(3);
    put_text(&mut request, raw);
    put_text(&mut request, request_id);
    expect_core(
        Entry::StreamFailure,
        ask(&mut request, |reader| {
            Ok((read_kind(reader)?, reader.str()?.to_owned()))
        }),
    )
}

/// The message of a stream the provider ended inside `block` without its
/// terminal marker.
#[must_use]
pub fn dropped(block: Block) -> String {
    let tag = match block {
        Block::Thinking => 0,
        Block::Text => 1,
        Block::ToolCall => 2,
        Block::None => 3,
    };
    let mut request = Writer::new();
    request.tag(4).tag(tag);
    expect_core(Entry::StreamFailure, text_reply(&mut request))
}

/// The message of a stream with no event for `idle_ms` (the deadline as
/// the host writes it).
#[must_use]
pub fn stalled(idle_ms: &str) -> String {
    let mut request = Writer::new();
    request.tag(5).str(wire_text(idle_ms));
    expect_core(Entry::StreamFailure, text_reply(&mut request))
}

/// A repeated line as a message shows it: its first 80 chars and `…` when
/// it is longer.
#[must_use]
pub fn shown(line: &str) -> String {
    let mut request = Writer::new();
    request.tag(6).str(wire_text(line));
    expect_core(Entry::StreamFailure, text_reply(&mut request))
}

/// The message of a stream whose last `limit` lines repeat with a period
/// of `period` lines, `quoted` the shown line quoted, and the period it
/// records (at least 1).
#[must_use]
pub fn repeating(limit: u32, period: u32, quoted: &str) -> (String, u32) {
    let mut request = Writer::new();
    request
        .tag(7)
        .nat(u64::from(limit))
        .nat(u64::from(period))
        .str(wire_text(quoted));
    expect_core(
        Entry::StreamFailure,
        ask(&mut request, |reader| {
            Ok((reader.str()?.to_owned(), reader.u32()?))
        }),
    )
}

/// `NAT_MAX` bounds every number this entry sends: statuses and counts are
/// `u16` and `u32`.
const _: () = assert!(u32::MAX as u64 <= NAT_MAX);

#[cfg(test)]
mod tests {
    use super::*;

    /// The causes and messages come from the compiled core: a 402 before
    /// its type, a lowered type, a message with every qualifier, an HTTP
    /// error whose class name stands in for the type.
    #[test]
    fn the_core_names_the_failure() {
        assert_eq!(
            (
                classify(Some("invalid_request_error"), Some(402)),
                classify(Some("Content-Filter"), None),
                message(&Qualified {
                    kind: StreamFailureKind::Overloaded,
                    provider_error_type: Some("overloaded_error"),
                    status: Some(529),
                    detail: Some("slow down"),
                    request_id: Some("req_abc"),
                }),
                http(&HttpFacts {
                    message: "429 x",
                    status: Some(429),
                    body_type: None,
                    body_message: Some("slow"),
                    code: None,
                    sdk_name: Some("ApiError"),
                    request_id: None,
                }),
            ),
            (
                StreamFailureKind::PaymentRequired,
                StreamFailureKind::Safety,
                "Provider overloaded (overloaded_error, 529): slow down [request_id: req_abc]"
                    .to_owned(),
                HttpCause {
                    kind: StreamFailureKind::RateLimit,
                    provider_error_type: Some("ApiError".to_owned()),
                    message: Some("Provider rate limit exceeded (ApiError, 429): slow".to_owned()),
                },
            )
        );
    }
}
