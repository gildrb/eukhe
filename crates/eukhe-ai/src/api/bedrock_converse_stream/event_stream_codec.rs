//! The AWS `vnd.amazon.eventstream` binary framing of Bedrock responses:
//! `getChunkedStream` (message reassembly from body chunks) and
//! `EventStreamCodec.decode` (`splitMessage` with its CRC-32 checks plus
//! `HeaderMarshaller.parse`) of `@smithy/core/event-streams`, with the same
//! error texts.

// Decode failures are the thrown JS `Error`s (`ErrorObject`); cold path.
#![allow(clippy::result_large_err)]

use eukhe_types::pi_ai::IndexMap;

use crate::utils::diagnostics::ErrorObject;

const PRELUDE_MEMBER_LENGTH: usize = 4;
const PRELUDE_LENGTH: usize = PRELUDE_MEMBER_LENGTH * 2;
const CHECKSUM_LENGTH: usize = 4;
const MINIMUM_MESSAGE_LENGTH: usize = PRELUDE_LENGTH + CHECKSUM_LENGTH * 2;

/// V8's `DataView` bounds error.
const OUT_OF_BOUNDS: &str = "Offset is outside the bounds of the DataView";

/// One event-stream header value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum HeaderValue {
    Bool(bool),
    Byte(i8),
    Short(i16),
    Integer(i32),
    Long(i64),
    Binary(Vec<u8>),
    String(String),
    /// Milliseconds since the epoch.
    Timestamp(i64),
    Uuid(String),
}

impl HeaderValue {
    /// JS `String(header.value)` (timestamps as their epoch milliseconds).
    pub(crate) fn to_js_string(&self) -> String {
        match self {
            Self::Bool(value) => value.to_string(),
            Self::Byte(value) => value.to_string(),
            Self::Short(value) => value.to_string(),
            Self::Integer(value) => value.to_string(),
            Self::Long(value) | Self::Timestamp(value) => value.to_string(),
            Self::Binary(bytes) => bytes
                .iter()
                .map(u8::to_string)
                .collect::<Vec<_>>()
                .join(","),
            Self::String(value) | Self::Uuid(value) => value.clone(),
        }
    }
}

/// A decoded message: headers (a later duplicate replaces an earlier one, as
/// in the SDK's header object) and the body bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct EventMessage {
    pub(crate) headers: IndexMap<String, HeaderValue>,
    pub(crate) body: Vec<u8>,
}

fn range_error() -> ErrorObject {
    ErrorObject::named("RangeError", OUT_OF_BOUNDS)
}

/// `getChunkedStream`: reassembles whole messages from response body chunks
/// by their length prelude.
#[derive(Default)]
pub(crate) struct MessageChunker {
    length_buffer: Vec<u8>,
    message: Option<Vec<u8>>,
    total_length: usize,
}

impl MessageChunker {
    /// Feed one body chunk: the messages it completes, in order; a framing
    /// failure ends the list (and the stream).
    pub(crate) fn push(&mut self, chunk: &[u8]) -> Vec<Result<Vec<u8>, ErrorObject>> {
        let mut out = Vec::new();
        let mut offset = 0;
        while offset < chunk.len() {
            if self.message.is_none() {
                let wanted = 4 - self.length_buffer.len();
                let take = wanted.min(chunk.len() - offset);
                self.length_buffer
                    .extend_from_slice(&chunk[offset..offset + take]);
                offset += take;
                if self.length_buffer.len() < 4 {
                    break;
                }
                let prefix = [
                    self.length_buffer[0],
                    self.length_buffer[1],
                    self.length_buffer[2],
                    self.length_buffer[3],
                ];
                let size = u32::from_be_bytes(prefix) as usize;
                self.length_buffer.clear();
                if size < 4 {
                    // `new DataView(new Uint8Array(size).buffer).setUint32(0, …)`.
                    out.push(Err(range_error()));
                    return out;
                }
                let mut message = Vec::with_capacity(size);
                message.extend_from_slice(&prefix);
                self.message = Some(message);
                self.total_length = size;
            }
            let Some(message) = self.message.as_mut() else {
                break;
            };
            let take = (self.total_length - message.len()).min(chunk.len() - offset);
            message.extend_from_slice(&chunk[offset..offset + take]);
            offset += take;
            if message.len() == self.total_length {
                out.push(Ok(std::mem::take(message)));
                self.message = None;
                self.total_length = 0;
            }
        }
        out
    }

    /// The end of the body: an incomplete message is a truncation.
    pub(crate) fn finish(&self) -> Result<(), ErrorObject> {
        match &self.message {
            Some(message) if message.len() != self.total_length => {
                Err(ErrorObject::new("Truncated event message received."))
            }
            Some(_) | None => Ok(()),
        }
    }
}

fn read_u32(bytes: &[u8], at: usize) -> u32 {
    u32::from_be_bytes([bytes[at], bytes[at + 1], bytes[at + 2], bytes[at + 3]])
}

/// `EventStreamCodec.decode`.
pub(crate) fn decode_message(message: &[u8]) -> Result<EventMessage, ErrorObject> {
    let byte_length = message.len();
    if byte_length < MINIMUM_MESSAGE_LENGTH {
        return Err(ErrorObject::new(
            "Provided message too short to accommodate event stream message overhead",
        ));
    }
    let message_length = read_u32(message, 0) as usize;
    if byte_length != message_length {
        return Err(ErrorObject::new(
            "Reported message length does not match received message length",
        ));
    }
    let header_length = read_u32(message, PRELUDE_MEMBER_LENGTH) as usize;
    let expected_prelude_checksum = read_u32(message, PRELUDE_LENGTH);
    let expected_message_checksum = read_u32(message, byte_length - CHECKSUM_LENGTH);
    let mut hasher = crc32fast::Hasher::new();
    hasher.update(&message[..PRELUDE_LENGTH]);
    let prelude_checksum = hasher.clone().finalize();
    if expected_prelude_checksum != prelude_checksum {
        return Err(ErrorObject::new(format!(
            "The prelude checksum specified in the message ({expected_prelude_checksum}) does not match the calculated CRC32 checksum ({prelude_checksum})"
        )));
    }
    hasher.update(&message[PRELUDE_LENGTH..byte_length - CHECKSUM_LENGTH]);
    let message_checksum = hasher.finalize();
    if expected_message_checksum != message_checksum {
        return Err(ErrorObject::new(format!(
            "The message checksum ({message_checksum}) did not match the expected value of {expected_message_checksum}"
        )));
    }
    let headers_start = PRELUDE_LENGTH + CHECKSUM_LENGTH;
    let body_length = message_length
        .checked_sub(header_length + PRELUDE_LENGTH + CHECKSUM_LENGTH + CHECKSUM_LENGTH)
        .ok_or_else(|| ErrorObject::named("RangeError", "Invalid typed array length"))?;
    let headers = message
        .get(headers_start..headers_start + header_length)
        .ok_or_else(range_error)?;
    let body = message
        .get(headers_start + header_length..headers_start + header_length + body_length)
        .ok_or_else(range_error)?;
    Ok(EventMessage {
        headers: parse_headers(headers)?,
        body: body.to_vec(),
    })
}

/// A bounds-checked reader over the header section.
struct HeaderReader<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl HeaderReader<'_> {
    fn take(&mut self, length: usize) -> Result<&[u8], ErrorObject> {
        let slice = self
            .bytes
            .get(self.position..self.position + length)
            .ok_or_else(range_error)?;
        self.position += length;
        Ok(slice)
    }

    fn u8(&mut self) -> Result<u8, ErrorObject> {
        Ok(self.take(1)?[0])
    }

    fn u16(&mut self) -> Result<u16, ErrorObject> {
        let bytes = self.take(2)?;
        Ok(u16::from_be_bytes([bytes[0], bytes[1]]))
    }

    fn i64(&mut self) -> Result<i64, ErrorObject> {
        let bytes = self.take(8)?;
        let mut array = [0u8; 8];
        array.copy_from_slice(bytes);
        Ok(i64::from_be_bytes(array))
    }
}

/// `HeaderMarshaller.parse`.
fn parse_headers(bytes: &[u8]) -> Result<IndexMap<String, HeaderValue>, ErrorObject> {
    let mut out = IndexMap::new();
    let mut reader = HeaderReader { bytes, position: 0 };
    while reader.position < bytes.len() {
        let name_length = usize::from(reader.u8()?);
        let name = String::from_utf8_lossy(reader.take(name_length)?).into_owned();
        let value = match reader.u8()? {
            0 => HeaderValue::Bool(true),
            1 => HeaderValue::Bool(false),
            2 => HeaderValue::Byte(i8::from_be_bytes([reader.u8()?])),
            3 => {
                let value = reader.take(2)?;
                HeaderValue::Short(i16::from_be_bytes([value[0], value[1]]))
            }
            4 => {
                let value = reader.take(4)?;
                HeaderValue::Integer(i32::from_be_bytes([value[0], value[1], value[2], value[3]]))
            }
            5 => HeaderValue::Long(reader.i64()?),
            6 => {
                let length = usize::from(reader.u16()?);
                HeaderValue::Binary(reader.take(length)?.to_vec())
            }
            7 => {
                let length = usize::from(reader.u16()?);
                HeaderValue::String(String::from_utf8_lossy(reader.take(length)?).into_owned())
            }
            8 => HeaderValue::Timestamp(reader.i64()?),
            9 => {
                let uuid = hex::encode(reader.take(16)?);
                HeaderValue::Uuid(format!(
                    "{}-{}-{}-{}-{}",
                    &uuid[..8],
                    &uuid[8..12],
                    &uuid[12..16],
                    &uuid[16..20],
                    &uuid[20..]
                ))
            }
            _ => return Err(ErrorObject::new("Unrecognized header type tag")),
        };
        out.insert(name, value);
    }
    Ok(out)
}

/// `EventStreamCodec.encode` for string headers: frames one message (used by
/// tests and mock servers).
#[cfg(test)]
pub(crate) fn encode_message(headers: &[(&str, &str)], body: &[u8]) -> Vec<u8> {
    let mut header_bytes = Vec::new();
    for (name, value) in headers {
        header_bytes.push(u8::try_from(name.len()).unwrap_or(u8::MAX));
        header_bytes.extend_from_slice(name.as_bytes());
        header_bytes.push(7);
        header_bytes
            .extend_from_slice(&u16::try_from(value.len()).unwrap_or(u16::MAX).to_be_bytes());
        header_bytes.extend_from_slice(value.as_bytes());
    }
    let length = header_bytes.len() + body.len() + 16;
    let mut out = Vec::with_capacity(length);
    out.extend_from_slice(&u32::try_from(length).unwrap_or(u32::MAX).to_be_bytes());
    out.extend_from_slice(
        &u32::try_from(header_bytes.len())
            .unwrap_or(u32::MAX)
            .to_be_bytes(),
    );
    let prelude_crc = crc32fast::hash(&out);
    out.extend_from_slice(&prelude_crc.to_be_bytes());
    out.extend_from_slice(&header_bytes);
    out.extend_from_slice(body);
    let message_crc = crc32fast::hash(&out);
    out.extend_from_slice(&message_crc.to_be_bytes());
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn event(body: &str) -> Vec<u8> {
        encode_message(
            &[(":message-type", "event"), (":event-type", "messageStart")],
            body.as_bytes(),
        )
    }

    #[test]
    fn reassembles_messages_split_across_chunks() {
        let first = event(r#"{"role":"assistant"}"#);
        let second = event("{}");
        let mut bytes = first.clone();
        bytes.extend_from_slice(&second);
        let mut chunker = MessageChunker::default();
        let mut messages = Vec::new();
        for chunk in bytes.chunks(3) {
            messages.extend(chunker.push(chunk));
        }
        assert_eq!(messages, vec![Ok(first.clone()), Ok(second)]);
        assert_eq!(chunker.finish(), Ok(()));
        let decoded = decode_message(&first).expect("decodes");
        assert_eq!(
            decoded.headers.get(":event-type"),
            Some(&HeaderValue::String("messageStart".into()))
        );
        assert_eq!(decoded.body, br#"{"role":"assistant"}"#);
    }

    #[test]
    fn reports_truncation_at_the_end_of_the_body() {
        let message = event("{}");
        let mut chunker = MessageChunker::default();
        assert!(chunker.push(&message[..message.len() - 3]).is_empty());
        assert_eq!(
            chunker.finish(),
            Err(ErrorObject::new("Truncated event message received."))
        );
    }

    #[test]
    fn verifies_the_message_checksum_like_the_sdk() {
        let mut message = event(r#"{"role":"assistant"}"#);
        let last = message.len() - 1;
        message[last] ^= 0xff;
        let expected = read_u32(&message, message.len() - 4);
        let actual = crc32fast::hash(&message[..message.len() - 4]);
        assert_eq!(
            decode_message(&message),
            Err(ErrorObject::new(format!(
                "The message checksum ({actual}) did not match the expected value of {expected}"
            )))
        );
    }
}
