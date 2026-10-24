//! The gate of one host-request frame of a kernel's stream
//! (`bend/sandbox.bend` `admit`, entry `bend/ffi_frames.bend`;
//! `laws/sandbox.bend`): a repeated id, a frame past the limit, a frame
//! with no type or of a type the host does not serve is refused, the rest
//! is served. The caller cuts the stream and reads each frame's facts;
//! [`admit`] encodes them, calls [`Entry::Frames`] and decodes the
//! verdict.

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// Whether a frame's id was seen before on the stream.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Id {
    Fresh,
    Seen,
}

/// How long a frame is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Length {
    /// The whole frame, in bytes.
    Bytes(usize),
    /// Past the limit: the stream cut it there.
    PastLimit,
}

/// A frame's request type, as the host reads it (`Sb.Typed`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Typed {
    /// No type (or not a string, or empty).
    Unnamed,
    /// A type the host serves.
    Served,
    /// A type the host does not serve.
    NotServed,
}

/// The gate's verdict on a host-request frame (`Sb.Verdict`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Serve,
    Duplicate,
    Oversize,
    Kindless,
    NotServed,
}

/// The verdict on a host-request frame under the limit `max` (bytes).
#[must_use]
pub fn admit(max: usize, id: Id, length: Length, typed: Typed) -> Verdict {
    expect_core(Entry::Frames, admit_call(max, id, length, typed))
}

fn admit_call(max: usize, id: Id, length: Length, typed: Typed) -> Result<Verdict, Error> {
    let mut request = Writer::new();
    request
        .count(max)
        .bool(id == Id::Fresh)
        .count(match length {
            Length::Bytes(bytes) => bytes,
            Length::PastLimit => max.saturating_add(1),
        });
    match typed {
        Typed::Unnamed => request.tag(0),
        Typed::Served => request.tag(1).bool(true),
        Typed::NotServed => request.tag(1).bool(false),
    };
    let reply = call(Entry::Frames, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = match reader.tag_of(5, "a frame's verdict")? {
        0 => Verdict::Serve,
        1 => Verdict::Duplicate,
        2 => Verdict::Oversize,
        3 => Verdict::Kindless,
        // `tag_of` answers a tag below 5: this is 4.
        _ => Verdict::NotServed,
    };
    reader.end()?;
    Ok(verdict)
}

#[cfg(test)]
mod tests {
    use super::{admit, Id, Length, Typed, Verdict};

    #[test]
    fn the_codec_carries_each_frame_through_the_core() {
        assert_eq!(
            [
                admit(100, Id::Fresh, Length::Bytes(100), Typed::Served),
                admit(100, Id::Seen, Length::Bytes(10), Typed::Served),
                admit(100, Id::Fresh, Length::PastLimit, Typed::Unnamed),
                admit(100, Id::Fresh, Length::Bytes(10), Typed::Unnamed),
                admit(100, Id::Fresh, Length::Bytes(10), Typed::NotServed),
            ],
            [
                Verdict::Serve,
                Verdict::Duplicate,
                Verdict::Oversize,
                Verdict::Kindless,
                Verdict::NotServed,
            ]
        );
    }
}
