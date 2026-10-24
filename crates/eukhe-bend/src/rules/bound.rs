//! The bounder of a tool's output (`bend/bound.bend`, entry
//! `bend/ffi_bound.bend`; `laws/bound.bend`, docs/runtime.md S2): which
//! bytes of an output a cap keeps (whole lines from the start or the end,
//! else the first line cut at a character boundary), what it counts as
//! dropped, what a streaming output stores, and the truncation notice.
//! Rust reads the text into what the core decides on (each line's bytes,
//! whether the text ends inside a line, and the character boundaries at
//! the cap's byte limit) and moves the bytes the reply names.
//!
//! The opt-out (no cap) keeps every byte: nothing here runs for it.

use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error, Stepper};

/// A cap: at most `bytes` bytes in at most `lines` lines, from the start of
/// the output or (`tail`) from its end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cap {
    pub bytes: usize,
    pub lines: usize,
    pub tail: bool,
}

/// The window of a whole text: the bytes `from..to` it keeps, and the
/// bytes and lines it drops.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Slice {
    pub from: usize,
    pub to: usize,
    pub dropped_bytes: usize,
    pub dropped_lines: usize,
}

/// The window of `text` under `cap` (`slice`).
#[must_use]
pub fn slice(text: &str, cap: Cap) -> Slice {
    expect_core(Entry::Bound, slice_call(text, cap))
}

fn slice_call(text: &str, cap: Cap) -> Result<Slice, Error> {
    let mut request = Writer::new();
    request.count(8 + lines_of(text));
    request.nat(0);
    write_cap(&mut request, cap);
    write_body(&mut request, text, cap.bytes);
    let reply = nats(&call(Entry::Bound, &request.finish()?)?)?;
    let [from, to, dropped_bytes, dropped_lines] = sizes(&reply, "a window of a text")?;
    let (from, to) = span(text, from, to)?;
    Ok(Slice {
        from,
        to,
        dropped_bytes,
        dropped_lines,
    })
}

/// Where a truncation notice says the output was cut.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum At {
    /// A head cap kept the start.
    End,
    /// A tail cap kept the end.
    Start,
}

/// The truncation notice of an output that dropped `dropped` bytes under
/// a head or (`tail`) a tail cap, while the result still holds that output
/// (`still`): `None` when there is none (`notice`).
#[must_use]
pub fn notice(tail: bool, dropped: u64, still: bool) -> Option<At> {
    expect_core(Entry::Bound, notice_call(tail, dropped, still))
}

fn notice_call(tail: bool, dropped: u64, still: bool) -> Result<Option<At>, Error> {
    let mut request = Writer::new();
    request
        .count(4)
        .nat(1)
        .nat(bit(tail))
        .nat(dropped.min(NAT_MAX))
        .nat(bit(still));
    match nats(&call(Entry::Bound, &request.finish()?)?)?[..] {
        [] => Ok(None),
        [0] => Ok(Some(At::End)),
        [1] => Ok(Some(At::Start)),
        _ => Err(malformed("a notice").into()),
    }
}

/// What to do with a text of a streaming output (`Act`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Act {
    /// Drop it: the head window is full.
    Drop,
    /// Store it.
    Store,
    /// Store it, then [`Stream::look`] at the stored text and trim it.
    Trim,
}

/// What [`Stream::look`] reads of the stored text: the bytes `from..to` of
/// it in the window, the bytes and lines the whole output dropped, and
/// where the stored text now starts (`cut`: the bytes before it go).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Look {
    pub from: usize,
    pub to: usize,
    pub dropped_bytes: usize,
    pub dropped_lines: usize,
    pub cut: usize,
}

/// One streaming output under a cap, its state in the compiled core.
#[derive(Debug)]
pub struct Stream {
    core: Stepper,
    cap: Cap,
    skips: bool,
}

impl Stream {
    /// A new output under `cap`: nothing came, nothing is stored.
    #[must_use]
    pub fn open(cap: Cap) -> Stream {
        expect_core(Entry::Bound, Self::open_call(cap))
    }

    fn open_call(cap: Cap) -> Result<Stream, Error> {
        let mut request = Writer::new();
        request.count(3);
        write_cap(&mut request, cap);
        let (core, reply) = Stepper::open(Entry::Bound, &request.finish()?)?;
        let skips = flag(&nats(&reply)?, "whether it takes skips")?;
        Ok(Stream { core, cap, skips })
    }

    /// Whether it takes the output a shell left out (a tail does).
    #[must_use]
    pub fn takes_skips(&self) -> bool {
        self.skips
    }

    /// A text of `bytes` bytes and `newlines` newlines comes, after which
    /// the output ends inside a line or not (`open`) (`out`).
    #[must_use]
    pub fn out(&mut self, bytes: usize, newlines: usize, open: bool) -> Act {
        expect_core(Entry::Bound, self.out_call(bytes, newlines, open))
    }

    fn out_call(&mut self, bytes: usize, newlines: usize, open: bool) -> Result<Act, Error> {
        let mut request = Writer::new();
        request
            .count(4)
            .nat(0)
            .nat(saturate(bytes))
            .nat(saturate(newlines))
            .nat(bit(open));
        match nats(&self.core.step(&request.finish()?)?)?[..] {
            [0] => Ok(Act::Drop),
            [1] => Ok(Act::Store),
            [2] => Ok(Act::Trim),
            _ => Err(malformed("what to do with a text").into()),
        }
    }

    /// A shell left out `bytes` bytes of `newlines` newlines, after which
    /// the output ends inside a line or not (`open`); `true`: clear the
    /// stored text (`skip`).
    #[must_use]
    pub fn skip(&mut self, bytes: u64, newlines: u64, open: bool) -> bool {
        expect_core(Entry::Bound, self.skip_call(bytes, newlines, open))
    }

    fn skip_call(&mut self, bytes: u64, newlines: u64, open: bool) -> Result<bool, Error> {
        let mut request = Writer::new();
        request
            .count(4)
            .nat(1)
            .nat(bytes.min(NAT_MAX))
            .nat(newlines.min(NAT_MAX))
            .nat(bit(open));
        let reply = nats(&self.core.step(&request.finish()?)?)?;
        Ok(flag(&reply, "whether to clear")?)
    }

    /// The window of the whole output, read from the text it stores
    /// (`look`).
    #[must_use]
    pub fn look(&mut self, stored: &str) -> Look {
        expect_core(Entry::Bound, self.look_call(stored))
    }

    fn look_call(&mut self, stored: &str) -> Result<Look, Error> {
        let mut request = Writer::new();
        request.count(5 + lines_of(stored));
        request.nat(2);
        write_body(&mut request, stored, self.cap.bytes);
        let reply = nats(&self.core.step(&request.finish()?)?)?;
        let [from, to, dropped_bytes, dropped_lines, cut] = sizes(&reply, "a look")?;
        let (from, to) = span(stored, from, to)?;
        if !stored.is_char_boundary(cut) {
            return Err(malformed("a cut of the stored text").into());
        }
        Ok(Look {
            from,
            to,
            dropped_bytes,
            dropped_lines,
            cut,
        })
    }
}

/// A count on the wire: a text past [`NAT_MAX`] bytes (100 TB) cannot be
/// in memory, so the bound never changes a decision.
fn saturate(n: usize) -> u64 {
    u64::try_from(n).map_or(NAT_MAX, |n| n.min(NAT_MAX))
}

fn bit(b: bool) -> u64 {
    u64::from(b)
}

fn write_cap(request: &mut Writer, cap: Cap) {
    request
        .nat(saturate(cap.bytes))
        .nat(saturate(cap.lines))
        .nat(bit(cap.tail));
}

/// The lines of `text`: each ends after its newline, and the last one
/// without when the text does not end with one.
fn lines_of(text: &str) -> usize {
    text.split_inclusive('\n').count()
}

/// The body of `text` (`Body`): whether it ends inside a line, the bytes
/// of its longest start and of its longest end within `bytes`, of its
/// shortest end past them (all of it when it is not longer), then each
/// line's bytes.
fn write_body(request: &mut Writer, text: &str, bytes: usize) {
    let all = text.as_bytes();
    let len = all.len();
    let open = !text.is_empty() && !text.ends_with('\n');
    let head = character_end(all, bytes.min(len));
    let tail = len - character_start(all, len.saturating_sub(bytes));
    let margin = if len > bytes {
        len - character_end(all, len - bytes - 1)
    } else {
        len
    };
    request
        .nat(bit(open))
        .nat(saturate(head))
        .nat(saturate(tail))
        .nat(saturate(margin));
    for line in text.split_inclusive('\n') {
        request.nat(saturate(line.len()));
    }
}

/// The last character boundary at or before `index`.
fn character_end(bytes: &[u8], index: usize) -> usize {
    let mut end = index;
    while end > 0 && (bytes.get(end).copied().unwrap_or(0) & 0xc0) == 0x80 {
        end -= 1;
    }
    end
}

/// The first character boundary at or after `index`.
fn character_start(bytes: &[u8], index: usize) -> usize {
    let mut start = index;
    while start < bytes.len() && (bytes[start] & 0xc0) == 0x80 {
        start += 1;
    }
    start
}

/// A reply that is not the list the request answers; the decoder read
/// the list whole, so no offset in it is wrong.
fn malformed(expected: &'static str) -> WireError {
    WireError::Malformed { at: 0, expected }
}

/// The list of Nats a reply is, whole.
fn nats(reply: &str) -> Result<Vec<u64>, WireError> {
    let mut reader = Reader::reply(reply)?;
    let xs = (0..reader.count()?)
        .map(|_| reader.nat())
        .collect::<Result<Vec<u64>, WireError>>()?;
    reader.end()?;
    Ok(xs)
}

/// A reply of exactly N byte counts.
fn sizes<const N: usize>(xs: &[u64], expected: &'static str) -> Result<[usize; N], WireError> {
    let xs: &[u64; N] = xs.try_into().map_err(|_| malformed(expected))?;
    let mut out = [0; N];
    for (to, &x) in out.iter_mut().zip(xs) {
        *to = usize::try_from(x).map_err(|_| malformed(expected))?;
    }
    Ok(out)
}

/// A reply of one Bool (0 or 1).
fn flag(xs: &[u64], expected: &'static str) -> Result<bool, WireError> {
    match xs {
        [0] => Ok(false),
        [1] => Ok(true),
        _ => Err(malformed(expected)),
    }
}

/// The window `from..to` of `text`, at character boundaries.
fn span(text: &str, from: usize, to: usize) -> Result<(usize, usize), WireError> {
    if from <= to && text.get(from..to).is_some() {
        Ok((from, to))
    } else {
        Err(malformed("a window of the text"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each decision comes from the compiled core: a head and a tail
    /// window of a whole text, a notice, and a tail stream that stores,
    /// trims and reads its window.
    #[test]
    fn the_bounder_decisions_come_from_the_compiled_core() {
        let head = Cap {
            bytes: 5,
            lines: 10,
            tail: false,
        };
        let tail = Cap { tail: true, ..head };
        let mut stream = Stream::open(tail);
        let acts = [stream.out(3, 1, false), stream.out(30, 0, true)];
        assert_eq!(
            (
                slice("ab\ncde\n", head),
                slice("ab\ncde\n", tail),
                notice(true, 4, true),
                notice(false, 4, false),
                stream.takes_skips(),
                acts,
                stream.look(&format!("ab\n{}", "x".repeat(30))),
            ),
            (
                Slice {
                    from: 0,
                    to: 3,
                    dropped_bytes: 4,
                    dropped_lines: 1
                },
                Slice {
                    from: 3,
                    to: 7,
                    dropped_bytes: 3,
                    dropped_lines: 1
                },
                Some(At::Start),
                None,
                true,
                [Act::Store, Act::Trim],
                Look {
                    from: 28,
                    to: 33,
                    dropped_bytes: 28,
                    dropped_lines: 1,
                    cut: 27
                },
            )
        );
    }
}
