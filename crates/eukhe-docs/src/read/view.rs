//! What a read of a file shows: one call of the compiled Bend core
//! (`bend/ffi_doc_rows.bend`, model `bend/doc_rows.bend`, laws
//! `laws/doc_rows.bend`). Rust sends the facts about the bytes, the
//! selector and the projection of the text ([`Projection`]); the core
//! answers whether the read goes on, the lines it counts, the spans it
//! shows, the notices and whether it gets a tag. `read/mod.rs` writes the
//! rows of those spans.

use eukhe_bend::wire::{Reader, WireError, Writer, NAT_MAX};
use eukhe_bend::{expect_core, Entry};

use super::selector::{LineRange, Selector};
use crate::text::Projection;

/// Whether a read goes on (model `Gate`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Gate {
    Go,
    NotUtf8,
    Binary,
}

/// Lines `start..=end` (from 1) shown; `gap`: a gap marker comes before
/// them (model `Span`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Span {
    pub(super) start: usize,
    pub(super) end: usize,
    pub(super) gap: bool,
}

/// A notice of a read (model `Note`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Note {
    /// A window starts past the end, at this line.
    Beyond { line: u64 },
    /// `count` lines remain, from line `next`.
    Remain { count: u64, next: u64 },
    /// A range starts past the end.
    RangeBeyond { start: u64, end: Option<u64> },
    /// Over the size limit: no tag.
    TooBig,
}

/// What a read shows (model `View`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct View {
    /// The lines the read counts.
    pub(super) total: usize,
    pub(super) raw: bool,
    pub(super) spans: Vec<Span>,
    pub(super) notes: Vec<Note>,
    /// The read records the text and shows its tag.
    pub(super) tag: bool,
}

/// One call of `bend/ffi_doc_rows.bend`.
fn call(request: &mut Writer) -> String {
    let request = expect_core(Entry::DocRows, request.finish());
    expect_core(Entry::DocRows, eukhe_bend::call(Entry::DocRows, &request))
}

/// What a read knows of the bytes before it shows them.
#[expect(
    clippy::struct_excessive_bools,
    reason = "the four facts the gate reads (model `gate`), each a yes or no"
)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Facts {
    /// The selector is raw.
    pub(super) raw: bool,
    /// The bytes are UTF-8.
    pub(super) utf8: bool,
    /// They start with a UTF-16 BOM.
    pub(super) utf16: bool,
    /// The sniffed head has a NUL byte.
    pub(super) nul: bool,
}

/// Whether a read goes on.
pub(super) fn gate(facts: Facts) -> Gate {
    let mut request = Writer::new();
    request
        .tag(0)
        .bool(facts.raw)
        .bool(facts.utf8)
        .bool(facts.utf16)
        .bool(facts.nul);
    let reply = call(&mut request);
    expect_core(Entry::DocRows, read_gate(&reply))
}

fn read_gate(reply: &str) -> Result<Gate, WireError> {
    let mut reader = Reader::reply(reply)?;
    let gate = match reader.tag_of(3, "a read gate")? {
        0 => Gate::Go,
        1 => Gate::NotUtf8,
        _ => Gate::Binary,
    };
    reader.end()?;
    Ok(gate)
}

/// A line number on the wire: past the wire's bound no file has the line,
/// so the bound stands for it.
fn line(request: &mut Writer, n: u64) {
    request.nat(n.min(NAT_MAX));
}

fn put_range(request: &mut Writer, range: &LineRange) {
    line(request, range.start_line);
    match range.end_line {
        Some(end) => {
            request.some();
            line(request, end);
        }
        None => {
            request.none();
        }
    }
}

/// What a read of the text `lines` shows: `utf8` the bytes are UTF-8,
/// `over` the file is over the size limit of a tag.
pub(super) fn view(selector: &Selector, utf8: bool, over: bool, lines: &Projection<'_>) -> View {
    let mut request = Writer::new();
    request.tag(1);
    match selector {
        Selector::Whole => {
            request.tag(0);
        }
        Selector::Raw => {
            request.tag(1);
        }
        Selector::Lines { ranges, raw } => {
            request.tag(2).count(ranges.len());
            for range in ranges {
                put_range(&mut request, range);
            }
            request.bool(*raw);
        }
    }
    request.bool(utf8).bool(over);
    lines.put(&mut request);
    let reply = call(&mut request);
    expect_core(Entry::DocRows, read_view(&reply))
}

fn read_note(reader: &mut Reader<'_>) -> Result<Note, WireError> {
    Ok(match reader.tag_of(4, "a read notice")? {
        0 => Note::Beyond {
            line: reader.nat()?,
        },
        1 => Note::Remain {
            count: reader.nat()?,
            next: reader.nat()?,
        },
        2 => Note::RangeBeyond {
            start: reader.nat()?,
            end: if reader.maybe()? {
                Some(reader.nat()?)
            } else {
                None
            },
        },
        _ => Note::TooBig,
    })
}

fn read_view(reply: &str) -> Result<View, WireError> {
    let mut reader = Reader::reply(reply)?;
    let total = reader.count()?;
    let raw = reader.bool()?;
    let spans = (0..reader.count()?)
        .map(|_| {
            Ok(Span {
                start: reader.count()?,
                end: reader.count()?,
                gap: reader.bool()?,
            })
        })
        .collect::<Result<Vec<_>, WireError>>()?;
    let notes = (0..reader.count()?)
        .map(|_| read_note(&mut reader))
        .collect::<Result<Vec<_>, WireError>>()?;
    let tag = reader.bool()?;
    reader.end()?;
    Ok(View {
        total,
        raw,
        spans,
        notes,
        tag,
    })
}

/// The lines a read of the text numbers (the edit anchors of a whole read).
pub(crate) fn line_count(lines: &Projection<'_>) -> usize {
    view(&Selector::Whole, true, false, lines).total
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The gate and a view reach the compiled core: a UTF-16 file is
    /// refused; a read at 4-5 of a 9-line file shows 3-8 and the notice of
    /// line 9.
    #[test]
    fn gate_and_view_reach_the_core() {
        let utf16 = Facts {
            raw: false,
            utf8: false,
            utf16: true,
            nul: false,
        };
        assert_eq!(gate(utf16), Gate::NotUtf8);
        let text = "1\n2\n3\n4\n5\n6\n7\n8\n9\n";
        let range = LineRange {
            start_line: 4,
            end_line: Some(5),
        };
        let selector = Selector::Lines {
            ranges: vec![range],
            raw: false,
        };
        assert_eq!(
            view(&selector, true, false, &Projection::of(text)),
            View {
                total: 9,
                raw: false,
                spans: vec![Span {
                    start: 3,
                    end: 8,
                    gap: false
                }],
                notes: vec![Note::Remain { count: 1, next: 9 }],
                tag: true
            }
        );
    }
}
