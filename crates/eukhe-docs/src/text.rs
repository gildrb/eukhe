//! Line endings and the byte order mark: a file is edited as LF text without a
//! BOM and written back with both restored.
//!
//! Rust scans a text into its [`Projection`] (model `proj` of
//! `bend/doc_lines.bend`, laws in `laws/doc_lines.bend` and
//! `laws/doc_rows.bend`): the BOM flag and each line (each piece between
//! `\n` bytes) with its own ending. Every decision over the lines runs in
//! the compiled Bend core on that projection: the carry of a loaded file
//! and what a whole-file write keeps here (`bend/ffi_doc_lines.bend`), the
//! separators of an edit in `hashline/endings.rs`, what a read shows in
//! `read/view.rs`. This module only scans and joins bytes.

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{expect_core, Entry};

/// Line-ending style of a file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LineEnding {
    Lf,
    CrLf,
}

impl LineEnding {
    /// The bytes of the ending.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Lf => "\n",
            Self::CrLf => "\r\n",
        }
    }

    /// The wire tag of the ending (model `End`: `Lf` 0, `CrLf` 1).
    pub(crate) fn tag(self) -> u32 {
        match self {
            Self::Lf => 0,
            Self::CrLf => 1,
        }
    }

    /// The ending a wire tag names.
    pub(crate) fn read(reader: &mut Reader<'_>) -> Result<Self, WireError> {
        // tag_of answers 0 or 1.
        Ok(if reader.tag_of(2, "a line ending")? == 0 {
            Self::Lf
        } else {
            Self::CrLf
        })
    }
}

/// The UTF-8 byte order mark.
pub const BOM: &str = "\u{FEFF}";

/// One line of a text: its chars without the ending, and its own ending
/// (`None`: the last piece, after the last `\n`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Line<'a> {
    pub text: &'a str,
    pub end: Option<LineEnding>,
}

/// The projection of a text (model `Proj`): whether it starts with a BOM,
/// and its lines. A `\n` ends a line; a `\r` right before it makes the
/// ending CRLF; a lone `\r` is content. The last piece has no ending.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Projection<'a> {
    pub bom: bool,
    pub lines: Vec<Line<'a>>,
}

impl<'a> Projection<'a> {
    /// Scan `content`.
    #[must_use]
    pub fn of(content: &'a str) -> Self {
        let (bom, body) = match content.strip_prefix(BOM) {
            Some(body) => (true, body),
            None => (false, content),
        };
        let mut lines = Vec::new();
        let mut rest = body;
        while let Some(at) = rest.find('\n') {
            let piece = &rest[..at];
            lines.push(match piece.strip_suffix('\r') {
                Some(text) => Line {
                    text,
                    end: Some(LineEnding::CrLf),
                },
                None => Line {
                    text: piece,
                    end: Some(LineEnding::Lf),
                },
            });
            rest = &rest[at + 1..];
        }
        lines.push(Line {
            text: rest,
            end: None,
        });
        Projection { bom, lines }
    }

    /// The BOM to write back: the mark when the text had one.
    #[must_use]
    pub fn bom(&self) -> &'static str {
        if self.bom {
            BOM
        } else {
            ""
        }
    }

    /// The text without its BOM, each line ending made `\n`.
    #[must_use]
    pub fn lf_text(&self) -> String {
        let mut out =
            String::with_capacity(self.lines.iter().map(|line| line.text.len() + 1).sum());
        for (at, line) in self.lines.iter().enumerate() {
            if at > 0 {
                out.push('\n');
            }
            out.push_str(line.text);
        }
        out
    }

    /// The ending of each line that has one, in order.
    pub fn endings(&self) -> impl Iterator<Item = LineEnding> + '_ {
        self.lines.iter().filter_map(|line| line.end)
    }

    /// The projection on the wire (`bend/ffi_doc_lines.bend`): the BOM
    /// flag, then each line's length in chars and its ending.
    pub(crate) fn put(&self, request: &mut Writer) {
        request.bool(self.bom).count(self.lines.len());
        for line in &self.lines {
            request.count(line.text.chars().count());
            match line.end {
                Some(end) => request.some().tag(end.tag()),
                None => request.none(),
            };
        }
    }
}

/// `content` without its BOM, each line ending made `\n` (a lone `\r`
/// stays).
#[must_use]
pub fn lf_text(content: &str) -> String {
    Projection::of(content).lf_text()
}

/// One call of `bend/ffi_doc_lines.bend`: the request's kind mark (`L`,
/// `W`), then its projections.
fn call_lines(mark: char, request: &mut Writer) -> String {
    let fields = expect_core(Entry::DocLines, request.finish());
    let request = format!("{mark}{fields}");
    expect_core(Entry::DocLines, eukhe_bend::call(Entry::DocLines, &request))
}

/// The carry of a loaded file: the separator an edit writes before a new
/// line that follows no line of the file (model `carry`: the file's first
/// ending, else LF).
pub(crate) fn carry(file: &Projection<'_>) -> LineEnding {
    let mut request = Writer::new();
    file.put(&mut request);
    let reply = call_lines('L', &mut request);
    expect_core(Entry::DocLines, read_carry(&reply))
}

fn read_carry(reply: &str) -> Result<LineEnding, WireError> {
    let mut reader = Reader::reply(reply)?;
    let end = LineEnding::read(&mut reader)?;
    reader.end()?;
    Ok(end)
}

/// What a whole-file write keeps of the file it replaces (model `Kept`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Kept {
    /// The file's BOM.
    pub(crate) bom: bool,
    /// The ending of every line of the new content.
    pub(crate) sep: LineEnding,
    /// Both texts have line endings and the content's first one differs.
    pub(crate) warn: bool,
}

/// The decision of a write of `content` over `previous` (model `write`).
pub(crate) fn kept(previous: &Projection<'_>, content: &Projection<'_>) -> Kept {
    let mut request = Writer::new();
    previous.put(&mut request);
    content.put(&mut request);
    let reply = call_lines('W', &mut request);
    expect_core(Entry::DocLines, read_kept(&reply))
}

fn read_kept(reply: &str) -> Result<Kept, WireError> {
    let mut reader = Reader::reply(reply)?;
    let kept = Kept {
        bom: reader.bool()?,
        sep: LineEnding::read(&mut reader)?,
        warn: reader.bool()?,
    };
    reader.end()?;
    Ok(kept)
}

/// What a file that is not UTF-8 text is: its BOM names UTF-16, else it is
/// some other encoding.
#[must_use]
pub(crate) fn encoding_name(bytes: &[u8]) -> &'static str {
    match bytes {
        [0xFF, 0xFE, ..] => "UTF-16 (little endian)",
        [0xFE, 0xFF, ..] => "UTF-16 (big endian)",
        _ => "not UTF-8",
    }
}

/// A byte count for messages: `512B`, `1.5KB`, `4.0MB`, `1.2GB`.
#[expect(
    clippy::cast_precision_loss,
    reason = "a one-decimal size label tolerates rounding"
)]
#[must_use]
pub(crate) fn format_bytes(bytes: u64) -> String {
    const KIB: u64 = 1024;
    if bytes < KIB {
        format!("{bytes}B")
    } else if bytes < KIB * KIB {
        format!("{:.1}KB", bytes as f64 / KIB as f64)
    } else if bytes < KIB * KIB * KIB {
        format!("{:.1}MB", bytes as f64 / (KIB * KIB) as f64)
    } else {
        format!("{:.1}GB", bytes as f64 / (KIB * KIB * KIB) as f64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The projection of a text, as the laws state it (model `proj`): the
    /// line lengths and endings recounted from the bytes.
    fn recount(content: &str) -> (bool, Vec<(usize, Option<LineEnding>)>) {
        let body = content.strip_prefix(BOM).unwrap_or(content);
        let bytes: Vec<char> = body.chars().collect();
        let mut lines = Vec::new();
        let mut len = 0;
        for (at, c) in bytes.iter().enumerate() {
            if *c == '\n' {
                let crlf = at > 0 && bytes[at - 1] == '\r';
                lines.push((
                    len - usize::from(crlf),
                    Some(if crlf {
                        LineEnding::CrLf
                    } else {
                        LineEnding::Lf
                    }),
                ));
                len = 0;
            } else {
                len += 1;
            }
        }
        lines.push((len, None));
        (content.starts_with(BOM), lines)
    }

    /// The scan is the projection the laws state, on texts of content, lone
    /// `\r`, `\r\n`, `\n`, multi-byte chars and a BOM; the LF text joins its
    /// lines with `\n`.
    #[test]
    fn the_scan_is_the_projection() {
        for text in [
            "",
            "\n",
            "a",
            "\u{FEFF}é\r\nb\r\n",
            "a\rb\r\nc\r\r\nd\n",
            "\r",
            "\r\n\r",
            "x\n\u{FEFF}y",
        ] {
            let projection = Projection::of(text);
            let lines: Vec<_> = projection
                .lines
                .iter()
                .map(|line| (line.text.chars().count(), line.end))
                .collect();
            assert_eq!((projection.bom, lines), recount(text), "{text:?}");
            assert_eq!(
                projection.lf_text(),
                text.strip_prefix(BOM).unwrap_or(text).replace("\r\n", "\n")
            );
        }
    }

    /// The carry and a write's decision reach the compiled core.
    #[test]
    fn carry_and_write_reach_the_core() {
        assert_eq!(carry(&Projection::of("a\r\nb\n")), LineEnding::CrLf);
        assert_eq!(
            kept(&Projection::of("\u{FEFF}a\r\nb"), &Projection::of("x\ny")),
            Kept {
                bom: true,
                sep: LineEnding::CrLf,
                warn: true
            }
        );
    }
}
