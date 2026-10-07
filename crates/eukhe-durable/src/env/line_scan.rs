//! Port of `env/line-scan.ts`.

use super::decode::{range_decoder, starts_with_bom, Utf8Decoder};
use super::LineScan;

const NEWLINE: u8 = b'\n';
/// `Number.MAX_SAFE_INTEGER`.
const MAX_SAFE_INTEGER: f64 = 9_007_199_254_740_991.0;

/// The JS `RangeError("Invalid line range")` of the `LineScanner` constructor.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
#[error("Invalid line range")]
pub struct InvalidLineRange;

/// `Number.isSafeInteger(value)`.
pub(crate) fn is_safe_integer(value: f64) -> bool {
    value.is_finite() && value.fract() == 0.0 && value.abs() <= MAX_SAFE_INTEGER
}

/// Computes a [`LineScan`] from a file's bytes fed in order, so an environment
/// can scan any size in bounded memory. Decoded sizes use the same streaming
/// WHATWG decoder as decoding the whole file at once.
#[derive(Clone, Debug)]
pub struct LineScanner {
    start_line: u64,
    /// `None`: to the end (`Infinity` in TS).
    end_line: Option<u64>,
    position: u64,
    newlines: u64,
    line_start: u64,
    start: Option<u64>,
    end: Option<u64>,
    first_line_end: Option<u64>,
    last_line_start: Option<u64>,
    selected_bytes: u64,
    first_line_bytes: u64,
    selection: Option<Utf8Decoder>,
    first_line: Option<Utf8Decoder>,
    /// The first bytes, held until it is known whether they are a byte-order
    /// mark.
    head: Option<Vec<u8>>,
    bom: bool,
}

impl LineScanner {
    /// `start_line` and `end_line` must be non-negative integers with
    /// `end_line > start_line`; `end_line` absent (or `Infinity`): to the end.
    ///
    /// # Errors
    ///
    /// [`InvalidLineRange`] when the range is not such a range.
    #[allow(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "both lines are checked to be non-negative safe integers first"
    )]
    pub fn new(start_line: f64, end_line: Option<f64>) -> Result<Self, InvalidLineRange> {
        let end = end_line.unwrap_or(f64::INFINITY);
        let ascending = end.partial_cmp(&start_line) == Some(std::cmp::Ordering::Greater);
        if !is_safe_integer(start_line) || start_line < 0.0 || !ascending {
            return Err(InvalidLineRange);
        }
        if end != f64::INFINITY && !is_safe_integer(end) {
            return Err(InvalidLineRange);
        }
        let mut scanner = Self {
            start_line: start_line as u64,
            end_line: (end != f64::INFINITY).then_some(end as u64),
            position: 0,
            newlines: 0,
            line_start: 0,
            start: None,
            end: None,
            first_line_end: None,
            last_line_start: None,
            selected_bytes: 0,
            first_line_bytes: 0,
            selection: None,
            first_line: None,
            head: Some(Vec::with_capacity(3)),
            bom: false,
        };
        if scanner.start_line == 0 {
            scanner.begin(0);
        }
        Ok(scanner)
    }

    /// Whether `line` is the last selected line.
    fn is_last_line(&self, line: u64) -> bool {
        self.end_line.is_some_and(|end_line| line == end_line - 1)
    }

    /// Feed the next bytes of the file.
    pub fn push(&mut self, chunk: &[u8]) {
        let mut chunk = chunk;
        if let Some(head) = &mut self.head {
            let take = (3 - head.len()).min(chunk.len());
            head.extend_from_slice(&chunk[..take]);
            if head.len() < 3 {
                return;
            }
            self.release_head();
            chunk = &chunk[take..];
        }
        self.process(chunk);
    }

    fn release_head(&mut self) {
        let head = self.head.take().unwrap_or_default();
        self.bom = starts_with_bom(&head);
        self.process(&head);
    }

    fn process(&mut self, chunk: &[u8]) {
        let base = self.position;
        let mut from = 0;
        let mut search = 0;
        while let Some(found) = chunk[search..].iter().position(|&byte| byte == NEWLINE) {
            let index = search + found;
            // The newline ends line `self.newlines`. It belongs to the selection
            // between selected lines only.
            self.feed(chunk, base, from, index);
            let line = self.newlines;
            let position = base + index as u64;
            if line == self.start_line {
                self.end_first_line(position);
            }
            if self.is_last_line(line) {
                self.end_selection(position);
            }
            self.feed(chunk, base, index, index + 1);
            from = index + 1;
            self.newlines += 1;
            self.line_start = position + 1;
            if self.newlines == self.start_line {
                self.begin(self.line_start);
            }
            if self.is_last_line(self.newlines) {
                self.last_line_start = Some(self.line_start);
            }
            search = index + 1;
        }
        self.feed(chunk, base, from, chunk.len());
        self.position += chunk.len() as u64;
    }

    /// The scan of all bytes fed.
    pub fn finish(&mut self) -> LineScan {
        if self.head.is_some() {
            self.release_head();
        }
        let size = self.position;
        let Some(start) = self.start else {
            return LineScan {
                newlines: self.newlines,
                start: size,
                end: size,
                first_line_end: size,
                last_line_start: size,
                selected_bytes: 0,
                first_line_bytes: 0,
            };
        };
        if self.first_line_end.is_none() {
            self.end_first_line(size);
        }
        if self.end.is_none() {
            self.end_selection(size);
        }
        LineScan {
            newlines: self.newlines,
            start,
            end: self.end.unwrap_or(size),
            first_line_end: self.first_line_end.unwrap_or(size),
            // A selection that reaches past the last line ends with the last line.
            last_line_start: self.last_line_start.unwrap_or(self.line_start),
            selected_bytes: self.selected_bytes,
            first_line_bytes: self.first_line_bytes,
        }
    }

    fn begin(&mut self, start: u64) {
        self.start = Some(start);
        if self.is_last_line(self.start_line) {
            self.last_line_start = Some(start);
        }
        self.selection = Some(range_decoder());
        self.first_line = Some(range_decoder());
    }

    fn end_first_line(&mut self, position: u64) {
        self.first_line_end = Some(position);
        if let Some(mut decoder) = self.first_line.take() {
            self.first_line_bytes += decoder.finish_len() as u64;
        }
    }

    fn end_selection(&mut self, position: u64) {
        self.end = Some(position);
        if let Some(mut decoder) = self.selection.take() {
            self.selected_bytes += decoder.finish_len() as u64;
        }
    }

    /// Feed `chunk[from, to)`, which starts at file offset `base`, to the
    /// decoders of the ranges still open.
    fn feed(&mut self, chunk: &[u8], base: u64, from: usize, to: usize) {
        let mut from = from;
        // Decoding the whole file drops a leading byte-order mark.
        if self.bom && base + (from as u64) < 3 {
            // `base < 3` here, so the difference fits.
            let skip = usize::try_from(3 - base).unwrap_or(usize::MAX);
            from = to.min(skip);
        }
        if to <= from {
            return;
        }
        let bytes = &chunk[from..to];
        if let Some(decoder) = &mut self.selection {
            self.selected_bytes += decoder.decode_chunk_len(bytes) as u64;
        }
        if let Some(decoder) = &mut self.first_line {
            self.first_line_bytes += decoder.decode_chunk_len(bytes) as u64;
        }
    }
}
