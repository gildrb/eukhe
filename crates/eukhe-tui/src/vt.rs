//! A virtual terminal: it applies the escape subset the inline writer
//! emits to a `width` x `height` grid that scrolls into a scrollback
//! list. The inline writer checks each frame on one before the frame
//! reaches the real terminal ([`crate::inline_term`]); tests read the
//! screen it leaves.
//!
//! - Autowrap works the xterm way: a glyph written into the last column
//!   leaves a pending wrap, the next glyph wraps and marks the row as
//!   soft-wrapped, and any control except SGR clears the pending wrap.
//! - A glyph takes its display width in cells ([`crate::width`]): a
//!   wide one takes two, a zero-width one joins the glyph before it.
//! - Moves are clamped to the grid, unknown sequences are ignored, and a
//!   truncated sequence is dropped: any input is safe.
//! - A resize reflows like modern terminals (kitty, VTE): a hard
//!   line longer than the new width wraps, soft-wrapped rows join again,
//!   and the cursor follows its cell.

use std::sync::Arc;

use unicode_segmentation::UnicodeSegmentation;

/// One cell of the grid.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Cell {
    /// A one-char glyph. A blank cell is a space.
    Char(char),
    /// A glyph of several chars (combining marks, emoji sequences).
    Cluster(Box<str>),
    /// The right half of a wide glyph.
    Spacer,
}

const BLANK: Cell = Cell::Char(' ');

/// One row of the screen.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct VtRow {
    cells: Vec<Cell>,
    /// The row's text continues on the next row (a soft wrap).
    wrapped: bool,
}

impl VtRow {
    /// The row's glyphs as text.
    pub(crate) fn text(&self) -> String {
        let mut text = String::with_capacity(self.cells.len());
        for cell in &self.cells {
            match cell {
                Cell::Char(c) => text.push(*c),
                Cell::Cluster(s) => text.push_str(s),
                Cell::Spacer => {}
            }
        }
        text
    }

    /// The cells written in the row (a wide glyph counts two).
    pub(crate) fn cell_count(&self) -> usize {
        self.cells.len()
    }

    /// Cut the row at `col`, blanking a wide glyph whose right half is
    /// cut off.
    fn truncate(&mut self, col: usize) {
        if col > 0 && self.cells.get(col) == Some(&Cell::Spacer) {
            self.cells[col - 1] = BLANK;
        }
        self.cells.truncate(col);
    }
}

/// A position: `row` counts from the first scrollback row (the grid
/// follows the scrollback), `col` is a cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Pos {
    pub(crate) row: usize,
    pub(crate) col: usize,
}

/// The terminal state. Rows are shared copy-on-write: a copy of the
/// screen is cheap, and a row written after the copy is a new row
/// ([`Vt::shares_row`]).
#[derive(Debug, Clone)]
pub(crate) struct Vt {
    width: usize,
    height: usize,
    scrollback: Vec<Arc<VtRow>>,
    grid: Vec<Arc<VtRow>>,
    /// The cursor's grid row and column.
    row: usize,
    col: usize,
    autowrap: bool,
    pending_wrap: bool,
    /// The blank row every erased or new row starts as.
    blank: Arc<VtRow>,
}

impl Vt {
    /// A blank screen with the cursor at the top left.
    pub(crate) fn new(width: usize, height: usize) -> Self {
        let height = height.max(1);
        let blank = Arc::new(VtRow::default());
        Vt {
            width: width.max(1),
            height,
            scrollback: Vec::new(),
            grid: vec![Arc::clone(&blank); height],
            row: 0,
            col: 0,
            autowrap: true,
            pending_wrap: false,
            blank,
        }
    }

    /// The cursor position.
    pub(crate) fn cursor(&self) -> Pos {
        Pos {
            row: self.scrollback.len() + self.row,
            col: self.col,
        }
    }

    /// The scrollback rows above the grid.
    pub(crate) fn scrollback_len(&self) -> usize {
        self.scrollback.len()
    }

    /// Drop the scrollback. Positions count from the grid's top again.
    pub(crate) fn forget_scrollback(&mut self) {
        self.scrollback.clear();
    }

    /// The scrollback and grid rows.
    pub(crate) fn rows_len(&self) -> usize {
        self.scrollback.len() + self.grid.len()
    }

    /// The row at `row`, counted from the first scrollback row.
    pub(crate) fn row_at(&self, row: usize) -> Option<&VtRow> {
        self.shared_row(row).map(|shared| &**shared)
    }

    /// Whether row `row` is row `other_row` of `other`, untouched since
    /// one screen was copied from the other. A blank row never is: every
    /// erase puts the one blank row object in place, so an erased row
    /// would read as untouched.
    pub(crate) fn shares_row(&self, row: usize, other: &Vt, other_row: usize) -> bool {
        match (self.shared_row(row), other.shared_row(other_row)) {
            (Some(mine), Some(theirs)) => {
                Arc::ptr_eq(mine, theirs) && !Arc::ptr_eq(mine, &self.blank)
            }
            (Some(_) | None, _) => false,
        }
    }

    fn shared_row(&self, row: usize) -> Option<&Arc<VtRow>> {
        match row.checked_sub(self.scrollback.len()) {
            Some(grid_row) => self.grid.get(grid_row),
            None => self.scrollback.get(row),
        }
    }

    /// The cursor's row, for writing.
    fn line(&mut self) -> &mut VtRow {
        Arc::make_mut(&mut self.grid[self.row])
    }

    #[cfg(test)]
    fn rows(&self) -> impl Iterator<Item = &VtRow> {
        self.scrollback.iter().chain(&self.grid).map(Arc::as_ref)
    }

    /// Apply terminal output.
    pub(crate) fn feed(&mut self, text: &str) {
        let mut rest = text;
        while let Some(c) = rest.chars().next() {
            let used = match c {
                '\x1b' => self.escape(rest),
                '\r' => {
                    self.pending_wrap = false;
                    self.col = 0;
                    1
                }
                '\n' | '\x0b' | '\x0c' => {
                    self.pending_wrap = false;
                    self.line_feed();
                    1
                }
                '\x08' => {
                    self.pending_wrap = false;
                    self.col = self.col.saturating_sub(1);
                    1
                }
                '\t' => {
                    self.pending_wrap = false;
                    self.col = ((self.col / 8 + 1) * 8).min(self.width - 1);
                    1
                }
                c if c.is_control() => c.len_utf8(),
                _ => {
                    let end = rest.find(char::is_control).unwrap_or(rest.len());
                    self.print(&rest[..end]);
                    end
                }
            };
            rest = &rest[used..];
        }
    }

    /// Apply the escape sequence at the start of `rest` (which starts
    /// with ESC) and return its length in bytes.
    fn escape(&mut self, rest: &str) -> usize {
        let bytes = rest.as_bytes();
        let Some(&second) = bytes.get(1) else {
            return bytes.len();
        };
        match second {
            b'[' => {
                for (at, &byte) in bytes.iter().enumerate().skip(2) {
                    match byte {
                        0x20..=0x3f => {}
                        0x40..=0x7e => {
                            self.csi(&rest[2..at], char::from(byte));
                            return at + 1;
                        }
                        // A stray byte cancels the sequence.
                        _ => return at,
                    }
                }
                bytes.len()
            }
            // OSC, DCS, APC, PM, SOS: skipped up to BEL or ST. An ESC
            // that does not start ST ends the string and starts a new
            // sequence.
            b']' | b'P' | b'_' | b'^' | b'X' => {
                let mut at = 2;
                while at < bytes.len() {
                    match bytes[at] {
                        0x07 => return at + 1,
                        0x1b if bytes.get(at + 1) == Some(&b'\\') => return at + 2,
                        0x1b => return at,
                        0xc2 if bytes.get(at + 1) == Some(&0x9c) => return at + 2,
                        _ => at += 1,
                    }
                }
                bytes.len()
            }
            b'D' => {
                self.pending_wrap = false;
                self.line_feed();
                2
            }
            b'E' => {
                self.pending_wrap = false;
                self.line_feed();
                self.col = 0;
                2
            }
            b'M' => {
                self.pending_wrap = false;
                if self.row == 0 {
                    self.grid.pop();
                    self.grid.insert(0, Arc::clone(&self.blank));
                } else {
                    self.row -= 1;
                }
                2
            }
            // ESC followed by a control: the control runs on its own.
            0x00..=0x1f => 1,
            // Intermediate bytes, then one final byte (charset choice).
            0x20..=0x2f => match bytes[2..].iter().position(|b| !(0x20..=0x2f).contains(b)) {
                Some(at) if bytes[2 + at] < 0x80 => 2 + at + 1,
                Some(at) => 2 + at,
                None => bytes.len(),
            },
            _ => rest[1..].chars().next().map_or(1, |c| 1 + c.len_utf8()),
        }
    }

    /// Apply one CSI sequence: `body` holds its parameter and
    /// intermediate bytes, `last` its final byte.
    fn csi(&mut self, body: &str, last: char) {
        // SGR styles cells; the screen keeps glyphs only.
        if last == 'm' {
            return;
        }
        self.pending_wrap = false;
        if body.bytes().any(|b| (0x20..=0x2f).contains(&b)) {
            return;
        }
        if let Some(modes) = body.strip_prefix('?') {
            if matches!(last, 'h' | 'l') && modes.split(';').any(|mode| mode == "7") {
                self.autowrap = last == 'h';
            }
            return;
        }
        if body.starts_with(['>', '<', '=']) {
            return;
        }
        let param = |at: usize| -> usize {
            body.split(';')
                .nth(at)
                .and_then(|p| p.parse().ok())
                .unwrap_or(0)
        };
        let n = param(0).max(1);
        let last_row = self.height - 1;
        let last_col = self.width - 1;
        match last {
            'A' => self.row = self.row.saturating_sub(n),
            'B' | 'e' => self.row = self.row.saturating_add(n).min(last_row),
            'C' | 'a' => self.col = self.col.saturating_add(n).min(last_col),
            'D' => self.col = self.col.saturating_sub(n),
            'E' => {
                self.row = self.row.saturating_add(n).min(last_row);
                self.col = 0;
            }
            'F' => {
                self.row = self.row.saturating_sub(n);
                self.col = 0;
            }
            'G' | '`' => self.col = (n - 1).min(last_col),
            'd' => self.row = (n - 1).min(last_row),
            'H' | 'f' => {
                self.row = (param(0).max(1) - 1).min(last_row);
                self.col = (param(1).max(1) - 1).min(last_col);
            }
            'K' => self.erase_line(param(0)),
            'J' => match param(0) {
                0 => {
                    self.erase_line(0);
                    let blank = &self.blank;
                    for row in &mut self.grid[self.row + 1..] {
                        *row = Arc::clone(blank);
                    }
                }
                1 => {
                    let blank = &self.blank;
                    for row in &mut self.grid[..self.row] {
                        *row = Arc::clone(blank);
                    }
                    self.erase_line(1);
                }
                2 => self.grid.fill(Arc::clone(&self.blank)),
                3 => self.scrollback.clear(),
                _ => {}
            },
            'X' => {
                let col = self.col;
                let cells = &mut self.line().cells;
                let end = col.saturating_add(n).min(cells.len());
                if col > 0 && cells.get(col) == Some(&Cell::Spacer) {
                    cells[col - 1] = BLANK;
                }
                if cells.get(end) == Some(&Cell::Spacer) {
                    cells[end] = BLANK;
                }
                for cell in cells.iter_mut().take(end).skip(col) {
                    *cell = BLANK;
                }
            }
            _ => {}
        }
    }

    /// EL: 0 erases from the cursor to the row end, 1 from the row start
    /// to the cursor, 2 the whole row.
    fn erase_line(&mut self, mode: usize) {
        let col = self.col;
        match mode {
            0 => {
                let row = self.line();
                row.truncate(col);
                row.wrapped = false;
            }
            1 => {
                let row = self.line();
                let end = (col + 1).min(row.cells.len());
                if row.cells.get(end) == Some(&Cell::Spacer) {
                    row.cells[end] = BLANK;
                }
                row.cells[..end].fill(BLANK);
            }
            2 => self.grid[self.row] = Arc::clone(&self.blank),
            _ => {}
        }
    }

    fn line_feed(&mut self) {
        if self.row + 1 >= self.height {
            let top = self.grid.remove(0);
            self.scrollback.push(top);
            self.grid.push(Arc::clone(&self.blank));
            self.row = self.height - 1;
        } else {
            self.row += 1;
        }
    }

    /// Print a run of text without controls. ASCII goes one cell per
    /// byte; grapheme clusters are found only around other chars (an
    /// ASCII char right before one may start its cluster).
    fn print(&mut self, text: &str) {
        let mut rest = text;
        while !rest.is_empty() {
            let ascii = rest.bytes().take_while(u8::is_ascii).count();
            let plain = if ascii == rest.len() {
                ascii
            } else {
                ascii.saturating_sub(1)
            };
            for byte in rest[..plain].bytes() {
                self.put(Cell::Char(char::from(byte)), 1);
            }
            rest = &rest[plain..];
            let mut resume = rest.len();
            for (at, glyph) in rest.grapheme_indices(true) {
                if at > 0 && glyph.len() == 1 {
                    resume = at;
                    break;
                }
                let width = crate::width::grapheme_width(glyph);
                if width == 0 {
                    self.join_previous(glyph);
                    continue;
                }
                let mut chars = glyph.chars();
                let cell = match (chars.next(), chars.next()) {
                    (Some(c), None) => Cell::Char(c),
                    (Some(_) | None, _) => Cell::Cluster(glyph.into()),
                };
                self.put(cell, width);
            }
            rest = &rest[resume..];
        }
    }

    /// Add a zero-width glyph to the glyph before the cursor.
    fn join_previous(&mut self, glyph: &str) {
        let previous = if self.pending_wrap {
            Some(self.col)
        } else {
            self.col.checked_sub(1)
        };
        let Some(at) = previous else {
            return;
        };
        let cells = &mut self.line().cells;
        let at = match cells.get(at) {
            Some(Cell::Spacer) if at > 0 => at - 1,
            Some(Cell::Char(_) | Cell::Cluster(_)) => at,
            Some(Cell::Spacer) | None => return,
        };
        let joined = match &cells[at] {
            Cell::Char(c) => format!("{c}{glyph}"),
            Cell::Cluster(s) => format!("{s}{glyph}"),
            Cell::Spacer => return,
        };
        cells[at] = Cell::Cluster(joined.into_boxed_str());
    }

    /// Write one glyph `width` cells wide at the cursor.
    fn put(&mut self, cell: Cell, width: usize) {
        let width = width.min(self.width);
        if self.pending_wrap {
            self.pending_wrap = false;
            self.line().wrapped = true;
            self.line_feed();
            self.col = 0;
        }
        if self.col + width > self.width {
            if self.autowrap {
                self.line().wrapped = true;
                self.line_feed();
                self.col = 0;
            } else {
                self.col = self.width - width;
            }
        }
        let col = self.col;
        let cells = &mut self.line().cells;
        if cells.len() < col + width {
            cells.resize(col + width, BLANK);
        }
        if col > 0 && cells[col] == Cell::Spacer {
            cells[col - 1] = BLANK;
        }
        if cells.get(col + width) == Some(&Cell::Spacer) {
            cells[col + width] = BLANK;
        }
        cells[col] = cell;
        cells[col + 1..col + width].fill(Cell::Spacer);
        if col + width < self.width {
            self.col = col + width;
        } else {
            self.col = self.width - 1;
            self.pending_wrap = self.autowrap;
        }
    }

    /// Resize to `width` x `height`; see [`Vt::resize_marked`].
    #[cfg(test)]
    pub(crate) fn resize(&mut self, width: usize, height: usize) {
        self.resize_marked(width, height, &mut []);
    }

    /// Resize to `width` x `height` and move each of `marks` with its
    /// cell. A new width reflows every row: each logical line (rows
    /// joined by soft wraps) is wrapped again at the new width. The grid
    /// then ends at the last written row or the cursor row, whichever is
    /// lower; rows above it go to scrollback, and scrollback rows come
    /// back down when there is room.
    pub(crate) fn resize_marked(&mut self, width: usize, height: usize, marks: &mut [Pos]) {
        let width = width.max(1);
        let height = height.max(1);
        let mut points: Vec<Pos> = std::iter::once(self.cursor())
            .chain(marks.iter().copied())
            .collect();
        let mut rows = std::mem::take(&mut self.scrollback);
        rows.append(&mut self.grid);
        if width != self.width {
            rows = rewrap(rows, width, &mut points);
        }
        let cursor = points[0];
        marks.copy_from_slice(&points[1..]);
        let written = rows
            .iter()
            .rposition(|row| **row != VtRow::default())
            .map_or(0, |at| at + 1);
        let end = written.max(cursor.row + 1);
        let start = end.saturating_sub(height).min(cursor.row);
        let stop = (start + height).min(rows.len());
        rows.truncate(stop);
        self.grid = rows.split_off(start);
        self.grid.resize_with(height, || Arc::clone(&self.blank));
        self.scrollback = rows;
        self.width = width;
        self.height = height;
        self.row = cursor.row - start;
        self.col = cursor.col.min(width - 1);
        self.pending_wrap = false;
    }

    /// Every row's text, scrollback first, trailing empty rows dropped.
    #[cfg(test)]
    pub(crate) fn all(&self) -> Vec<String> {
        let mut out: Vec<String> = self.rows().map(VtRow::text).collect();
        while out.last().is_some_and(String::is_empty) {
            out.pop();
        }
        out
    }

    /// The logical lines: every soft-wrapped row joined with the row
    /// below it, the way a terminal's selection reads them.
    #[cfg(test)]
    pub(crate) fn logical(&self) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        let mut joining = false;
        for row in self.rows() {
            match (joining, out.last_mut()) {
                (true, Some(last)) => last.push_str(&row.text()),
                (true | false, _) => out.push(row.text()),
            }
            joining = row.wrapped;
        }
        while out.last().is_some_and(String::is_empty) {
            out.pop();
        }
        out
    }
}

/// Where a point is while [`rewrap`] lays out the lines.
#[derive(Debug, Clone, Copy)]
enum Track {
    /// Its line is not reached yet.
    Waiting,
    /// At this cell offset in the line being laid out.
    Placing(usize),
    /// Moved to its new place.
    Done,
}

/// Wrap every logical line of `rows` again at `width`, moving each of
/// `points` with its cell. A point past the end of its line keeps its
/// distance from the end, clamped to the line's last row.
fn rewrap(rows: Vec<Arc<VtRow>>, width: usize, points: &mut [Pos]) -> Vec<Arc<VtRow>> {
    let mut out: Vec<Arc<VtRow>> = Vec::with_capacity(rows.len());
    let mut tracks = vec![Track::Waiting; points.len()];
    let mut cells: Vec<Cell> = Vec::new();
    let mut rows = rows.into_iter().enumerate().peekable();
    while let Some((at, row)) = rows.next() {
        for (point, track) in points.iter().zip(&mut tracks) {
            if matches!(track, Track::Waiting) && point.row == at {
                *track = Track::Placing(cells.len() + point.col);
            }
        }
        let row = Arc::unwrap_or_clone(row);
        let wrapped = row.wrapped;
        cells.extend(row.cells);
        if wrapped && rows.peek().is_some() {
            continue;
        }
        // The line ends: lay its cells out at the new width.
        let mut line = VtRow::default();
        let mut col = 0;
        let mut source = 0;
        let mut glyphs = std::mem::take(&mut cells).into_iter().peekable();
        while let Some(glyph) = glyphs.next() {
            let mut span = 1;
            while glyphs.next_if_eq(&Cell::Spacer).is_some() {
                span += 1;
            }
            let shown = span.min(width);
            if col + shown > width {
                line.wrapped = true;
                out.push(Arc::new(std::mem::take(&mut line)));
                col = 0;
            }
            for (point, track) in points.iter_mut().zip(&mut tracks) {
                if let Track::Placing(offset) = *track {
                    if (source..source + span).contains(&offset) {
                        *point = Pos {
                            row: out.len(),
                            col: col + (offset - source).min(shown - 1),
                        };
                        *track = Track::Done;
                    }
                }
            }
            line.cells.push(match glyph {
                Cell::Spacer => BLANK,
                Cell::Char(_) | Cell::Cluster(_) => glyph,
            });
            line.cells
                .extend(std::iter::repeat_n(Cell::Spacer, shown - 1));
            col += shown;
            source += span;
        }
        for (point, track) in points.iter_mut().zip(&mut tracks) {
            if let Track::Placing(offset) = *track {
                *point = Pos {
                    row: out.len(),
                    col: (col + offset.saturating_sub(source)).min(width - 1),
                };
                *track = Track::Done;
            }
        }
        out.push(Arc::new(line));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_wide_glyph_takes_two_cells_and_wraps_whole() {
        let mut vt = Vt::new(4, 3);
        vt.feed("a界b\r\nabc界");
        assert_eq!(vt.all(), ["a界b", "abc", "界"]);
        assert_eq!(vt.logical(), ["a界b", "abc界"]);
        assert_eq!(vt.cursor(), Pos { row: 2, col: 2 });
    }

    #[test]
    fn overwriting_half_a_wide_glyph_blanks_the_other_half() {
        let mut vt = Vt::new(6, 2);
        vt.feed("界界\rx\x1b[3Cy");
        assert_eq!(vt.all(), ["x 界y"]);
        vt.feed("\r\n e\u{301}\u{301}!");
        assert_eq!(vt.all(), ["x 界y", " e\u{301}\u{301}!"]);
    }

    #[test]
    fn autowrap_off_overwrites_the_last_cell() {
        let mut vt = Vt::new(4, 2);
        vt.feed("\x1b[?7labcdef\x1b[?7h\r\n\x1b[2Kxy\x1b]8;;https://x\x1b\\z\x1b]8;;\x07");
        assert_eq!(vt.all(), ["abcf", "xyz"]);
        assert_eq!(vt.logical(), ["abcf", "xyz"]);
    }

    #[test]
    fn a_resize_reflows_lines_and_the_cursor_follows_its_cell() {
        let mut vt = Vt::new(10, 10);
        vt.feed("0123456789abcde\r\n\x1b[?7lABCDEFGHIJ\x1b[?7h\r\nz");
        assert_eq!(vt.all(), ["0123456789", "abcde", "ABCDEFGHIJ", "z"]);
        vt.feed("\x1b[2A\r\x1b[3C");
        assert_eq!(vt.cursor(), Pos { row: 1, col: 3 });
        vt.resize(4, 10);
        assert_eq!(
            vt.all(),
            ["0123", "4567", "89ab", "cde", "ABCD", "EFGH", "IJ", "z"]
        );
        assert_eq!(vt.logical(), ["0123456789abcde", "ABCDEFGHIJ", "z"]);
        assert_eq!(vt.cursor(), Pos { row: 3, col: 1 });
        vt.resize(10, 10);
        assert_eq!(vt.all(), ["0123456789", "abcde", "ABCDEFGHIJ", "z"]);
        assert_eq!(vt.cursor(), Pos { row: 1, col: 3 });
        let mut marks = [Pos { row: 2, col: 9 }];
        vt.resize_marked(3, 10, &mut marks);
        assert_eq!(marks, [Pos { row: 8, col: 0 }]);
        // A shorter screen keeps the cursor row on it: rows above go to
        // scrollback, rows past the bottom are cut.
        vt.resize(3, 4);
        assert_eq!(vt.scrollback_len(), 4);
        assert_eq!(vt.cursor(), Pos { row: 4, col: 1 });
        assert_eq!(
            vt.all(),
            ["012", "345", "678", "9ab", "cde", "ABC", "DEF", "GHI"]
        );
    }

    /// Any input, cut anywhere, leaves the cursor on the grid and no row
    /// wider than the screen.
    #[test]
    fn arbitrary_input_never_panics() {
        const PIECES: [&str; 24] = [
            "\x1b",
            "[",
            "?",
            "7",
            "l",
            "h",
            ";",
            "A",
            "J",
            "K",
            "2",
            "3",
            "]8;;u",
            "\x07",
            "\\",
            "界",
            "e\u{301}",
            "\n",
            "\r",
            "x",
            "\x1b[999999999999999999999B",
            "_G",
            "\u{9c}",
            "\t",
        ];
        let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut next = move |bound: usize| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed % bound as u64) as usize
        };
        for _ in 0..200 {
            let mut vt = Vt::new(1 + next(6), 1 + next(4));
            for _ in 0..40 {
                let text: String = (0..=next(12)).map(|_| PIECES[next(PIECES.len())]).collect();
                vt.feed(&text);
                if next(8) == 0 {
                    vt.resize(1 + next(6), 1 + next(4));
                }
                assert!(vt.row < vt.height && vt.col < vt.width);
                assert_eq!(vt.grid.len(), vt.height);
                assert!(vt.rows().all(|row| row.cells.len() <= vt.width));
            }
        }
    }
}
