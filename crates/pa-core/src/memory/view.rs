//! The view: tree nodes ("parts") tiling the whole chat `[0, T)`, oldest
//! first, kept under [`VIEW`] bytes of line text. It only ever appends at
//! its end and coarsens by merging the most due adjacent pair; a merged part
//! is never split again, so consecutive views share their start and the
//! request prefix stays cacheable.

use std::fmt::Write as _;

use super::{MARKS, PLACEHOLDER, VIEW};

/// One tree node as a view part: `(l, i)` covers `[i·2^l, (i+1)·2^l)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct Part {
    pub l: u32,
    pub i: u64,
}

impl Part {
    /// The first message the part covers (`id` of `id+n`).
    pub(crate) fn start(self) -> u64 {
        self.i << self.l
    }

    /// How many messages the part covers (`n` of `id+n`).
    pub(crate) fn count(self) -> u64 {
        1 << self.l
    }

    /// One past the last message the part covers.
    pub(crate) fn end(self) -> u64 {
        (self.i + 1) << self.l
    }
}

/// Read access to the built node texts.
pub(crate) trait NodeTexts {
    /// The node's text, when it is built.
    fn node_text(&self, part: Part) -> Option<&str>;
}

/// The live view.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct View {
    parts: Vec<Part>,
    size: usize,
}

impl View {
    pub(crate) fn parts(&self) -> &[Part] {
        &self.parts
    }

    /// Bytes of line text, placeholders included.
    pub(crate) fn size(&self) -> usize {
        self.size
    }

    /// The new message `i` enters as its own level-0 part.
    pub(crate) fn append(&mut self, i: u64, tree: &impl NodeTexts) {
        let part = Part { l: 0, i };
        self.size += line_text(part, tree).len();
        self.parts.push(part);
    }

    /// A level-0 part in the view was built: its line now counts its
    /// summary instead of the placeholder.
    pub(crate) fn part_built(&mut self, part: Part, tree: &impl NodeTexts) {
        if part.l != 0 {
            return;
        }
        if let Ok(at) = self
            .parts
            .binary_search_by_key(&part.start(), |known| known.start())
        {
            if self.parts[at] == part {
                self.size = self.size - PLACEHOLDER.len() + line_text(part, tree).len();
            }
        }
    }

    /// Merge the most due built pair until the view fits [`VIEW`] or no
    /// pair has a built parent. `total` is the number of messages. Returns
    /// whether the view changed.
    pub(crate) fn fit(&mut self, total: u64, tree: &impl NodeTexts) -> bool {
        let mut changed = false;
        while self.size > VIEW {
            let mut best: Option<(usize, u64, u32)> = None;
            for (at, pair) in self.parts.windows(2).enumerate() {
                let (left, right) = (pair[0], pair[1]);
                let parent = Part {
                    l: left.l + 1,
                    i: left.i / 2,
                };
                if left.l == right.l
                    && left.i % 2 == 0
                    && right.i == left.i + 1
                    && tree.node_text(parent).is_some()
                {
                    let age = total - left.start();
                    let more_due = best.is_none_or(|(_, best_age, best_l)| {
                        more_due(age, left.l, best_age, best_l)
                    });
                    if more_due {
                        best = Some((at, age, left.l));
                    }
                }
            }
            let Some((at, _, _)) = best else {
                break;
            };
            let left = self.parts[at];
            let parent = Part {
                l: left.l + 1,
                i: left.i / 2,
            };
            let removed = line_text(left, tree).len() + line_text(self.parts[at + 1], tree).len();
            self.parts[at] = parent;
            self.parts.remove(at + 1);
            self.size = self.size - removed + line_text(parent, tree).len();
            changed = true;
        }
        changed
    }

    /// The first message whose view line is not built; `total` when every
    /// line is a summary.
    pub(crate) fn first_unbuilt(&self, total: u64, tree: &impl NodeTexts) -> u64 {
        self.parts
            .iter()
            .find(|part| tree.node_text(**part).is_none())
            .map_or(total, |part| part.start())
    }

    /// Whether every line of the view is a summary.
    pub(crate) fn settled(&self, tree: &impl NodeTexts) -> bool {
        self.parts
            .iter()
            .all(|part| tree.node_text(*part).is_some())
    }

    /// The agent's rendering: `<chat>`, one `id+n|text` line per part
    /// (newlines shown as spaces), `</chat>`.
    pub(crate) fn render(&self, tree: &impl NodeTexts) -> String {
        let mut out = String::with_capacity(self.size + self.parts.len() * 16 + 16);
        out.push_str("<chat>\n");
        for part in &self.parts {
            let _ = writeln!(
                out,
                "{}+{}|{}",
                part.start(),
                part.count(),
                flatten(line_text(*part, tree))
            );
        }
        out.push_str("</chat>");
        out
    }

    /// The compactor's context: the bare lines (no ids, no markers) of the
    /// parts that start before `end`, wrapped in `<chat>`.
    pub(crate) fn render_context(&self, end: u64, tree: &impl NodeTexts) -> String {
        let mut out = String::from("<chat>\n");
        for part in self.parts.iter().take_while(|part| part.start() < end) {
            out.push_str(&flatten(line_text(*part, tree)));
            out.push('\n');
        }
        out.push_str("</chat>");
        out
    }
}

/// `age_a / 2^(l_a+2) > age_b / 2^(l_b+2)`, exactly: both sides scale by
/// the smaller power, so the shift is at most 63 and fits in `u128`.
fn more_due(age_a: u64, l_a: u32, age_b: u64, l_b: u32) -> bool {
    let low = l_a.min(l_b);
    (u128::from(age_a) << (l_b - low)) > (u128::from(age_b) << (l_a - low))
}

/// A part's line text: its summary, or the placeholder.
pub(crate) fn line_text(part: Part, tree: &impl NodeTexts) -> &str {
    tree.node_text(part).unwrap_or(PLACEHOLDER)
}

/// Newlines (`\r\n`, `\n`, `\r`) as single spaces.
pub(crate) fn flatten(text: &str) -> String {
    text.replace("\r\n", " ").replace(['\n', '\r'], " ")
}

/// Cut a rendered view into pieces at the last line end before each of
/// [`MARKS`] characters; a mark past the end, or one that would repeat the
/// previous cut, is skipped. The pieces concatenate back to `text`.
pub(crate) fn pieces(text: &str) -> Vec<String> {
    let mut cuts = Vec::new();
    let mut marks = MARKS.iter().copied().peekable();
    let mut last_line_end: Option<usize> = None;
    for (chars, (at, character)) in text.char_indices().enumerate() {
        while marks.peek().is_some_and(|mark| chars >= *mark) {
            marks.next();
            if let Some(cut) = last_line_end {
                if cuts.last() != Some(&cut) {
                    cuts.push(cut);
                }
            }
        }
        if marks.peek().is_none() {
            break;
        }
        if character == '\n' {
            last_line_end = Some(at + 1);
        }
    }
    let mut out = Vec::with_capacity(cuts.len() + 1);
    let mut from = 0;
    for cut in cuts {
        out.push(text[from..cut].to_string());
        from = cut;
    }
    out.push(text[from..].to_string());
    out
}
