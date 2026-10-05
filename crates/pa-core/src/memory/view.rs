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

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    #[derive(Default)]
    struct Tree(HashMap<Part, String>);

    impl NodeTexts for Tree {
        fn node_text(&self, part: Part) -> Option<&str> {
            self.0.get(&part).map(String::as_str)
        }
    }

    impl Tree {
        fn build(&mut self, l: u32, i: u64, text: String) {
            self.0.insert(Part { l, i }, text);
        }
    }

    #[test]
    fn small_views_hold_one_line_per_message() {
        let mut tree = Tree::default();
        let mut view = View::default();
        for i in 0..4 {
            tree.build(0, i, format!("user: m{i}"));
            view.append(i, &tree);
            assert!(!view.fit(i + 1, &tree));
        }
        tree.build(1, 0, "merged".to_string());
        assert!(!view.fit(4, &tree));
        assert_eq!(
            view.render(&tree),
            "<chat>\n0+1|user: m0\n1+1|user: m1\n2+1|user: m2\n3+1|user: m3\n</chat>"
        );
        assert_eq!(
            view.render_context(2, &tree),
            "<chat>\nuser: m0\nuser: m1\n</chat>"
        );
    }

    #[test]
    fn over_budget_views_merge_the_oldest_pair_first() {
        let mut tree = Tree::default();
        let mut view = View::default();
        let line = "x".repeat(500);
        let total = (VIEW / 500 + 2) as u64;
        for i in 0..total {
            tree.build(0, i, line.clone());
            view.append(i, &tree);
        }
        for i in 0..total / 2 {
            tree.build(1, i, "y".repeat(500));
        }
        assert!(view.fit(total, &tree));
        assert!(view.size() <= VIEW);
        // 258 lines of 500 bytes need two merges; at equal levels the
        // oldest pair is the most due.
        assert_eq!(view.size(), VIEW);
        assert_eq!(
            view.parts()[..3],
            [
                Part { l: 1, i: 0 },
                Part { l: 1, i: 1 },
                Part { l: 0, i: 4 }
            ]
        );
    }

    #[test]
    fn unbuilt_parents_block_merging() {
        let mut tree = Tree::default();
        let mut view = View::default();
        let total = (VIEW / 500 + 2) as u64;
        for i in 0..total {
            tree.build(0, i, "x".repeat(500));
            view.append(i, &tree);
        }
        assert!(!view.fit(total, &tree));
        assert!(view.size() > VIEW);
    }

    #[test]
    fn placeholders_count_until_built() {
        let mut tree = Tree::default();
        let mut view = View::default();
        view.append(0, &tree);
        assert_eq!(view.size(), PLACEHOLDER.len());
        assert!(!view.settled(&tree));
        assert_eq!(view.first_unbuilt(1, &tree), 0);
        assert_eq!(
            view.render(&tree),
            format!("<chat>\n0+1|{PLACEHOLDER}\n</chat>")
        );
        tree.build(0, 0, "user: hi".to_string());
        view.part_built(Part { l: 0, i: 0 }, &tree);
        assert_eq!(view.size(), "user: hi".len());
        assert!(view.settled(&tree));
        assert_eq!(view.first_unbuilt(1, &tree), 1);
    }

    #[test]
    fn due_weighs_age_against_level() {
        // age 8 at level 1 (8/8 = 1) beats age 6 at level 0 (6/4 = 1.5)? No.
        assert!(!more_due(8, 1, 6, 0));
        assert!(more_due(6, 0, 8, 1));
        // Ties keep the earlier (older) pair: strict comparison.
        assert!(!more_due(8, 1, 4, 0));
    }

    #[test]
    fn pieces_cut_at_line_ends_before_each_mark() {
        let line = format!("{}\n", "a".repeat(999));
        let text = line.repeat(120);
        let pieces = pieces(&text);
        assert_eq!(pieces.concat(), text);
        assert_eq!(
            pieces.iter().map(String::len).collect::<Vec<_>>(),
            vec![50_000, 30_000, 20_000, 20_000]
        );
        assert_eq!(super::pieces("short\n"), vec!["short\n".to_string()]);
    }

    #[test]
    fn flatten_turns_every_newline_into_one_space() {
        assert_eq!(flatten("a\r\nb\nc\rd"), "a b c d");
    }
}
