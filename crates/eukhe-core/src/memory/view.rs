//! The view: tree nodes ("parts") tiling the whole chat `[0, T)`, oldest
//! first. It only ever appends at its end, and coarsens by merging the most
//! due adjacent pairs in batches (§3.2); a merged part is never split again,
//! so consecutive views share their start and the request prefix stays
//! cacheable.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::{BLOCK, PLACEHOLDER};

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
    /// The view of `total` messages after `merges`, in log order: every
    /// message enters as its own part, and each merge replaces its two
    /// children with their parent (§3.2). Messages only ever append at the
    /// end, so a merge's children are in the view whatever came after
    /// them. A merge whose children are not both in the view is skipped
    /// and returned.
    pub(crate) fn fold(
        total: u64,
        merges: impl IntoIterator<Item = Part>,
        tree: &impl NodeTexts,
    ) -> (View, Vec<Part>) {
        let mut by_start: BTreeMap<u64, Part> = (0..total).map(|i| (i, Part { l: 0, i })).collect();
        let mut skipped = Vec::new();
        for parent in merges {
            let children = parent.l.checked_sub(1).map(|l| {
                (
                    Part { l, i: parent.i * 2 },
                    Part {
                        l,
                        i: parent.i * 2 + 1,
                    },
                )
            });
            let Some((left, right)) = children.filter(|(left, right)| {
                by_start.get(&left.start()) == Some(left)
                    && by_start.get(&right.start()) == Some(right)
            }) else {
                skipped.push(parent);
                continue;
            };
            by_start.remove(&right.start());
            by_start.insert(left.start(), parent);
        }
        let parts: Vec<Part> = by_start.into_values().collect();
        let size = parts.iter().map(|part| line_text(*part, tree).len()).sum();
        (View { parts, size }, skipped)
    }

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

    /// Merge the most due built pair until the view fits `budget` bytes or
    /// no pair has a built parent. `total` is the number of messages.
    /// Returns the merged parents, in merge order.
    ///
    /// A pair is due by how long ago it ended in its own line size,
    /// `(T - last) / 2^l`, written as `(T + 1)/2^l - i` (same order, shifted
    /// by 2); of equal pairs the oldest merges first. This picks the merges
    /// of Taelin's rollback `push`. Measuring from the pair's first message
    /// rewrites old lines near ties.
    pub(crate) fn fit(&mut self, total: u64, budget: usize, tree: &impl NodeTexts) -> Vec<Part> {
        let mut merged = Vec::new();
        while self.size > budget {
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
                    // `T + 1 - first`: the pair ends at `first + 2^(l+1) - 1`
                    // and `right` exists, so this is at least `2^(l+1)`.
                    let age = total + 1 - left.start();
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
            merged.push(parent);
        }
        merged
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

    /// A compaction's view (§4): `<chat>`, one `id+n|text` line per part
    /// that starts before `end`, `</chat>`; it stops at the first unbuilt
    /// line, so no call sees a placeholder or half a message.
    pub(crate) fn render_built_until(&self, end: u64, tree: &impl NodeTexts) -> String {
        let mut out = String::from("<chat>\n");
        for part in self.parts.iter().take_while(|part| part.start() < end) {
            let Some(text) = tree.node_text(*part) else {
                break;
            };
            let _ = writeln!(out, "{}+{}|{}", part.start(), part.count(), flatten(text));
        }
        out.push_str("</chat>");
        out
    }
}

/// Whether `parts` tile `[0, end)` for some `end <= total`, oldest first,
/// each a real tree node (`start` a multiple of its count). Returns that
/// `end`, or `None` when they do not.
pub(crate) fn tiled_end(parts: &[Part], total: u64) -> Option<u64> {
    let mut end = 0u64;
    for part in parts {
        let count = 1u64.checked_shl(part.l).filter(|_| part.l < 63)?;
        let start = part.i.checked_mul(count)?;
        if start != end {
            return None;
        }
        end = start.checked_add(count).filter(|end| *end <= total)?;
    }
    Some(end)
}

/// `age_a / 2^l_a > age_b / 2^l_b`, exactly: both sides scale by the
/// smaller power, so the shift is at most 63 and fits in `u128`. Strict:
/// of equal pairs, the earlier (older) one stays the best.
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

/// Cut a rendered view (`<chat>`, its lines, `</chat>`) after its last
/// whole block of [`BLOCK`] lines (§3.3): the first piece carries the cache
/// mark, the second holds the lines after it and the frame's end. A view
/// shorter than one block is one piece. The pieces concatenate back to
/// `text`.
pub(crate) fn pieces(text: &str) -> Vec<String> {
    let lines = text.matches('\n').count();
    // `<chat>\n` and the view lines end in a newline; `</chat>` does not.
    let blocks = lines.saturating_sub(1) / BLOCK;
    if blocks == 0 {
        return vec![text.to_string()];
    }
    let keep = 1 + blocks * BLOCK;
    let cut = text
        .match_indices('\n')
        .nth(keep - 1)
        .map_or(text.len(), |(at, _)| at + 1);
    vec![text[..cut].to_string(), text[cut..].to_string()]
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::memory::VIEW_CEILING as VIEW;

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

    /// The parts as `(l, i)` pairs.
    fn coordinates(view: &View) -> Vec<(u32, u64)> {
        view.parts().iter().map(|part| (part.l, part.i)).collect()
    }

    #[test]
    fn small_views_hold_one_line_per_message() {
        let mut tree = Tree::default();
        let mut view = View::default();
        for i in 0..4 {
            tree.build(0, i, format!("user: m{i}"));
            view.append(i, &tree);
            assert_eq!(view.fit(i + 1, VIEW, &tree).len(), 0);
        }
        tree.build(1, 0, "merged".to_string());
        assert_eq!(view.fit(4, VIEW, &tree).len(), 0);
        assert_eq!(
            view.render(&tree),
            "<chat>\n0+1|user: m0\n1+1|user: m1\n2+1|user: m2\n3+1|user: m3\n</chat>"
        );
        // A compaction's view ends at its node.
        assert_eq!(
            view.render_built_until(2, &tree),
            "<chat>\n0+1|user: m0\n1+1|user: m1\n</chat>"
        );
    }

    #[test]
    fn render_flattens_newlines_and_names_lines_by_id_and_count() {
        let mut tree = Tree::default();
        let mut view = View::default();
        for i in 0..2 {
            tree.build(0, i, format!("talk: a\r\nb{i}"));
            view.append(i, &tree);
        }
        view.append(2, &tree);
        assert_eq!(
            (view.render(&tree), view.render_built_until(3, &tree)),
            (
                format!("<chat>\n0+1|talk: a b0\n1+1|talk: a b1\n2+1|{PLACEHOLDER}\n</chat>"),
                "<chat>\n0+1|talk: a b0\n1+1|talk: a b1\n</chat>".to_string()
            )
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
        assert_eq!(view.fit(total, VIEW, &tree).len(), 2);
        // 258 lines of 500 bytes need two merges; at equal levels the
        // oldest pair is the most due.
        assert_eq!(view.size(), VIEW);
        assert_eq!(coordinates(&view)[..3], [(1, 0), (1, 1), (0, 4)]);
    }

    /// Most due is oldest relative to size: a younger level-0 pair goes
    /// before an older level-1 pair whose parent is built too.
    #[test]
    fn the_most_due_pair_weighs_age_against_level() {
        let mut tree = Tree::default();
        let mut view = View::default();
        let line = || "x".repeat(500);
        let first = (VIEW / 500 + 2) as u64;
        for i in 0..first {
            tree.build(0, i, line());
            view.append(i, &tree);
        }
        tree.build(1, 0, line());
        tree.build(1, 1, line());
        assert_eq!(view.fit(first, VIEW, &tree).len(), 2);
        assert_eq!(coordinates(&view)[..3], [(1, 0), (1, 1), (0, 4)]);
        // One more message: one merge fits the view again. With T = 259,
        // the level-1 pair 0..4 is due (260 - 0)/2 = 130 and the level-0
        // pair 4..6 is due (260 - 4)/1 = 256: the younger pair is more due.
        tree.build(0, first, line());
        view.append(first, &tree);
        tree.build(2, 0, line());
        tree.build(1, 2, line());
        assert_eq!(view.fit(first + 1, VIEW, &tree).len(), 1);
        assert_eq!(
            (view.size(), coordinates(&view)[..4].to_vec()),
            (VIEW, vec![(1, 0), (1, 1), (1, 2), (0, 6)])
        );
    }

    /// The view only appends at its end and coarsens: every part of an
    /// earlier view lies inside one part of every later view, and the
    /// parts tile `[0, T)`.
    #[test]
    fn merged_parts_are_never_split() {
        let mut tree = Tree::default();
        let mut view = View::default();
        let mut before: Vec<Part> = Vec::new();
        for i in 0..600u64 {
            tree.build(0, i, "x".repeat(500));
            // Every parent is built once both its children are.
            let mut part = Part { l: 0, i };
            while part.i % 2 == 1 {
                part = Part {
                    l: part.l + 1,
                    i: part.i / 2,
                };
                tree.build(part.l, part.i, "y".repeat(400));
            }
            view.append(i, &tree);
            view.fit(i + 1, VIEW, &tree);
            let parts = view.parts();
            assert!(view.size() <= VIEW);
            assert_eq!((parts[0].start(), parts[parts.len() - 1].end()), (0, i + 1));
            assert!(parts
                .windows(2)
                .all(|pair| pair[0].end() == pair[1].start()));
            let mut at = 0;
            for old in &before {
                while parts[at].end() < old.end() {
                    at += 1;
                }
                let new = parts[at];
                assert!(
                    new.l >= old.l && new.start() <= old.start() && old.end() <= new.end(),
                    "{old:?} was split at message {i}"
                );
            }
            before = parts.to_vec();
        }
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
        assert_eq!(view.fit(total, VIEW, &tree).len(), 0);
        assert!(view.size() > VIEW);
    }

    #[test]
    fn placeholders_count_until_built() {
        let mut tree = Tree::default();
        let mut view = View::default();
        view.append(0, &tree);
        assert_eq!(
            (
                view.size(),
                view.settled(&tree),
                view.first_unbuilt(1, &tree),
                view.render(&tree)
            ),
            (
                PLACEHOLDER.len(),
                false,
                0,
                format!("<chat>\n0+1|{PLACEHOLDER}\n</chat>")
            )
        );
        tree.build(0, 0, "user: hi".to_string());
        view.part_built(Part { l: 0, i: 0 }, &tree);
        assert_eq!(
            (
                view.size(),
                view.settled(&tree),
                view.first_unbuilt(1, &tree)
            ),
            ("user: hi".len(), true, 1)
        );
    }

    #[test]
    fn due_weighs_age_against_level() {
        // Age 6 at level 0 (6/1 = 6) beats age 8 at level 1 (8/2 = 4).
        assert!(!more_due(8, 1, 6, 0));
        assert!(more_due(6, 0, 8, 1));
        // Ties keep the earlier (older) pair: strict comparison.
        assert!(!more_due(8, 1, 4, 0));
    }

    /// Taelin's rollback `push` (`rollback_state_list.js`): the kept states,
    /// newest first, with their `keep` bits.
    fn push(state: u64, states: &mut Vec<(bool, u64)>) {
        let mut carry = state;
        let mut at = 0;
        loop {
            match states.get_mut(at) {
                None => {
                    states.push((false, carry));
                    return;
                }
                Some((keep @ false, _)) => {
                    *keep = true;
                    return;
                }
                Some((keep @ true, kept)) => {
                    *keep = false;
                    carry = std::mem::replace(kept, carry);
                    at += 1;
                }
            }
        }
    }

    /// With push's list length as the budget, the view makes exactly push's
    /// merges at every step. Measuring due from a pair's first message
    /// broke this near ties (at T = 10 it merged `0+8` instead of `8+2`).
    #[test]
    fn fit_matches_the_rollback_push_at_every_step() {
        let mut tree = Tree::default();
        let mut view = View::default();
        let mut states = Vec::new();
        for t in 0..4_096u64 {
            tree.build(0, t, "x".to_string());
            let mut part = Part { l: 0, i: t };
            while part.i % 2 == 1 {
                part = Part {
                    l: part.l + 1,
                    i: part.i / 2,
                };
                tree.build(part.l, part.i, "x".to_string());
            }
            push(t, &mut states);
            view.append(t, &tree);
            view.fit(t + 1, states.len(), &tree);
            let starts: Vec<u64> = states.iter().rev().map(|(_, state)| *state).collect();
            let parts: Vec<u64> = view.parts().iter().map(|part| part.start()).collect();
            assert_eq!(parts, starts, "at t = {t}");
        }
    }

    #[test]
    fn pieces_end_the_marked_piece_at_the_last_whole_block() {
        let view = |lines: usize| {
            let mut text = String::from("<chat>\n");
            for at in 0..lines {
                let _ = writeln!(text, "{at}+1|l{at}");
            }
            text.push_str("</chat>");
            text
        };
        assert_eq!(
            (pieces(&view(3)), pieces(&view(9)), pieces(&view(8))),
            (
                vec![view(3)],
                vec![
                    "<chat>\n0+1|l0\n1+1|l1\n2+1|l2\n3+1|l3\n4+1|l4\n5+1|l5\n6+1|l6\n7+1|l7\n"
                        .to_string(),
                    "8+1|l8\n</chat>".to_string()
                ],
                vec![
                    "<chat>\n0+1|l0\n1+1|l1\n2+1|l2\n3+1|l3\n4+1|l4\n5+1|l5\n6+1|l6\n7+1|l7\n"
                        .to_string(),
                    "</chat>".to_string()
                ]
            )
        );
    }

    /// A saved view must tile the log from message 0 with real tree nodes;
    /// it may stop short of `T` (messages logged after its last save).
    #[test]
    fn tiled_end_accepts_only_contiguous_tree_nodes() {
        let part = |l, i| Part { l, i };
        assert_eq!(
            [
                tiled_end(&[part(2, 0), part(1, 2), part(0, 6)], 9),
                tiled_end(&[], 3),
                tiled_end(&[part(1, 0), part(0, 3)], 9),
                tiled_end(&[part(1, 0), part(1, 1)], 3),
            ],
            [Some(7), Some(0), None, None]
        );
    }

    #[test]
    fn flatten_turns_every_newline_into_one_space() {
        assert_eq!(flatten("a\r\nb\nc\rd"), "a b c d");
    }
}
