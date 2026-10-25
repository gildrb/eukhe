//! The view: tree nodes ("parts") tiling the whole chat `[0, T)`, oldest
//! first. It only ever appends at its end, and coarsens by merging the most
//! due adjacent pairs in batches (§3.2); a merged part is never split again,
//! so consecutive views share their start and the request prefix stays
//! cacheable.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use eukhe_bend::rules::optchat::Node;

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

/// A node as the planner names it.
impl From<Part> for Node {
    fn from(part: Part) -> Node {
        Node {
            l: part.l,
            i: part.i,
        }
    }
}

impl From<Node> for Part {
    fn from(node: Node) -> Part {
        Part {
            l: node.l,
            i: node.i,
        }
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
        (View::of(by_start.into_values().collect(), tree), skipped)
    }

    /// The view of `parts`, with its size.
    pub(crate) fn of(parts: Vec<Part>, tree: &impl NodeTexts) -> View {
        let size = parts.iter().map(|part| line_text(*part, tree).len()).sum();
        View { parts, size }
    }

    pub(crate) fn parts(&self) -> &[Part] {
        &self.parts
    }

    /// Whether `part` is a line of the view (the lines are in order).
    pub(crate) fn contains(&self, part: Part) -> bool {
        self.parts
            .binary_search_by_key(&part.start(), |known| known.start())
            .is_ok_and(|at| self.parts[at] == part)
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
        if part.l == 0 && self.contains(part) {
            self.size = self.size - PLACEHOLDER.len() + line_text(part, tree).len();
        }
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

    /// The agent's rendering ([`render_parts`]).
    pub(crate) fn render(&self, tree: &impl NodeTexts) -> String {
        render_parts(&self.parts, tree)
    }
}

/// `<chat>`, one `id+n|text` line per part (newlines shown as spaces),
/// `</chat>`.
pub(crate) fn render_parts(parts: &[Part], tree: &impl NodeTexts) -> String {
    let mut out = String::from("<chat>\n");
    for part in parts {
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

/// The merge order, the sawtooth and the rendering are secured by the
/// Bend laws (`laws/optchat.bend`, `PROOF.bend`) of the planner this view
/// takes its lines from; these cover what the model leaves out.
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
