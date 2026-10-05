//! The in-memory chat: the message index, the built nodes, the view, and
//! the compactor's scheduling state. Pure logic over loaded data; the owner
//! (`service`) performs every read and write.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use super::store::{Loaded, MessageMeta, NodeRecord};
use super::view::{flatten, line_text, NodeTexts, Part, View};
use super::{labeled, Kind, JOBS, NODE};

/// The built nodes by part.
#[derive(Debug, Default)]
pub(crate) struct Nodes(HashMap<Part, Arc<str>>);

impl NodeTexts for Nodes {
    fn node_text(&self, part: Part) -> Option<&str> {
        self.0.get(&part).map(AsRef::as_ref)
    }
}

impl Nodes {
    pub(crate) fn len(&self) -> usize {
        self.0.len()
    }

    /// Every built node, in no particular order.
    pub(crate) fn iter(&self) -> impl Iterator<Item = (Part, &str)> {
        self.0.iter().map(|(part, text)| (*part, text.as_ref()))
    }
}

/// What building one node takes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Step {
    /// Compress message `i` (its text is read from disk).
    Compress { message: u64 },
    /// Merge two built children.
    Merge { left: Arc<str>, right: Arc<str> },
}

/// What `zoom(id, n)` resolves to before any disk read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Zoom {
    /// `n = 1`: the whole message `id`.
    Message(u64),
    /// The two lines under `id+n`, rendered.
    Lines(String),
    /// The arguments name no line.
    NoLine,
}

/// The chat state.
#[derive(Debug, Default)]
pub(crate) struct Chat {
    messages: Vec<MessageMeta>,
    nodes: Nodes,
    view: View,
    /// Merges whose children are built and that are not built yet,
    /// ordered by level, then index.
    ready: BTreeSet<Part>,
    busy: HashSet<Part>,
}

impl Chat {
    /// Build the state from a load: index the nodes, then fold the view
    /// again from message 0 (append + fit for every message in order).
    pub(crate) fn from_loaded(loaded: Loaded, problems: &mut Vec<String>) -> Chat {
        let total = loaded.messages.len() as u64;
        let mut chat = Chat {
            messages: loaded.messages,
            ..Chat::default()
        };
        for NodeRecord { l, i, text, .. } in loaded.nodes {
            let part = Part { l, i };
            // `(i+1)·2^l <= T` without overflow: `i < T >> l`.
            let fits = l < 64 && i < total >> l;
            if !fits {
                problems.push(format!(
                    "skipped node {l}/{i}: it lies past the {total} messages"
                ));
                continue;
            }
            if chat.nodes.0.contains_key(&part) {
                problems.push(format!(
                    "skipped a second copy of node {}+{}",
                    part.start(),
                    part.count()
                ));
                continue;
            }
            chat.nodes.0.insert(part, Arc::from(text));
        }
        let built: Vec<Part> = chat.nodes.0.keys().copied().collect();
        for part in built {
            chat.note_ready_parent(part);
        }
        for i in 0..total {
            chat.view.append(i, &chat.nodes);
            chat.view.fit(i + 1, &chat.nodes);
        }
        chat
    }

    pub(crate) fn total(&self) -> u64 {
        self.messages.len() as u64
    }

    pub(crate) fn message(&self, id: u64) -> Option<&MessageMeta> {
        usize::try_from(id)
            .ok()
            .and_then(|at| self.messages.get(at))
    }

    pub(crate) fn nodes(&self) -> &Nodes {
        &self.nodes
    }

    pub(crate) fn view(&self) -> &View {
        &self.view
    }

    pub(crate) fn busy_count(&self) -> usize {
        self.busy.len()
    }

    /// The first message whose view line is not built (`T` when none).
    pub(crate) fn first(&self) -> u64 {
        self.view.first_unbuilt(self.total(), &self.nodes)
    }

    pub(crate) fn settled(&self) -> bool {
        self.view.settled(&self.nodes)
    }

    /// A new message enters the log and the view. Returns its id.
    pub(crate) fn push_message(&mut self, meta: MessageMeta) -> u64 {
        let id = self.total();
        self.messages.push(meta);
        self.view.append(id, &self.nodes);
        self.view.fit(self.total(), &self.nodes);
        id
    }

    /// A node was built and saved: index it, release it, refit the view.
    pub(crate) fn insert_node(&mut self, part: Part, text: &str) {
        self.nodes.0.insert(part, Arc::from(text));
        self.ready.remove(&part);
        self.busy.remove(&part);
        self.note_ready_parent(part);
        self.view.part_built(part, &self.nodes);
        self.view.fit(self.total(), &self.nodes);
    }

    /// The parent of a built part becomes ready once its sibling is built.
    fn note_ready_parent(&mut self, part: Part) {
        if part.l >= 62 {
            return;
        }
        let sibling = Part {
            l: part.l,
            i: part.i ^ 1,
        };
        let parent = Part {
            l: part.l + 1,
            i: part.i / 2,
        };
        if self.nodes.0.contains_key(&sibling) && !self.nodes.0.contains_key(&parent) {
            self.ready.insert(parent);
        }
    }

    /// The nodes to start now, in the pump's order (level 0 first, then by
    /// level and index), within the free job slots: unbuilt, not running,
    /// sources built, and every view line before the node's end built.
    pub(crate) fn candidates(&self) -> Vec<Part> {
        let room = JOBS.saturating_sub(self.busy.len());
        let first = self.first();
        let mut out = Vec::new();
        if room == 0 {
            return out;
        }
        let compress = Part { l: 0, i: first };
        if first < self.total()
            && self.nodes.node_text(compress).is_none()
            && !self.busy.contains(&compress)
        {
            out.push(compress);
        }
        for part in &self.ready {
            if out.len() >= room {
                break;
            }
            if !self.busy.contains(part) && part.end() <= first {
                out.push(*part);
            }
        }
        out
    }

    /// The node is running (or waiting out its retry delay).
    pub(crate) fn mark_busy(&mut self, part: Part) {
        self.busy.insert(part);
    }

    /// The node's retry delay passed: it may start again.
    pub(crate) fn release(&mut self, part: Part) {
        self.busy.remove(&part);
    }

    /// How the node is built.
    pub(crate) fn step(&self, part: Part) -> Option<Step> {
        if part.l == 0 {
            return (part.i < self.total()).then_some(Step::Compress { message: part.i });
        }
        let left = Part {
            l: part.l - 1,
            i: part.i * 2,
        };
        let right = Part {
            l: part.l - 1,
            i: part.i * 2 + 1,
        };
        Some(Step::Merge {
            left: self.nodes.0.get(&left)?.clone(),
            right: self.nodes.0.get(&right)?.clone(),
        })
    }

    /// The compactor's context for a node: the bare view lines up to it. A
    /// level-0 node sees the lines before its message (the message comes
    /// whole in the step); a merge sees the lines up to its last message.
    pub(crate) fn context(&self, part: Part) -> String {
        let end = if part.l == 0 {
            part.start()
        } else {
            part.end()
        };
        self.view.render_context(end, &self.nodes)
    }

    /// The agent's view.
    pub(crate) fn render(&self) -> String {
        self.view.render(&self.nodes)
    }

    /// Resolve `zoom(id, n)`.
    pub(crate) fn zoom(&self, id: u64, count: u64) -> Zoom {
        let valid = count.is_power_of_two()
            && id % count == 0
            && id.checked_add(count).is_some_and(|end| end <= self.total());
        if !valid {
            return Zoom::NoLine;
        }
        if count == 1 {
            return Zoom::Message(id);
        }
        let l = count.trailing_zeros() - 1;
        let i = id / count * 2;
        let lines = [Part { l, i }, Part { l, i: i + 1 }]
            .iter()
            .map(|part| {
                format!(
                    "{}+{}|{}",
                    part.start(),
                    part.count(),
                    flatten(line_text(*part, &self.nodes))
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        Zoom::Lines(lines)
    }
}

/// The node text of a free node: a short message is its own line, and two
/// short children are their own merge. `None` when the model must write it.
pub(crate) fn free_text(kind_and_text: Option<(Kind, &str)>, step: &Step) -> Option<String> {
    let text = match (step, kind_and_text) {
        (Step::Compress { .. }, Some((kind, text))) => labeled(kind, text),
        (Step::Merge { left, right }, _) => format!("{left}\n{right}"),
        (Step::Compress { .. }, None) => return None,
    };
    (text.len() <= NODE).then_some(text)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn meta(kind: Kind) -> MessageMeta {
        MessageMeta {
            kind,
            size: 0,
            date: String::new(),
            file: 0,
            offset: 0,
            len: 0,
        }
    }

    fn chat_with(total: u64) -> Chat {
        let mut chat = Chat::default();
        for _ in 0..total {
            chat.push_message(meta(Kind::User));
        }
        chat
    }

    #[test]
    fn messages_compress_one_at_a_time_in_order() {
        let mut chat = chat_with(3);
        assert_eq!(chat.candidates(), vec![Part { l: 0, i: 0 }]);
        chat.mark_busy(Part { l: 0, i: 0 });
        assert!(chat.candidates().is_empty());
        chat.insert_node(Part { l: 0, i: 0 }, "user: a");
        assert_eq!(chat.candidates(), vec![Part { l: 0, i: 1 }]);
        chat.insert_node(Part { l: 0, i: 1 }, "user: b");
        // The merge of 0 and 1 runs alongside the compression of 2.
        assert_eq!(
            chat.candidates(),
            vec![Part { l: 0, i: 2 }, Part { l: 1, i: 0 }]
        );
    }

    #[test]
    fn merges_wait_for_their_whole_context() {
        let mut chat = chat_with(4);
        chat.insert_node(Part { l: 0, i: 0 }, "a");
        chat.insert_node(Part { l: 0, i: 1 }, "b");
        chat.insert_node(Part { l: 0, i: 3 }, "d");
        // 2 is unbuilt: the merge (1,1) covering 2..4 is not ready, and
        // (1,0) ends at 2 <= first = 2.
        assert_eq!(
            chat.candidates(),
            vec![Part { l: 0, i: 2 }, Part { l: 1, i: 0 }]
        );
        chat.insert_node(Part { l: 0, i: 2 }, "c");
        assert_eq!(
            chat.candidates(),
            vec![Part { l: 1, i: 0 }, Part { l: 1, i: 1 }]
        );
    }

    #[test]
    fn zoom_opens_lines_and_messages() {
        let mut chat = chat_with(4);
        for (i, text) in ["a", "b", "c\nd", "e"].iter().enumerate() {
            chat.insert_node(Part { l: 0, i: i as u64 }, text);
        }
        chat.insert_node(Part { l: 1, i: 0 }, "ab");
        assert_eq!(
            chat.zoom(0, 4),
            Zoom::Lines("0+2|ab\n2+2|(not summarized yet: zoom it)".to_string())
        );
        assert_eq!(chat.zoom(2, 2), Zoom::Lines("2+1|c d\n3+1|e".to_string()));
        assert_eq!(chat.zoom(3, 1), Zoom::Message(3));
        assert_eq!(chat.zoom(1, 2), Zoom::NoLine);
        assert_eq!(chat.zoom(0, 3), Zoom::NoLine);
        assert_eq!(chat.zoom(4, 1), Zoom::NoLine);
        assert_eq!(chat.zoom(0, 8), Zoom::NoLine);
    }

    #[test]
    fn free_nodes_need_no_model() {
        assert_eq!(
            free_text(Some((Kind::User, "hi")), &Step::Compress { message: 0 }),
            Some("user: hi".to_string())
        );
        assert_eq!(
            free_text(
                Some((Kind::Echo, &"x".repeat(NODE))),
                &Step::Compress { message: 0 }
            ),
            None
        );
        let step = Step::Merge {
            left: Arc::from("a"),
            right: Arc::from("b"),
        };
        assert_eq!(free_text(None, &step), Some("a\nb".to_string()));
    }

    #[test]
    fn a_reload_folds_the_same_view() {
        let mut chat = chat_with(2);
        chat.insert_node(Part { l: 0, i: 0 }, "a");
        let loaded = Loaded {
            messages: vec![meta(Kind::User), meta(Kind::Talk)],
            nodes: vec![
                NodeRecord {
                    l: 0,
                    i: 0,
                    text: "a".to_string(),
                    size: 1,
                },
                NodeRecord {
                    l: 3,
                    i: 0,
                    text: "foreign".to_string(),
                    size: 7,
                },
            ],
            problems: Vec::new(),
        };
        let mut problems = Vec::new();
        let reloaded = Chat::from_loaded(loaded, &mut problems);
        assert_eq!(problems.len(), 1);
        assert_eq!(reloaded.render(), chat.render());
        assert_eq!(reloaded.first(), 1);
    }
}
