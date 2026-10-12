//! The in-memory chat: the message index, the built nodes, the view and
//! the compaction view, and the compactor's scheduling state. Pure logic
//! over loaded data; the owner (`service`) performs every read and write.

#[cfg(test)]
mod tests;

use std::collections::{BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use super::store::{Loaded, MessageMeta, NodeRecord};
use super::view::{flatten, line_text, tiled_end, NodeTexts, Part, View};
use super::{
    labeled, Kind, COMPACTION_CEILING, COMPACTION_FLOOR, JOBS, NODE, VIEW_CEILING, VIEW_FLOOR,
};

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

/// One batch of the view's sawtooth (§3.2): merging `merged` (in order)
/// took the view from `before` to `after` bytes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Batch {
    pub merged: Vec<Part>,
    pub before: usize,
    pub after: usize,
}

/// The chat state.
#[derive(Debug, Default)]
pub(crate) struct Chat {
    messages: Vec<MessageMeta>,
    nodes: Nodes,
    view: View,
    /// The compactions' view (§4): the view merged further, to
    /// [`COMPACTION_FLOOR`]..[`COMPACTION_CEILING`] bytes.
    compaction: View,
    /// A batch could not reach [`VIEW_FLOOR`] yet (unbuilt parents): each
    /// new message merges what it can until it does.
    shrinking: bool,
    /// Merges whose children are built and that are not built yet,
    /// ordered by level, then index.
    ready: BTreeSet<Part>,
    busy: HashSet<Part>,
}

impl Chat {
    /// Build the state from a load: index the nodes, then fold the view
    /// from the log's merge batches. Returns the merges the log does not
    /// hold yet, which the owner appends:
    ///
    /// - a chat from before the merge batches were logged imports its
    ///   saved view once, as the merges that build it;
    /// - a view over its ceiling (the owner died between a message and its
    ///   batch) merges its batch now.
    pub(crate) fn from_loaded(
        loaded: Loaded,
        saved: Option<Vec<Part>>,
        problems: &mut Vec<String>,
    ) -> (Chat, Vec<Part>) {
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
        let logged: Vec<Part> = loaded
            .merges
            .iter()
            .flat_map(|record| record.merge.iter().map(|&(l, i)| Part { l, i }))
            .collect();
        let mut unlogged = Vec::new();
        if logged.is_empty() {
            if let Some(parts) = saved {
                if tiled_end(&parts, total).is_some() {
                    unlogged = merges_building(&parts);
                } else {
                    problems.push(format!(
                        "the saved view does not tile the {total} messages: ignored it"
                    ));
                }
            }
        }
        let (view, skipped) = View::fold(
            total,
            logged.into_iter().chain(unlogged.clone()),
            &chat.nodes,
        );
        for part in skipped {
            problems.push(format!(
                "skipped the merge into {}+{}: its halves are not in the view",
                part.start(),
                part.count()
            ));
        }
        chat.view = view;
        if chat.view.size() > VIEW_CEILING {
            unlogged.extend(chat.view.fit(total, VIEW_FLOOR, &chat.nodes));
            chat.shrinking = chat.view.size() > VIEW_FLOOR;
        }
        chat.compaction = chat.view.clone();
        chat.compaction.fit(total, COMPACTION_FLOOR, &chat.nodes);
        (chat, unlogged)
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

    /// A new message enters the log and the view. Returns its id and the
    /// batch it set off, if any.
    pub(crate) fn push_message(&mut self, meta: MessageMeta) -> (u64, Option<Batch>) {
        let id = self.total();
        self.messages.push(meta);
        (id, self.grow(id))
    }

    /// Message `id` (already indexed) appends its line to both views; the
    /// view merges in batches (§3.2): once it passes [`VIEW_CEILING`], down
    /// to [`VIEW_FLOOR`], and while that floor is out of reach (unbuilt
    /// parents), as far as it can at every message after. The compaction
    /// view merges with it, else on its own past [`COMPACTION_CEILING`].
    fn grow(&mut self, id: u64) -> Option<Batch> {
        let total = id + 1;
        self.view.append(id, &self.nodes);
        self.compaction.append(id, &self.nodes);
        if self.view.size() > VIEW_CEILING {
            self.shrinking = true;
        }
        if !self.shrinking {
            self.fit_compaction(total);
            return None;
        }
        let before = self.view.size();
        let merged = self.view.fit(total, VIEW_FLOOR, &self.nodes);
        if self.view.size() <= VIEW_FLOOR {
            self.shrinking = false;
        }
        if merged.is_empty() {
            self.fit_compaction(total);
            return None;
        }
        // The chat's view merged: the compaction view starts again from it.
        self.compaction = self.view.clone();
        self.compaction.fit(total, COMPACTION_FLOOR, &self.nodes);
        Some(Batch {
            merged,
            before,
            after: self.view.size(),
        })
    }

    /// The compaction view's own sawtooth: past its ceiling, down to its
    /// floor.
    fn fit_compaction(&mut self, total: u64) {
        if self.compaction.size() > COMPACTION_CEILING {
            self.compaction.fit(total, COMPACTION_FLOOR, &self.nodes);
        }
    }

    /// A node was built and saved: index it and release it. Neither view
    /// merges here: the view merges only when a message comes.
    pub(crate) fn insert_node(&mut self, part: Part, text: &str) {
        self.nodes.0.insert(part, Arc::from(text));
        self.ready.remove(&part);
        self.busy.remove(&part);
        self.note_ready_parent(part);
        self.view.part_built(part, &self.nodes);
        self.compaction.part_built(part, &self.nodes);
        self.fit_compaction(self.total());
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

    /// The nodes to start now, within the free job slots (§4 "The order"):
    /// a message's node once fewer than [`JOBS`] view lines before it are
    /// unbuilt, oldest first; then the ready merges (both halves built),
    /// from the queue, never from a scan of the tree.
    pub(crate) fn candidates(&self) -> Vec<Part> {
        let room = JOBS.saturating_sub(self.busy.len());
        let mut out = Vec::new();
        if room == 0 {
            return out;
        }
        let parts = self.view.parts();
        let first = self.first();
        let from = parts.partition_point(|part| part.start() < first);
        let mut unbuilt_before = 0;
        for part in &parts[from..] {
            if unbuilt_before >= JOBS || out.len() >= room {
                break;
            }
            if self.nodes.node_text(*part).is_some() {
                continue;
            }
            if !self.busy.contains(part) {
                out.push(*part);
            }
            unbuilt_before += 1;
        }
        for part in &self.ready {
            if out.len() >= room {
                break;
            }
            if !self.busy.contains(part) {
                out.push(*part);
            }
        }
        out
    }

    /// The node is running (or waiting out its retry delay).
    pub(crate) fn mark_busy(&mut self, part: Part) {
        self.busy.insert(part);
    }

    /// The node may start again.
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

    /// A compaction's view of a node (§4): the compaction view's lines
    /// before the message (it comes whole in the task), or up to a merge's
    /// last message, stopping at the first unbuilt line.
    pub(crate) fn context(&self, part: Part) -> String {
        let end = if part.l == 0 {
            part.start()
        } else {
            part.end()
        };
        self.compaction.render_built_until(end, &self.nodes)
    }

    /// The agent's view.
    pub(crate) fn render(&self) -> String {
        self.view.render(&self.nodes)
    }

    /// Resolve `zoom(id, n)`.
    pub(crate) fn zoom(&self, id: u64, count: u64) -> Zoom {
        let valid = count.is_power_of_two()
            && id.is_multiple_of(count)
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

/// The merges that build `parts` from single messages: each part's inner
/// nodes, level by level.
fn merges_building(parts: &[Part]) -> Vec<Part> {
    let mut merges = Vec::new();
    for part in parts {
        for l in 1..=part.l {
            let first = part.start() >> l;
            merges.extend((first..first + (1 << (part.l - l))).map(|i| Part { l, i }));
        }
    }
    merges
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
