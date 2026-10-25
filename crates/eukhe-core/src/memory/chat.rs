//! The in-memory chat: the message index, the built nodes and the view
//! the agent reads. Which lines the view and the compaction view hold,
//! which batch a message runs and which nodes the compactor starts is the
//! planner's, a stepper of the compiled core
//! (`eukhe_bend::rules::optchat`, model `bend/optchat/`): the chat tells
//! it each event, asks it each question, and does what it answers. The
//! owner (`service`) performs every read and write.

#[cfg(test)]
mod tests;

use std::collections::HashMap;
use std::sync::Arc;

use eukhe_bend::rules::optchat::{self, Demand, LastBatch, Node, Planner, Sizes};

use super::store::{Loaded, MergeRecord, MessageMeta, NodeRecord};
use super::view::{flatten, line_text, render_parts, tiled_end, NodeTexts, Part, View};
use super::{labeled, Kind};
use super::{COMPACTION_CEILING, COMPACTION_FLOOR, JOBS, PLACEHOLDER, VIEW_CEILING, VIEW_FLOOR};

/// The byte budgets of the two sawtooths and the compactor's job slots
/// (§3.2, §4). Only tests set other values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Budgets {
    pub ceiling: usize,
    pub floor: usize,
    pub compaction_ceiling: usize,
    pub compaction_floor: usize,
    pub jobs: usize,
}

impl Default for Budgets {
    fn default() -> Budgets {
        Budgets {
            ceiling: VIEW_CEILING,
            floor: VIEW_FLOOR,
            compaction_ceiling: COMPACTION_CEILING,
            compaction_floor: COMPACTION_FLOOR,
            jobs: JOBS,
        }
    }
}

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

impl Step {
    /// The node's input (§2): the message, labeled (`message` reads it),
    /// or the two children joined by a newline. An input within
    /// [`super::NODE`] bytes is the node's line, with no model call.
    pub(crate) fn input(
        &self,
        message: impl FnOnce(u64) -> anyhow::Result<(Kind, String)>,
    ) -> anyhow::Result<String> {
        match self {
            Step::Compress { message: id } => message(*id).map(|(kind, text)| labeled(kind, &text)),
            Step::Merge { left, right } => Ok(format!("{left}\n{right}")),
        }
    }
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

/// One batch of the view's sawtooth (§3.2): at message `total - 1`,
/// merging `merged` (in order, maybe none) took the view from `before` to
/// `after` bytes; `open` when it is still over its floor, so the next
/// message merges what it can.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Batch {
    pub merged: Vec<Part>,
    pub before: usize,
    pub after: usize,
    pub open: bool,
    pub total: u64,
}

impl Batch {
    /// The batch as its `tree/` line.
    pub(crate) fn record(&self) -> MergeRecord {
        MergeRecord {
            open: self.open,
            t: Some(self.total),
            ..MergeRecord::of(&self.merged)
        }
    }
}

/// The chat state: the message index, the built nodes, the view, and the
/// planner that decides the view.
#[derive(Debug)]
pub(crate) struct Chat {
    messages: Vec<MessageMeta>,
    nodes: Nodes,
    /// The planner's view, with its size: it appends each message's line
    /// and takes the planner's view after each batch.
    view: View,
    planner: Planner,
}

impl Chat {
    /// Build the state from a load: index the nodes, then fold the view
    /// from the log's merge batches. The view is the live one: the same
    /// parts in the same order, and still shrinking when the last batch
    /// left it over its floor. Returns the `tree/` lines the log does not
    /// hold yet, which the owner appends:
    ///
    /// - a chat from before the merge batches were logged imports its
    ///   saved view once, as the merges that build it;
    /// - a shrinking view whose last message has no batch line (the owner
    ///   died between the two writes) runs that batch now.
    pub(crate) fn from_loaded(
        budgets: Budgets,
        loaded: Loaded,
        saved: Option<Vec<Part>>,
        problems: &mut Vec<String>,
    ) -> (Chat, Vec<MergeRecord>) {
        let total = loaded.messages.len() as u64;
        let mut nodes = Nodes::default();
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
            if nodes.0.contains_key(&part) {
                problems.push(format!(
                    "skipped a second copy of node {}+{}",
                    part.start(),
                    part.count()
                ));
                continue;
            }
            nodes.0.insert(part, Arc::from(text));
        }
        let logged: Vec<Part> = loaded
            .merges
            .iter()
            .flat_map(|record| record.merge.iter().map(|&(l, i)| Part { l, i }))
            .collect();
        let last = loaded.merges.last();
        let last_batch = match last {
            Some(record) if record.open && record.t < Some(total) => LastBatch::Missed,
            Some(record) if record.open => LastBatch::Shrinking,
            Some(_) | None => LastBatch::Settled,
        };
        let mut unlogged = Vec::new();
        let mut imported = Vec::new();
        if logged.is_empty() {
            if let Some(parts) = saved {
                if tiled_end(&parts, total).is_some() {
                    imported = merges_building(&parts);
                    unlogged.push(MergeRecord::of(&imported));
                } else {
                    problems.push(format!(
                        "the saved view does not tile the {total} messages: ignored it"
                    ));
                }
            }
        }
        let (view, skipped) = View::fold(total, logged.into_iter().chain(imported), &nodes);
        for part in skipped {
            problems.push(format!(
                "skipped the merge into {}+{}: its halves are not in the view",
                part.start(),
                part.count()
            ));
        }
        let sizes = Sizes {
            placeholder: PLACEHOLDER.len(),
            ceiling: budgets.ceiling,
            floor: budgets.floor,
            compaction_ceiling: budgets.compaction_ceiling,
            compaction_floor: budgets.compaction_floor,
            jobs: budgets.jobs,
        };
        let (planner, missed) = Planner::open(
            sizes,
            total,
            nodes
                .0
                .iter()
                .map(|(part, text)| (Node::from(*part), text.len())),
            view.parts().iter().map(|part| Node::from(*part)),
            last_batch,
        );
        let mut chat = Chat {
            messages: loaded.messages,
            nodes,
            view,
            planner,
        };
        if let Some(batch) = chat.took(missed, total) {
            unlogged.push(batch.record());
        }
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

    pub(crate) fn busy_count(&mut self) -> usize {
        self.planner.busy_count()
    }

    /// The first message whose view line is not built (`T` when none).
    pub(crate) fn first(&self) -> u64 {
        self.view.first_unbuilt(self.total(), &self.nodes)
    }

    pub(crate) fn settled(&self) -> bool {
        self.view.settled(&self.nodes)
    }

    /// A new message enters the log and the view. Returns its id and the
    /// batch it ran, if any (to log, even when it merged nothing).
    pub(crate) fn push_message(&mut self, meta: MessageMeta) -> (u64, Option<Batch>) {
        let id = self.total();
        self.messages.push(meta);
        self.view.append(id, &self.nodes);
        let batch = self.planner.message();
        (id, self.took(batch, id + 1))
    }

    /// The view after the planner's batch, if one ran, and the batch as the
    /// log keeps it.
    fn took(&mut self, batch: Option<optchat::Batch>, total: u64) -> Option<Batch> {
        let optchat::Batch {
            merged,
            view,
            shrinking,
        } = batch?;
        let before = self.view.size();
        self.view = View::of(view.into_iter().map(Part::from).collect(), &self.nodes);
        Some(Batch {
            merged: merged.into_iter().map(Part::from).collect(),
            before,
            after: self.view.size(),
            open: shrinking,
            total,
        })
    }

    /// A node was built and saved: index it and tell the planner. Neither
    /// view merges here: the view merges only when a message comes.
    pub(crate) fn insert_node(&mut self, part: Part, text: &str) {
        self.nodes.0.insert(part, Arc::from(text));
        self.planner.built(part.into(), text.len());
        self.view.part_built(part, &self.nodes);
    }

    /// The nodes to start now, within the free job slots, as the planner
    /// orders them (§4 "The order").
    pub(crate) fn candidates(&mut self, demand: Demand) -> Vec<Part> {
        parts(self.planner.candidates(demand))
    }

    /// The node is running (or failed, waiting to be tried again).
    pub(crate) fn mark_busy(&mut self, part: Part) {
        self.planner.started(part.into());
    }

    /// The node may start again.
    pub(crate) fn release(&mut self, part: Part) {
        self.planner.freed(part.into());
    }

    /// A turn starts to wait (H2.1): every busy node that is not a view
    /// line still unbuilt goes back to the queue, as the planner answers.
    /// Returns those that went back, so the owner stops their calls.
    pub(crate) fn hold_for_turn(&mut self) -> Vec<Part> {
        parts(self.planner.hold())
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

    /// A compaction's view of a node (§4), as the planner answers it: the
    /// compaction view's lines before the message (it comes whole in the
    /// task), or up to a merge's last message, stopping at the first
    /// unbuilt line.
    pub(crate) fn context(&mut self, part: Part) -> String {
        render_parts(&parts(self.planner.context(part.into())), &self.nodes)
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

fn parts(nodes: Vec<Node>) -> Vec<Part> {
    nodes.into_iter().map(Part::from).collect()
}
