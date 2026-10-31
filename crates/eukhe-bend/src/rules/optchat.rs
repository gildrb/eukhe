//! The chat memory's planner (spec/README.md M1, gist §3-§4): the model
//! `bend/optchat/`, stepper entry `bend/ffi_optchat.bend`.
//!
//! The planner lives in the compiled core: which lines the view and the
//! compaction view hold, which batch a message runs, which nodes the
//! compactor starts. The chat opens it from its loaded log, sends each
//! event as it happens (a message, a node built, a call started or freed,
//! a turn that starts to wait) and each query it needs (the nodes to
//! start, a compaction's view, how many calls run), and does what each
//! reply says (`optchat_step_is_model` in `laws/optchat.bend`). The chat
//! keeps the texts and tells the planner only their sizes.

use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{expect_core, Entry, Stepper};

/// A tree node: `(l, i)` covers the `2^l` messages from `i·2^l` on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Node {
    pub l: u32,
    pub i: u64,
}

/// The sizes the planner works with, in bytes of line text, and its job
/// slots (§3.2, §4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Sizes {
    /// A line whose message is not summarized yet.
    pub placeholder: usize,
    /// The view's sawtooth: past `ceiling`, a batch merges it down to
    /// `floor`.
    pub ceiling: usize,
    pub floor: usize,
    /// The compaction view's sawtooth.
    pub compaction_ceiling: usize,
    pub compaction_floor: usize,
    /// Compactor calls at once; also how many unbuilt lines may sit before
    /// a message whose node starts.
    pub jobs: usize,
}

/// How the log's last batch left the view.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LastBatch {
    /// At or under its floor (or no batch yet).
    Settled,
    /// Still over its floor: the next message merges what it can.
    Shrinking,
    /// Still over its floor, and the last message has no batch line (the
    /// owner died between the two writes): that batch runs at the open.
    Missed,
}

/// A batch that ran: its merged parents in merge order (maybe none), the
/// view after it, and whether the view is still over its floor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Batch {
    pub merged: Vec<Node>,
    pub view: Vec<Node>,
    pub shrinking: bool,
}

/// Who the compactor's next calls serve (H2.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Demand {
    /// No turn waits: the gist's order (§4).
    Background,
    /// A turn waits for the view: only the view's unbuilt lines start; the
    /// ready merges wait until the view settles.
    Turn,
}

/// The chat's planner, kept in the compiled core.
#[derive(Debug)]
pub struct Planner {
    stepper: Stepper,
}

impl Planner {
    /// The planner of a loaded chat: `total` messages, every built node
    /// with its size, the view folded from the log and how its last batch
    /// left it. A [`LastBatch::Missed`] batch runs now and comes back.
    pub fn open(
        sizes: Sizes,
        total: u64,
        built: impl ExactSizeIterator<Item = (Node, usize)>,
        view: impl ExactSizeIterator<Item = Node>,
        last: LastBatch,
    ) -> (Self, Option<Batch>) {
        let mut request = Writer::new();
        request
            .nat(saturate(sizes.placeholder))
            .nat(saturate(sizes.ceiling))
            .nat(saturate(sizes.floor))
            .nat(saturate(sizes.compaction_ceiling))
            .nat(saturate(sizes.compaction_floor))
            .nat(saturate(sizes.jobs))
            .nat(total)
            .count(built.len());
        for (node, size) in built {
            put_node(&mut request, node);
            request.nat(saturate(size));
        }
        request.count(view.len());
        for node in view {
            put_node(&mut request, node);
        }
        request
            .bool(last != LastBatch::Settled)
            .bool(last == LastBatch::Missed);
        let request = expect_core(Entry::Optchat, request.finish());
        let (stepper, reply) = expect_core(Entry::Optchat, Stepper::open(Entry::Optchat, &request));
        let batch = expect_core(Entry::Optchat, read_batch(&reply));
        (Planner { stepper }, batch)
    }

    /// Message `T` arrives: the batch it ran, if one ran (log it even when
    /// it merged nothing).
    pub fn message(&mut self) -> Option<Batch> {
        let reply = self.step(Writer::new().tag(0));
        expect_core(Entry::Optchat, read_batch(&reply))
    }

    /// Node `node` was built, `size` bytes.
    pub fn built(&mut self, node: Node, size: usize) {
        let mut request = Writer::new();
        request.tag(1);
        put_node(&mut request, node);
        request.nat(saturate(size));
        let reply = self.step(&mut request);
        expect_core(Entry::Optchat, read_done(&reply));
    }

    /// The node's call started (or failed, waiting to be tried again).
    pub fn started(&mut self, node: Node) {
        self.node_event(2, node);
    }

    /// The node may start again.
    pub fn freed(&mut self, node: Node) {
        self.node_event(3, node);
    }

    /// A turn starts to wait (H2.1): the calls it stops, which the chat's
    /// owner stops (in no particular order).
    pub fn hold(&mut self) -> Vec<Node> {
        let reply = self.step(Writer::new().tag(4));
        expect_core(Entry::Optchat, read_nodes(&reply))
    }

    /// The nodes to start now, within the free job slots, in order (§4
    /// "The order").
    pub fn candidates(&mut self, demand: Demand) -> Vec<Node> {
        let tag = match demand {
            Demand::Background => 5,
            Demand::Turn => 6,
        };
        let reply = self.step(Writer::new().tag(tag));
        expect_core(Entry::Optchat, read_nodes(&reply))
    }

    /// A compaction's view of `node` (§4): the compaction view's lines up
    /// to it, stopping at the first unbuilt line.
    pub fn context(&mut self, node: Node) -> Vec<Node> {
        let mut request = Writer::new();
        request.tag(7);
        put_node(&mut request, node);
        let reply = self.step(&mut request);
        expect_core(Entry::Optchat, read_nodes(&reply))
    }

    /// How many nodes are being built (or failed, waiting to be tried
    /// again).
    pub fn busy_count(&mut self) -> usize {
        let reply = self.step(Writer::new().tag(8));
        expect_core(Entry::Optchat, read_count(&reply))
    }

    fn node_event(&mut self, tag: u32, node: Node) {
        let mut request = Writer::new();
        request.tag(tag);
        put_node(&mut request, node);
        let reply = self.step(&mut request);
        expect_core(Entry::Optchat, read_done(&reply));
    }

    fn step(&mut self, request: &mut Writer) -> String {
        let request = expect_core(Entry::Optchat, request.finish());
        expect_core(Entry::Optchat, self.stepper.step(&request))
    }
}

/// A size on the wire: a text past [`NAT_MAX`] bytes (100 TB) cannot be
/// in memory, so the bound never changes a decision.
fn saturate(n: usize) -> u64 {
    u64::try_from(n).map_or(NAT_MAX, |n| n.min(NAT_MAX))
}

fn put_node(request: &mut Writer, node: Node) {
    request.nat(u64::from(node.l)).nat(node.i);
}

fn get_node(reader: &mut Reader<'_>) -> Result<Node, WireError> {
    let l = reader.u32()?;
    let i = reader.nat()?;
    Ok(Node { l, i })
}

fn get_nodes(reader: &mut Reader<'_>) -> Result<Vec<Node>, WireError> {
    let count = reader.count()?;
    (0..count).map(|_| get_node(reader)).collect()
}

fn read_nodes(reply: &str) -> Result<Vec<Node>, WireError> {
    let mut reader = Reader::reply(reply)?;
    let nodes = get_nodes(&mut reader)?;
    reader.end()?;
    Ok(nodes)
}

fn read_batch(reply: &str) -> Result<Option<Batch>, WireError> {
    let mut reader = Reader::reply(reply)?;
    // `tag_of` answers a tag below 2: 0 no batch ran, 1 a batch ran.
    let batch = if reader.tag_of(2, "a batch: none or ran")? == 0 {
        None
    } else {
        let merged = get_nodes(&mut reader)?;
        let view = get_nodes(&mut reader)?;
        let shrinking = reader.bool()?;
        Some(Batch {
            merged,
            view,
            shrinking,
        })
    };
    reader.end()?;
    Ok(batch)
}

fn read_done(reply: &str) -> Result<(), WireError> {
    let mut reader = Reader::reply(reply)?;
    reader.tag_of(1, "an event's answer: done")?;
    reader.end()
}

fn read_count(reply: &str) -> Result<usize, WireError> {
    let mut reader = Reader::reply(reply)?;
    let count = reader.count()?;
    reader.end()?;
    Ok(count)
}

#[cfg(test)]
mod tests {
    use super::{Batch, Demand, LastBatch, Node, Planner, Sizes};

    fn node(l: u32, i: u64) -> Node {
        Node { l, i }
    }

    /// The compiled core is reached: an open with a missed batch, each
    /// event and query (the rule itself is pinned by `laws/optchat.bend`).
    #[test]
    fn the_planner_runs_in_the_core() {
        let sizes = Sizes {
            placeholder: 10,
            ceiling: 40,
            floor: 20,
            compaction_ceiling: 30,
            compaction_floor: 10,
            jobs: 2,
        };
        let leaves = [node(0, 0), node(0, 1), node(0, 2)];
        let (mut planner, missed) = Planner::open(
            sizes,
            3,
            leaves.iter().map(|leaf| (*leaf, 5)),
            leaves.iter().copied(),
            LastBatch::Missed,
        );
        assert_eq!(
            missed,
            Some(Batch {
                merged: Vec::new(),
                view: leaves.to_vec(),
                shrinking: false
            })
        );
        assert_eq!(planner.message(), None);
        assert_eq!(
            planner.candidates(Demand::Background),
            [node(0, 3), node(1, 0)]
        );
        assert_eq!(planner.candidates(Demand::Turn), [node(0, 3)]);
        planner.started(node(1, 0));
        assert_eq!(planner.busy_count(), 1);
        assert_eq!(planner.hold(), [node(1, 0)]);
        assert_eq!(planner.busy_count(), 0);
        planner.started(node(0, 3));
        planner.freed(node(0, 3));
        planner.built(node(1, 0), 9);
        planner.built(node(0, 3), 5);
        assert_eq!(
            planner.context(node(1, 1)),
            [node(0, 0), node(0, 1), node(0, 2), node(0, 3)]
        );
        assert_eq!(planner.message(), None);
    }
}
