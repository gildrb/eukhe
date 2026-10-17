//! The bridge between the session tree ([`super::SessionTree`],
//! [`super::Journal`]) and its Bend model (`bend/tree.bend`, whose laws
//! `PROOF.bend` proves): both run the same scenarios and must print the
//! same transcript, byte for byte.
//!
//! A scenario is a list of events (`bend/bridge_tree.bend` documents the
//! format): checked puts and deletes, saves, rewinds to a save, raw
//! rewinds, and replays of the journal. The driver below pushes each
//! record into a [`Journal`] and prints the live tree; a replay prints
//! [`Journal::replay`] of every record so far.
//!
//! [`compare`] runs it (and skips without `bend`, unless
//! `EUKHE_REQUIRE_BEND` is set).

use std::collections::BTreeSet;
use std::fmt::Write as _;

use super::{Applied, Journal, NodeId, RewindEffect, SessionTree, TreeOp, TreeRecord};
use crate::testing::bridge::{compare, Rng, Scenario};

/// The largest node id of a scenario.
const KEYS: u64 = 12;
/// The largest value of a scenario.
const VALUES: u64 = 4;

/// A case the scenarios must reach, so that the bridge checks every rule
/// of the model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Case {
    /// A checked put with a bad parent.
    RejectedPut,
    /// A delete of a node with a grandchild.
    DeepPrune,
    /// A raw rewind whose result is not sound.
    RejectedRewind,
    /// A raw rewind whose result is sound.
    AcceptedRewind,
    /// A delete of the root, rejected while the tree has nodes.
    RejectedRootDel,
    /// A rewind to a save that starts, stops and restores nodes.
    EveryEffect,
}

/// The cases the scenarios reached.
type Reached = BTreeSet<Case>;

/// One scenario as it runs: the journal, the saves, and both texts.
struct Run {
    journal: Journal<u64>,
    saves: Vec<SessionTree<u64>>,
    events: String,
    transcript: String,
}

impl Run {
    /// Print the live tree after `head`.
    fn show_tree(&mut self, head: &str) {
        self.transcript.push_str(head);
        for (id, node) in self.journal.tree().iter() {
            let _ = write!(
                self.transcript,
                " {}:{}:{}",
                id.0, node.parent.0, node.value
            );
        }
        self.transcript.push('\n');
    }

    /// Push `record` and print the tree after it.
    fn record(&mut self, record: TreeRecord<u64>) -> Applied {
        let applied = self.journal.push(record);
        self.show_tree("t");
        applied
    }

    /// `p K P V`: a checked put.
    fn put(&mut self, rng: &mut Rng, reached: &mut Reached) {
        let id = rng.range(1, KEYS);
        let parent = if rng.chance(75) {
            let mut below = vec![0];
            below.extend(
                self.journal
                    .tree()
                    .iter()
                    .map(|(key, _)| key.0)
                    .filter(|key| *key < id),
            );
            rng.pick(&below).unwrap_or(0)
        } else {
            rng.range(0, KEYS)
        };
        let value = rng.range(0, VALUES);
        let _ = writeln!(self.events, "p {id} {parent} {value}");
        let applied = self.record(TreeRecord::Do(TreeOp::Put {
            id: NodeId(id),
            parent: NodeId(parent),
            value,
        }));
        if applied == Applied::Rejected {
            reached.insert(Case::RejectedPut);
        }
    }

    /// `d K`: a delete of a node, of an id that is not a node, or (a few
    /// percent) of the root.
    fn del(&mut self, rng: &mut Rng, reached: &mut Reached) {
        let keys: Vec<u64> = self.journal.tree().iter().map(|(key, _)| key.0).collect();
        let id = if rng.chance(5) {
            NodeId::ROOT.0
        } else {
            match rng.pick(&keys) {
                Some(key) if rng.chance(75) => key,
                Some(_) | None => rng.range(1, KEYS),
            }
        };
        let tree = self.journal.tree();
        let deep = tree.contains(NodeId(id))
            && tree
                .children(NodeId(id))
                .any(|(child, _)| tree.children(child).next().is_some());
        if deep {
            reached.insert(Case::DeepPrune);
        }
        let populated = !tree.is_empty();
        let _ = writeln!(self.events, "d {id}");
        let applied = self.record(TreeRecord::Do(TreeOp::Del { id: NodeId(id) }));
        if id == NodeId::ROOT.0 && applied == Applied::Rejected && populated {
            reached.insert(Case::RejectedRootDel);
        }
    }

    /// `s`: save the tree.
    fn save(&mut self) {
        self.events.push_str("s\n");
        let _ = writeln!(self.transcript, "s {}", self.saves.len());
        self.saves.push(self.journal.tree().clone());
    }

    /// `b N`: rewind to save `N`; print the diff, then the tree. Without
    /// a save it saves instead.
    fn back(&mut self, rng: &mut Rng, reached: &mut Reached) {
        let Some(count) = u64::try_from(self.saves.len())
            .ok()
            .filter(|count| *count > 0)
        else {
            self.save();
            return;
        };
        let at = usize::try_from(rng.below(count)).unwrap_or(0);
        let _ = writeln!(self.events, "b {at}");
        let target = &self.saves[at];
        let tree = self.journal.tree();
        let effects = tree.rewind_effects(target);
        let every = effects.iter().any(|e| matches!(e, RewindEffect::Start(_)))
            && effects.iter().any(|e| matches!(e, RewindEffect::Stop(_)))
            && effects
                .iter()
                .any(|e| matches!(e, RewindEffect::Restore(_)));
        if every {
            reached.insert(Case::EveryEffect);
        }
        let ops = tree.diff(target);
        assert_eq!(tree.rewind_to(target), TreeRecord::Rewind(ops.clone()));
        assert_eq!(effects.len(), ops.len());
        self.transcript.push('w');
        for op in &ops {
            match op {
                TreeOp::Put { id, parent, value } => {
                    let _ = write!(self.transcript, " +{}:{}:{value}", id.0, parent.0);
                }
                TreeOp::Del { id } => {
                    let _ = write!(self.transcript, " -{}", id.0);
                }
            }
        }
        self.transcript.push('\n');
        self.record(TreeRecord::Rewind(ops));
    }

    /// `x OPS`: a raw rewind. Half of them are a save's diff with some
    /// noise, the others random ops; some orphan a node or hang it under
    /// a larger id, and the tree rejects them.
    fn raw(&mut self, rng: &mut Rng, reached: &mut Reached) {
        let count = u64::try_from(self.saves.len()).unwrap_or(0);
        let mut ops = if count > 0 && rng.chance(50) {
            let at = usize::try_from(rng.below(count)).unwrap_or(0);
            self.journal.tree().diff(&self.saves[at])
        } else {
            Vec::new()
        };
        for _ in 0..rng.below(4) {
            let id = rng.range(1, KEYS);
            let op = if rng.chance(55) {
                TreeOp::Put {
                    id: NodeId(id),
                    parent: NodeId(rng.range(0, KEYS)),
                    value: rng.range(0, VALUES),
                }
            } else {
                TreeOp::Del { id: NodeId(id) }
            };
            let room = u64::try_from(ops.len()).unwrap_or(0) + 1;
            let at = usize::try_from(rng.below(room)).unwrap_or(0);
            ops.insert(at, op);
        }
        self.events.push('x');
        for op in &ops {
            match op {
                TreeOp::Put { id, parent, value } => {
                    let _ = write!(self.events, " P {} {} {value}", id.0, parent.0);
                }
                TreeOp::Del { id } => {
                    let _ = write!(self.events, " D {}", id.0);
                }
            }
        }
        self.events.push('\n');
        reached.insert(match self.record(TreeRecord::Rewind(ops)) {
            Applied::Accepted => Case::AcceptedRewind,
            Applied::Rejected => Case::RejectedRewind,
        });
    }

    /// `j`: replay every record so far.
    fn replay(&mut self) {
        self.events.push_str("j\n");
        let tree = Journal::replay(self.journal.records());
        assert_eq!(&tree, self.journal.tree());
        assert_eq!(
            &self.journal.snapshot_at(self.journal.records().len()),
            self.journal.tree()
        );
        self.transcript.push('j');
        for (id, node) in tree.iter() {
            let _ = write!(
                self.transcript,
                " {}:{}:{}",
                id.0, node.parent.0, node.value
            );
        }
        self.transcript.push('\n');
    }
}

/// One scenario of 40 to 80 events.
fn scenario(rng: &mut Rng, reached: &mut Reached) -> (String, String) {
    let mut run = Run {
        journal: Journal::new(),
        saves: Vec::new(),
        events: String::new(),
        transcript: String::new(),
    };
    for _ in 0..rng.range(40, 80) {
        match rng.below(100) {
            0..=39 => run.put(rng, reached),
            40..=54 => run.del(rng, reached),
            55..=64 => run.save(),
            65..=76 => run.back(rng, reached),
            77..=91 => run.raw(rng, reached),
            92.. => run.replay(),
        }
        if rng.chance(2) {
            run.events.push('\n');
        }
    }
    (run.events, run.transcript)
}

#[test]
fn the_rust_tree_equals_the_bend_model() {
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    let mut reached = Reached::new();
    let scenarios: Vec<Scenario> = (0..300)
        .map(|at| {
            let (events, transcript) = scenario(&mut rng, &mut reached);
            Scenario {
                name: format!("tree {at}"),
                events,
                transcript,
            }
        })
        .collect();
    compare("bend/bridge_tree.bend", scenarios);
    // The scenarios reach every rule of the model.
    assert_eq!(
        reached,
        Reached::from([
            Case::RejectedPut,
            Case::DeepPrune,
            Case::RejectedRewind,
            Case::AcceptedRewind,
            Case::RejectedRootDel,
            Case::EveryEffect,
        ])
    );
}
