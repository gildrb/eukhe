//! Agent messaging in a tree (`bend/kin.bend`, entry `bend/ffi_kin.bend`;
//! `laws/kin.bend`, spec `spec/agents/kin.bend`): an agent messages only
//! its parent and its own children, never itself. An admitted message
//! always lands in the target's inbox: queued while the target is busy,
//! delivered when it is idle, delivered after a wake when it is parked.

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// An edge of the agent tree: `parent` spawned `child`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Edge<'a> {
    /// The spawned agent.
    pub child: &'a str,
    /// The agent that spawned it.
    pub parent: &'a str,
}

/// A message to admit: who sends it, to whom, in which tree.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Message<'a> {
    /// The sending agent.
    pub sender: &'a str,
    /// The agent the message is for.
    pub target: &'a str,
    /// Every edge of the tree the sender knows.
    pub edges: &'a [Edge<'a>],
}

/// What the target is, seen from the sender.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Relation {
    /// The target spawned the sender.
    Parent,
    /// The sender spawned the target.
    Child,
}

/// The decision on a message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Admission {
    /// The message may go: the target is the sender's parent or child.
    Admit(Relation),
    /// The message may not go; the text says why (the error the sender sees).
    Refuse(String),
}

/// The target's state when an admitted message reaches it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TargetState {
    /// It is running a turn.
    Busy,
    /// It is live and waiting for input.
    Idle,
    /// It is parked: no worker runs it.
    Parked,
}

/// How an admitted message reaches the target's inbox.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Landing {
    /// Queued; the target reads it after its turn.
    Queue,
    /// Delivered now.
    Deliver,
    /// The target is woken, then the message is delivered.
    WakeThenDeliver,
}

/// The decision on `message`, from the compiled core.
#[must_use]
pub fn admit(message: &Message<'_>) -> Admission {
    expect_core(Entry::Kin, admit_call(message))
}

fn admit_call(message: &Message<'_>) -> Result<Admission, Error> {
    let mut request = Writer::new();
    request
        .tag(0)
        .str(message.sender)
        .str(message.target)
        .count(message.edges.len());
    for edge in message.edges {
        request.str(edge.child);
    }
    request.count(message.edges.len());
    for edge in message.edges {
        request.str(edge.parent);
    }
    let reply = call(Entry::Kin, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let admission = if reader.tag_of(2, "a kin verdict")? == 0 {
        Admission::Admit(if reader.tag_of(2, "a kin relation")? == 0 {
            Relation::Parent
        } else {
            Relation::Child
        })
    } else {
        Admission::Refuse(reader.str()?.to_owned())
    };
    reader.end()?;
    Ok(admission)
}

/// How an admitted message reaches a target in `state`, from the compiled
/// core.
#[must_use]
pub fn land(state: TargetState) -> Landing {
    expect_core(Entry::Kin, land_call(state))
}

fn land_call(state: TargetState) -> Result<Landing, Error> {
    let code = match state {
        TargetState::Busy => 0,
        TargetState::Idle => 1,
        TargetState::Parked => 2,
    };
    let reply = call(Entry::Kin, &Writer::new().tag(1).tag(code).finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let tag = reader.tag_of(3, "a kin landing")?;
    reader.end()?;
    Ok(if tag == 0 {
        Landing::Queue
    } else if tag == 1 {
        Landing::Deliver
    } else {
        Landing::WakeThenDeliver
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The decisions come from the compiled core, in the tree root -> a,
    /// root -> b, a -> c and a second tree y -> x: a child reaches its
    /// parent, a parent its child; a sibling, a grandparent, the agent
    /// itself and an agent of the other tree are refused.
    #[test]
    fn the_core_decides_who_may_message_whom() {
        let edge = |child, parent| Edge { child, parent };
        let edges = [
            edge("a", "root"),
            edge("b", "root"),
            edge("c", "a"),
            edge("x", "y"),
        ];
        let message = |sender, target| {
            admit(&Message {
                sender,
                target,
                edges: &edges,
            })
        };
        let refused = |text: &str| Admission::Refuse(text.to_owned());
        let not_kin = "agents message only their parent and their own children";
        assert_eq!(
            [
                message("a", "root"),
                message("root", "a"),
                message("a", "b"),
                message("c", "root"),
                message("a", "a"),
                message("x", "a"),
            ],
            [
                Admission::Admit(Relation::Parent),
                Admission::Admit(Relation::Child),
                refused(not_kin),
                refused(not_kin),
                refused("an agent cannot message itself"),
                refused(not_kin),
            ]
        );
    }

    /// Every state lands the message in the inbox, from the compiled core:
    /// busy queues, idle delivers, parked wakes then delivers.
    #[test]
    fn the_core_lands_a_message_in_every_state() {
        assert_eq!(
            [
                land(TargetState::Busy),
                land(TargetState::Idle),
                land(TargetState::Parked),
            ],
            [Landing::Queue, Landing::Deliver, Landing::WakeThenDeliver]
        );
    }
}
