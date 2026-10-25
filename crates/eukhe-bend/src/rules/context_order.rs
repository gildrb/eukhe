//! What the model context of one conversation is made of, by index
//! (`bend/context_order.bend`, entry `bend/ffi_context_order.bend`;
//! `laws/context_order.bend`): the order of the messages a request sends
//! (each assistant's tool results right after it in call order, a missing
//! one synthesized, the others dropped), where its settled part ends, which
//! system message leads, which entries of a range are active and what each
//! contributes, and whether entries added to a range derive it again. The
//! caller gives each message's facts ([`Fact`]: its kind, an assistant's
//! stop reason and calls, a result's call; call ids interned to numbers,
//! equal ids equal numbers) and acts on the indices it gets back; every
//! index is checked against the facts it names.

use eukhe_types::pi_ai::StopReason;

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// A message as the core sees it (`Co.Msg`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fact {
    User,
    System,
    /// An assistant answer: its stop reason and its tool calls' ids, in
    /// order.
    Assistant {
        stop: StopReason,
        calls: Vec<u64>,
    },
    /// A tool result: its call's id.
    Result {
        call: u64,
    },
}

/// The role of a message of the context (`Co.Role`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    User,
    System,
    Assistant,
    Result,
}

/// A message of the order (`Co.Step`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Step {
    /// The message at this index.
    Take(usize),
    /// The missing result of call `call` (its position among the calls) of
    /// the assistant at `assistant`.
    Missing { assistant: usize, call: usize },
}

/// The order of some messages and where its settled part ends (`Co.Plan`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan {
    /// The index of the last assistant when it is not the first message:
    /// the messages from it on stay open.
    pub split: Option<usize>,
    /// How many of `steps`, from the first, the messages before the split
    /// give: they never change again.
    pub settles: usize,
    pub steps: Vec<Step>,
}

/// The newest edit of an entry in its range (`Co.Edit`).
#[derive(Clone, Copy, Debug)]
pub enum Edit<'a> {
    None,
    Omit,
    /// The facts of the messages that replace the entry's own.
    Replace(&'a [Fact]),
}

/// An entry of a range (`Co.Ent`).
#[derive(Clone, Copy, Debug)]
pub struct Ranged<'a> {
    /// Whether it is a head marker.
    pub head: bool,
    pub edit: Edit<'a>,
    /// The facts of its own messages.
    pub own: &'a [Fact],
}

/// What an active entry contributes (`Co.Keep`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Keep {
    Omitted,
    /// Its own messages at these indices.
    Own(Vec<usize>),
    /// Its Replace edit's messages at these indices.
    Replaced(Vec<usize>),
}

/// An active entry: its index among the entries asked about, and what it
/// contributes (`Co.Part`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Part {
    pub at: usize,
    pub keep: Keep,
}

/// An entry added after a range's tail (`Co.Add`).
#[derive(Clone, Copy, Debug)]
pub struct Added<'a> {
    /// Whether it carries edits.
    pub edits: bool,
    /// Whether it is a head marker.
    pub head: bool,
    /// Whether an edit of the range targets it.
    pub edited: bool,
    /// The facts of its own messages.
    pub own: &'a [Fact],
}

/// What entries added to a range give (`Co.Extended`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Extension {
    /// Derive the whole range again.
    Rederive,
    /// The indices of the own messages each added entry keeps, and the plan
    /// of the open messages followed by the kept ones.
    Extend { keeps: Vec<Vec<usize>>, plan: Plan },
}

/// The order of the messages `facts` (Rust `order_tool_results`).
///
/// # Panics
/// When the compiled core fails (an inconsistent build).
#[must_use]
pub fn order(facts: &[Fact]) -> Vec<Step> {
    expect_core(Entry::ContextOrder, call_order(facts))
}

/// The active entries of a range, in increasing order, and the plan of the
/// messages they contribute; with a head `marker` the first entry is the
/// marker and the others the range.
///
/// # Panics
/// When the compiled core fails (an inconsistent build).
#[must_use]
pub fn derive(marker: bool, entries: &[Ranged<'_>]) -> (Vec<Part>, Plan) {
    expect_core(Entry::ContextOrder, call_derive(marker, entries))
}

/// What the entries `added` after a range whose open messages are `open`
/// give.
///
/// # Panics
/// When the compiled core fails (an inconsistent build).
#[must_use]
pub fn extend(added: &[Added<'_>], open: &[Fact]) -> Extension {
    expect_core(Entry::ContextOrder, call_extend(added, open))
}

/// The index of the system message that moves to the front of the
/// messages whose roles are `roles`, if one does.
///
/// # Panics
/// When the compiled core fails (an inconsistent build).
#[must_use]
pub fn lead(roles: &[Role]) -> Option<usize> {
    expect_core(Entry::ContextOrder, call_lead(roles))
}

/// The wire tag of a stop reason (`Co.Stop`).
pub(crate) fn stop_tag(stop: StopReason) -> u32 {
    match stop {
        StopReason::Pending => 0,
        StopReason::Stop => 1,
        StopReason::Length => 2,
        StopReason::ToolUse => 3,
        StopReason::Error => 4,
        StopReason::Aborted => 5,
        StopReason::Deferred => 6,
    }
}

/// A list of messages' facts (`List<Co.Msg>`).
pub(crate) fn put_facts(request: &mut Writer, facts: &[Fact]) {
    request.count(facts.len());
    for fact in facts {
        match fact {
            Fact::User => {
                request.tag(0);
            }
            Fact::System => {
                request.tag(1);
            }
            Fact::Assistant { stop, calls } => {
                request.tag(2).tag(stop_tag(*stop)).count(calls.len());
                for id in calls {
                    request.nat(*id);
                }
            }
            Fact::Result { call } => {
                request.tag(3).nat(*call);
            }
        }
    }
}

fn malformed(expected: &'static str) -> WireError {
    WireError::Malformed { at: 0, expected }
}

/// An index below `len`.
fn index(reply: &mut Reader<'_>, len: usize, expected: &'static str) -> Result<usize, WireError> {
    usize::try_from(reply.nat()?)
        .ok()
        .filter(|&index| index < len)
        .ok_or(malformed(expected))
}

/// The steps of an order over the messages `seq`.
fn read_steps(reply: &mut Reader<'_>, seq: &[&Fact]) -> Result<Vec<Step>, WireError> {
    let count = reply.count()?;
    let mut steps = Vec::with_capacity(count);
    for _ in 0..count {
        let missing = reply.tag_of(2, "a step")? == 1;
        steps.push(if missing {
            let assistant = index(reply, seq.len(), "an assistant's index")?;
            let Fact::Assistant { calls, .. } = seq[assistant] else {
                return Err(malformed("an assistant's index"));
            };
            let call = index(reply, calls.len(), "a call of the assistant")?;
            Step::Missing { assistant, call }
        } else {
            Step::Take(index(reply, seq.len(), "a message's index")?)
        });
    }
    Ok(steps)
}

fn read_plan(reply: &mut Reader<'_>, seq: &[&Fact]) -> Result<Plan, WireError> {
    let split = if reply.maybe()? {
        Some(index(reply, seq.len(), "the split")?)
    } else {
        None
    };
    let settles = reply.count()?;
    let steps = read_steps(reply, seq)?;
    if settles > steps.len() {
        return Err(malformed("a settled count within the order"));
    }
    Ok(Plan {
        split,
        settles,
        steps,
    })
}

/// Indices into the `len` messages of an entry.
fn read_picks(reply: &mut Reader<'_>, len: usize) -> Result<Vec<usize>, WireError> {
    let count = reply.count()?;
    let mut picks = Vec::with_capacity(count);
    for _ in 0..count {
        picks.push(index(reply, len, "a message of the entry")?);
    }
    Ok(picks)
}

fn call_order(facts: &[Fact]) -> Result<Vec<Step>, Error> {
    let mut request = Writer::new();
    request.tag(0);
    put_facts(&mut request, facts);
    let reply = call(Entry::ContextOrder, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let seq: Vec<&Fact> = facts.iter().collect();
    let steps = read_steps(&mut reply, &seq)?;
    reply.end()?;
    Ok(steps)
}

fn call_derive(marker: bool, entries: &[Ranged<'_>]) -> Result<(Vec<Part>, Plan), Error> {
    let mut request = Writer::new();
    request.tag(1).bool(marker).count(entries.len());
    for entry in entries {
        request.bool(entry.head);
        match entry.edit {
            Edit::None => {
                request.tag(0);
            }
            Edit::Omit => {
                request.tag(1);
            }
            Edit::Replace(facts) => {
                request.tag(2);
                put_facts(&mut request, facts);
            }
        }
        put_facts(&mut request, entry.own);
    }
    let reply = call(Entry::ContextOrder, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let count = reply.count()?;
    let mut parts = Vec::with_capacity(count);
    let mut seq: Vec<&Fact> = Vec::new();
    for _ in 0..count {
        let at = index(&mut reply, entries.len(), "an entry's index")?;
        if parts.last().is_some_and(|last: &Part| last.at >= at) {
            return Err(malformed("entries in increasing order").into());
        }
        let entry = &entries[at];
        let keep = match reply.tag_of(3, "a contribution")? {
            0 => Keep::Omitted,
            1 => {
                let picks = read_picks(&mut reply, entry.own.len())?;
                seq.extend(picks.iter().map(|&pick| &entry.own[pick]));
                Keep::Own(picks)
            }
            2.. => {
                let Edit::Replace(facts) = entry.edit else {
                    return Err(malformed("a replacement only for a Replace edit").into());
                };
                let picks = read_picks(&mut reply, facts.len())?;
                seq.extend(picks.iter().map(|&pick| &facts[pick]));
                Keep::Replaced(picks)
            }
        };
        parts.push(Part { at, keep });
    }
    let plan = read_plan(&mut reply, &seq)?;
    reply.end()?;
    Ok((parts, plan))
}

fn call_extend(added: &[Added<'_>], open: &[Fact]) -> Result<Extension, Error> {
    let mut request = Writer::new();
    request.tag(2).count(added.len());
    for entry in added {
        request
            .bool(entry.edits)
            .bool(entry.head)
            .bool(entry.edited);
        put_facts(&mut request, entry.own);
    }
    put_facts(&mut request, open);
    let reply = call(Entry::ContextOrder, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let extends = reply.tag_of(2, "an extension")? == 1;
    let extension = if extends {
        if reply.count()? != added.len() {
            return Err(malformed("what each added entry keeps").into());
        }
        let mut seq: Vec<&Fact> = open.iter().collect();
        let mut keeps = Vec::with_capacity(added.len());
        for entry in added {
            let picks = read_picks(&mut reply, entry.own.len())?;
            seq.extend(picks.iter().map(|&pick| &entry.own[pick]));
            keeps.push(picks);
        }
        let plan = read_plan(&mut reply, &seq)?;
        Extension::Extend { keeps, plan }
    } else {
        Extension::Rederive
    };
    reply.end()?;
    Ok(extension)
}

fn call_lead(roles: &[Role]) -> Result<Option<usize>, Error> {
    let mut request = Writer::new();
    request.tag(3).count(roles.len());
    for role in roles {
        request.tag(match role {
            Role::User => 0,
            Role::System => 1,
            Role::Assistant => 2,
            Role::Result => 3,
        });
    }
    let reply = call(Entry::ContextOrder, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let lead = if reply.maybe()? {
        Some(index(&mut reply, roles.len(), "a message's index")?)
    } else {
        None
    };
    reply.end()?;
    Ok(lead)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The order runs in the compiled core: results in call order right
    /// after their assistant, the first result per call id, a stray result
    /// dropped, a missing one synthesized.
    #[test]
    fn the_order_runs_in_the_compiled_core() {
        let facts = [
            Fact::User,
            Fact::Assistant {
                stop: StopReason::ToolUse,
                calls: vec![0, 1],
            },
            Fact::Result { call: 1 },
            Fact::Result { call: 2 },
            Fact::Result { call: 1 },
            Fact::Assistant {
                stop: StopReason::ToolUse,
                calls: vec![0],
            },
        ];
        assert_eq!(
            order(&facts),
            vec![
                Step::Take(0),
                Step::Take(1),
                Step::Missing {
                    assistant: 1,
                    call: 0
                },
                Step::Take(2),
                Step::Take(5),
                Step::Missing {
                    assistant: 5,
                    call: 0
                },
            ]
        );
    }
}
