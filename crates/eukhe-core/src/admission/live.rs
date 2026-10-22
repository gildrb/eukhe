//! The admission rule of one provider runs as its Bend model: the live
//! controller of `bend/admission.bend` (`Live.step`, which `LAWS.bend`
//! `admission_live_step` pins to the model of rule H3), kept in the Bend
//! heap by a [`Stepper`] of `bend/ffi_admission.bend`. Each op crosses the
//! wire; the reply is the controller's new state, which [`Live`] mirrors:
//! the live tickets (an ended ticket leaves; the others keep their
//! numbers), in ticket order, and the number of the next ticket.

use std::num::NonZeroU32;

use eukhe_bend::wire::{Reader, WireError, Writer};
use eukhe_bend::{expect_core, Entry, Stepper};
use eukhe_types::daemon::AdmissionPriority;

/// A live ticket's status: it waits, holds a slot its waiter has not
/// collected, holds a collected permit, or held a background permit an
/// interactive request took the slot from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Status {
    Queued,
    Granted,
    Held,
    Preempted,
}

/// One live ticket.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Ticket {
    pub(super) number: u64,
    pub(super) class: AdmissionPriority,
    pub(super) status: Status,
}

/// The limits and the live tickets of one provider, as the last reply of
/// the rule gave them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Live {
    /// `providerMaxQueued`.
    pub(super) queue_limit: u32,
    /// The live tickets, oldest first.
    pub(super) tickets: Vec<Ticket>,
    /// The number of the next ticket.
    pub(super) next: u64,
}

/// What a ticket's holder does: admit a request of a class (it gets ticket
/// `next`), collect a granted permit, release a collected permit, leave
/// (drop a waiter, granted or not), or set the limits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Op {
    Admit(AdmissionPriority),
    Collect(u64),
    Release(u64),
    Leave(u64),
    Limit(Option<NonZeroU32>, u32),
}

impl Live {
    /// The status of ticket `number`; `None` once it ended.
    pub(super) fn status(&self, number: u64) -> Option<Status> {
        self.tickets
            .binary_search_by_key(&number, |ticket| ticket.number)
            .ok()
            .map(|at| self.tickets[at].status)
    }

    /// The tickets of `class` that hold a slot (`holding`: granted or
    /// collected) or wait (queued).
    pub(super) fn count(&self, class: AdmissionPriority, holding: bool) -> usize {
        self.tickets
            .iter()
            .filter(|ticket| {
                ticket.class == class
                    && match ticket.status {
                        Status::Granted | Status::Held => holding,
                        Status::Queued => !holding,
                        Status::Preempted => false,
                    }
            })
            .count()
    }
}

/// The rule's state of one provider in the Bend heap.
#[derive(Debug)]
pub(super) struct Rule {
    stepper: Stepper,
}

impl Rule {
    /// A provider with these limits and no ticket, and its state.
    pub(super) fn open(limit: Option<NonZeroU32>, queue_limit: u32) -> (Rule, Live) {
        let opened = (|| -> Result<(Rule, Live), eukhe_bend::Error> {
            let mut request = Writer::new();
            write_limit(&mut request, limit);
            let input = request.u32(queue_limit).finish()?;
            let (stepper, reply) = Stepper::open(Entry::Admission, &input)?;
            Ok((Rule { stepper }, read_live(&reply)?))
        })();
        expect_core(Entry::Admission, opened)
    }

    /// One op; the provider's new state.
    pub(super) fn step(&mut self, op: Op) -> Live {
        let stepped = (|| -> Result<Live, eukhe_bend::Error> {
            let mut request = Writer::new();
            match op {
                Op::Admit(class) => write_class(request.tag(0), class),
                Op::Collect(number) => request.tag(1).nat(number),
                Op::Release(number) => request.tag(2).nat(number),
                Op::Leave(number) => request.tag(3).nat(number),
                Op::Limit(limit, queue_limit) => {
                    write_limit(request.tag(4), limit);
                    request.u32(queue_limit)
                }
            };
            let reply = self.stepper.step(&request.finish()?)?;
            Ok(read_live(&reply)?)
        })();
        expect_core(Entry::Admission, stepped)
    }
}

fn write_class(request: &mut Writer, class: AdmissionPriority) -> &mut Writer {
    request.tag(match class {
        AdmissionPriority::Interactive => 0,
        AdmissionPriority::Background => 1,
    })
}

/// `providerMaxInFlight`: unlimited, or `1 + p` slots.
fn write_limit(request: &mut Writer, limit: Option<NonZeroU32>) -> &mut Writer {
    match limit {
        None => request.tag(0),
        Some(limit) => request.tag(1).u32(limit.get() - 1),
    }
}

/// The classes by their wire tags.
const CLASSES: [AdmissionPriority; 2] = [
    AdmissionPriority::Interactive,
    AdmissionPriority::Background,
];

/// The statuses of a live ticket by their wire tags (tag 4, ended, never
/// comes back: an ended ticket leaves).
const STATUSES: [Status; 4] = [
    Status::Queued,
    Status::Granted,
    Status::Held,
    Status::Preempted,
];

/// The value whose wire tag comes next, of the values `all` in tag order.
fn read_tag<T: Copy>(
    reader: &mut Reader<'_>,
    all: &[T],
    expected: &'static str,
) -> Result<T, WireError> {
    let tags = u32::try_from(all.len()).unwrap_or(u32::MAX);
    let tag = reader.tag_of(tags, expected)?;
    usize::try_from(tag)
        .ok()
        .and_then(|at| all.get(at).copied())
        .ok_or(WireError::Malformed { at: 0, expected })
}

fn read_live(reply: &str) -> Result<Live, WireError> {
    let mut reader = Reader::reply(reply)?;
    // The limit comes back as it went out; the controller keeps its own.
    if reader.tag_of(2, "a limit")? == 1 {
        reader.u32()?;
    }
    let queue_limit = reader.u32()?;
    let count = reader.count()?;
    let mut tickets = Vec::with_capacity(count);
    for _ in 0..count {
        let number = reader.nat()?;
        let class = read_tag(&mut reader, &CLASSES, "a request class")?;
        let status = read_tag(&mut reader, &STATUSES, "a live ticket's status")?;
        tickets.push(Ticket {
            number,
            class,
            status,
        });
    }
    let next = reader.nat()?;
    reader.end()?;
    Ok(Live {
        queue_limit,
        tickets,
        next,
    })
}
