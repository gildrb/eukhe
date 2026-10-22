//! The admission rule of one provider as one pure step over its live
//! tickets: the Bend model's live controller (`Live.step` in
//! `bend/admission.bend`, which `LAWS.bend` `admission_live_step` pins to
//! the model of rule H3). A ticket that ends leaves; the others keep their
//! numbers, in ticket order, and `next` numbers the next ticket.

use std::num::NonZeroU32;

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

/// The limits and the live tickets of one provider.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Live {
    /// `providerMaxInFlight`; `None` is unlimited.
    pub(super) limit: Option<NonZeroU32>,
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
    pub(super) fn new(limit: Option<NonZeroU32>, queue_limit: u32) -> Self {
        Self {
            limit,
            queue_limit,
            tickets: Vec::new(),
            next: 0,
        }
    }

    /// The status of ticket `number`; `None` once it ended.
    pub(super) fn status(&self, number: u64) -> Option<Status> {
        self.tickets
            .binary_search_by_key(&number, |ticket| ticket.number)
            .ok()
            .map(|at| self.tickets[at].status)
    }

    /// The tickets of `class` that hold a slot (`holding`) or wait.
    pub(super) fn count(&self, class: AdmissionPriority, holding: bool) -> usize {
        self.tickets
            .iter()
            .filter(|ticket| {
                ticket.class == class
                    && holds(ticket.status) == holding
                    && ticket.status != Status::Preempted
            })
            .count()
    }

    fn room(&self, held: usize) -> bool {
        self.limit
            .is_none_or(|limit| held < usize::try_from(limit.get()).unwrap_or(usize::MAX))
    }

    /// Grant free slots to the oldest waiters: interactive ones first,
    /// background ones only while no interactive request holds or waits.
    fn grant(&mut self) {
        loop {
            let interactive_waiting = self.count(AdmissionPriority::Interactive, false);
            let interactive_holding = self.count(AdmissionPriority::Interactive, true);
            let held = interactive_holding + self.count(AdmissionPriority::Background, true);
            let class = if !self.room(held) {
                None
            } else if interactive_waiting > 0 {
                Some(AdmissionPriority::Interactive)
            } else if interactive_holding == 0
                && self.count(AdmissionPriority::Background, false) > 0
            {
                Some(AdmissionPriority::Background)
            } else {
                None
            };
            let Some(class) = class else {
                return;
            };
            let Some(oldest) = self
                .tickets
                .iter_mut()
                .find(|ticket| ticket.class == class && ticket.status == Status::Queued)
            else {
                return;
            };
            oldest.status = Status::Granted;
        }
    }

    fn remove(&mut self, number: u64) {
        self.tickets.retain(|ticket| ticket.number != number);
    }
}

/// Whether a status holds a slot (a preempted permit's slot is free).
fn holds(status: Status) -> bool {
    match status {
        Status::Granted | Status::Held => true,
        Status::Queued | Status::Preempted => false,
    }
}

/// One op on the live tickets.
pub(super) fn step(live: &Live, op: Op) -> Live {
    let mut next = live.clone();
    match op {
        Op::Admit(class) => {
            let interactive_waiting = live.count(AdmissionPriority::Interactive, false);
            let interactive_holding = live.count(AdmissionPriority::Interactive, true);
            let status = match class {
                AdmissionPriority::Interactive => {
                    for ticket in &mut next.tickets {
                        if ticket.class == AdmissionPriority::Background {
                            ticket.status = match ticket.status {
                                Status::Granted | Status::Queued => Status::Queued,
                                Status::Held | Status::Preempted => Status::Preempted,
                            };
                        }
                    }
                    if interactive_waiting == 0 && live.room(interactive_holding) {
                        Some(Status::Held)
                    } else if usize::try_from(live.queue_limit).unwrap_or(usize::MAX)
                        <= interactive_waiting
                    {
                        None
                    } else {
                        Some(Status::Queued)
                    }
                }
                AdmissionPriority::Background => {
                    let held =
                        interactive_holding + live.count(AdmissionPriority::Background, true);
                    let free = interactive_holding == 0
                        && interactive_waiting == 0
                        && live.count(AdmissionPriority::Background, false) == 0
                        && live.room(held);
                    Some(if free { Status::Held } else { Status::Queued })
                }
            };
            if let Some(status) = status {
                next.tickets.push(Ticket {
                    number: live.next,
                    class,
                    status,
                });
            }
            next.next = live.next + 1;
        }
        Op::Collect(number) => {
            if let Some(ticket) = next
                .tickets
                .iter_mut()
                .find(|ticket| ticket.number == number && ticket.status == Status::Granted)
            {
                ticket.status = Status::Held;
            }
        }
        Op::Release(number) => match live.status(number) {
            Some(Status::Held) => {
                next.remove(number);
                next.grant();
            }
            Some(Status::Preempted) => next.remove(number),
            Some(Status::Queued | Status::Granted) | None => {}
        },
        Op::Leave(number) => match live.status(number) {
            Some(Status::Queued | Status::Granted) => {
                next.remove(number);
                next.grant();
            }
            Some(Status::Held | Status::Preempted) | None => {}
        },
        Op::Limit(limit, queue_limit) => {
            next.limit = limit;
            next.queue_limit = queue_limit;
            next.grant();
        }
    }
    next
}
