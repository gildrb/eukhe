//! `jobs.wait`, the agent's one blocking wait on its own work
//! (`bend/wait_any.bend`, entry `bend/ffi_wait_any.bend`;
//! `laws/wait_any.bend`, spec `spec/durable/wait_any.bend`).
//!
//! A poll takes the first settled target (a ready one; a gone one too when
//! the caller named its targets), refuses a wait with nothing running and
//! nothing ready, then ends on the user's cancel, then on the cap. A job's
//! result goes to the session's notice only when no wait watches it and
//! the session has a wake path, else a wait takes it: each result is
//! delivered at most once (`wait_any_once`). A wait lasts what the caller
//! asked, at most 30 minutes.

use crate::wire::{Reader, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error};

/// A target of a wait, as the host finds it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    /// It still runs.
    Running,
    /// It settled; its result reached no one yet.
    Ready,
    /// It settled and its result was delivered.
    Gone,
}

/// Whether the caller named the targets of its wait.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Targets {
    /// `jobs.wait()`: every running piece of work.
    Any,
    /// The caller named them: a gone one is taken too.
    Named,
}

/// What one poll of a wait found besides its targets.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Signals {
    /// The user's cancel fired.
    pub cancelled: bool,
    /// The wait's length passed.
    pub late: bool,
}

/// What one poll decides.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pick {
    /// Keep waiting.
    Wait,
    /// The wait ends with the target at this index.
    Take(usize),
    /// Refused: nothing runs and nothing is ready.
    Nothing,
    /// The wait's length passed with nothing settled.
    Capped,
    /// The user's cancel ended it.
    Cancelled,
}

/// Where a job's result is in its delivery.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    /// The job runs.
    Live,
    /// Settled, held for a wait.
    Kept,
    /// Settled and delivered.
    Sent,
}

/// What happens to a job's delivery.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Event {
    /// A wait starts watching it.
    Watch,
    /// A wait stops watching it.
    Unwatch,
    /// The job settles.
    Settles,
    /// A wait takes its result.
    Taken,
}

/// Whether the session has a wake path (the job-settled notice).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Wake {
    Notice,
    None,
}

/// One job's delivery: how many waits watch it, and its phase.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Delivery {
    pub watchers: u64,
    pub phase: Phase,
}

impl Delivery {
    /// A job before any event: running, watched by no wait.
    pub const FRESH: Delivery = Delivery {
        watchers: 0,
        phase: Phase::Live,
    };
}

/// A delivery step's answer: the delivery after it, and whether the step
/// delivered the result (to the notice for a settle or an unwatch, to the
/// wait for a take).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stepped {
    pub delivery: Delivery,
    pub delivered: bool,
}

/// One poll of a wait over `targets`, from the compiled core.
#[must_use]
pub fn poll(named: Targets, signals: Signals, targets: &[Target]) -> Pick {
    expect_core(Entry::WaitAny, poll_call(named, signals, targets))
}

fn poll_call(named: Targets, signals: Signals, targets: &[Target]) -> Result<Pick, Error> {
    let mut request = Writer::new();
    request
        .tag(0)
        .bool(named == Targets::Named)
        .bool(signals.cancelled)
        .bool(signals.late)
        .count(targets.len());
    for target in targets {
        request.nat(match target {
            Target::Running => 0,
            Target::Ready => 1,
            Target::Gone => 2,
        });
    }
    let reply = call(Entry::WaitAny, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let pick = match reader.tag_of(5, "a wait poll")? {
        0 => Pick::Wait,
        1 => Pick::Take(reader.count()?),
        2 => Pick::Nothing,
        3 => Pick::Capped,
        // `tag_of` answers a tag below 5: this is 4.
        _ => Pick::Cancelled,
    };
    reader.end()?;
    Ok(pick)
}

/// One event of a job's delivery, from the compiled core.
#[must_use]
pub fn step(wake: Wake, delivery: Delivery, event: Event) -> Stepped {
    expect_core(Entry::WaitAny, step_call(wake, delivery, event))
}

fn step_call(wake: Wake, delivery: Delivery, event: Event) -> Result<Stepped, Error> {
    let mut request = Writer::new();
    request
        .tag(1)
        .bool(wake == Wake::Notice)
        .nat(delivery.watchers.min(NAT_MAX))
        .nat(match delivery.phase {
            Phase::Live => 0,
            Phase::Kept => 1,
            Phase::Sent => 2,
        })
        .nat(match event {
            Event::Watch => 0,
            Event::Unwatch => 1,
            Event::Settles => 2,
            Event::Taken => 3,
        });
    let reply = call(Entry::WaitAny, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let watchers = reader.nat()?;
    let phase = match reader.tag_of(3, "a delivery phase")? {
        0 => Phase::Live,
        1 => Phase::Kept,
        // `tag_of` answers a tag below 3: this is 2.
        _ => Phase::Sent,
    };
    let delivered = reader.tag_of(2, "a delivery count")? == 1;
    reader.end()?;
    Ok(Stepped {
        delivery: Delivery { watchers, phase },
        delivered,
    })
}

/// How long a wait lasts, in seconds: `asked` (`None`: the cap) at most
/// the cap of 30 minutes, from the compiled core.
#[must_use]
pub fn timeout_secs(asked: Option<u64>) -> u64 {
    expect_core(Entry::WaitAny, timeout_call(asked))
}

fn timeout_call(asked: Option<u64>) -> Result<u64, Error> {
    let mut request = Writer::new();
    request.tag(2);
    match asked {
        None => request.none(),
        Some(secs) => request.some().nat(secs.min(NAT_MAX)),
    };
    let reply = call(Entry::WaitAny, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let secs = reader.nat()?;
    reader.end()?;
    Ok(secs)
}

#[cfg(test)]
mod tests {
    use super::*;

    const CALM: Signals = Signals {
        cancelled: false,
        late: false,
    };

    /// The anchors of `wait_any_example`: a wait-any takes the first ready
    /// target past a gone one; a named wait takes a gone one; nothing
    /// running is refused; the cancel wins over the cap.
    #[test]
    fn the_core_polls_waits() {
        let both = Signals {
            cancelled: true,
            late: true,
        };
        assert_eq!(
            [
                poll(
                    Targets::Any,
                    CALM,
                    &[Target::Running, Target::Gone, Target::Ready]
                ),
                poll(Targets::Named, CALM, &[Target::Running, Target::Gone]),
                poll(Targets::Any, both, &[Target::Gone]),
                poll(Targets::Any, both, &[Target::Running]),
                poll(
                    Targets::Any,
                    Signals {
                        cancelled: false,
                        late: true
                    },
                    &[Target::Running]
                ),
                poll(Targets::Any, CALM, &[Target::Running]),
            ],
            [
                Pick::Take(2),
                Pick::Take(1),
                Pick::Nothing,
                Pick::Cancelled,
                Pick::Capped,
                Pick::Wait,
            ]
        );
    }

    /// A watched job's result is kept for the wait and taken once; an
    /// unwatched one goes to the notice; the last watcher leaving hands a
    /// kept result to the notice.
    #[test]
    fn the_core_routes_each_result_once() {
        let watched = step(Wake::Notice, Delivery::FRESH, Event::Watch).delivery;
        let kept = step(Wake::Notice, watched, Event::Settles);
        let taken = step(Wake::Notice, kept.delivery, Event::Taken);
        assert_eq!(
            [
                step(Wake::Notice, Delivery::FRESH, Event::Settles),
                kept,
                taken,
                step(Wake::Notice, taken.delivery, Event::Taken),
                step(Wake::Notice, kept.delivery, Event::Unwatch),
                step(Wake::None, Delivery::FRESH, Event::Settles),
            ],
            [
                Stepped {
                    delivery: Delivery {
                        watchers: 0,
                        phase: Phase::Sent
                    },
                    delivered: true
                },
                Stepped {
                    delivery: Delivery {
                        watchers: 1,
                        phase: Phase::Kept
                    },
                    delivered: false
                },
                Stepped {
                    delivery: Delivery {
                        watchers: 1,
                        phase: Phase::Sent
                    },
                    delivered: true
                },
                Stepped {
                    delivery: Delivery {
                        watchers: 1,
                        phase: Phase::Sent
                    },
                    delivered: false
                },
                Stepped {
                    delivery: Delivery {
                        watchers: 0,
                        phase: Phase::Sent
                    },
                    delivered: true
                },
                Stepped {
                    delivery: Delivery {
                        watchers: 0,
                        phase: Phase::Kept
                    },
                    delivered: false
                },
            ]
        );
    }

    /// The cap is 30 minutes; a shorter ask stands.
    #[test]
    fn the_core_caps_waits() {
        assert_eq!(
            [
                timeout_secs(None),
                timeout_secs(Some(45)),
                timeout_secs(Some(3600))
            ],
            [1800, 45, 1800]
        );
    }
}
