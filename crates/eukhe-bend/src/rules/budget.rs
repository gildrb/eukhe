//! The ledger of a task tree's budget (`bend/budget.bend`, entry
//! `bend/ffi_budget.bend`; `laws/budget.bend`, spec
//! `spec/budget/ledger.bend`). An account holds, in each of four spent
//! dimensions (money, tokens, tool calls, model requests), what is free,
//! spent, lent to live children given their own budget and spent past the
//! funding, next to its open reservations and its deadline (wall-clock
//! time). Each agent of the tree has its own phase, an input of
//! [`reserve`] and [`carve`] and the output of a refusal. Every change of
//! an account is one call of the compiled core: [`reserve`] before
//! anything is spent, [`settle`] after (a crash's open hold is settled at
//! its held amount), [`carve`] and [`close`] for a child given its own
//! budget, [`fund`] when budget or time is added. Rust (eukhe-budget)
//! keeps the account on disk and gathers the amounts; it decides nothing.
//!
//! Every number crosses the wire, so each must stay within
//! [`NAT_MAX`](crate::wire::NAT_MAX): a caller keeps its amounts, durations
//! and deadlines within `eukhe_types::budget::BUDGET_AMOUNT_MAX`, a tenth of
//! it, so no sum the core forms (free and a hold, a deadline and the
//! durations it is checked against) passes the wire or the runtime's bound
//! on a Nat. A number past the wire is an [`Error`], never a panic: the
//! ledger refuses the operation.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, Entry, Error};

/// An amount in each spent dimension: money, tokens, tool calls, model
/// requests.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Amt {
    pub cost: u64,
    pub tok: u64,
    pub calls: u64,
    pub reqs: u64,
}

/// What a reservation asks for: an amount and how long it may run (ms).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Ask {
    pub amt: Amt,
    pub ms: u64,
}

/// A dimension of a budget, in the core's order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Dim {
    Cost,
    Tokens,
    /// The deadline.
    Time,
    Calls,
    Reqs,
}

/// An open reservation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Hold {
    pub id: u64,
    pub amt: Amt,
}

/// What an agent is admitted.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Phase {
    /// Work, side requests and a final answer.
    #[default]
    Working,
    /// A final answer and side requests.
    WrapUp,
    /// Nothing.
    Exhausted,
}

/// The ledger of one account: what is free, spent, lent and overrun, the
/// open holds, the deadline (Unix ms).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Acct {
    pub free: Amt,
    pub spent: Amt,
    pub lent: Amt,
    pub over: Amt,
    pub holds: Vec<Hold>,
    pub until: u64,
}

/// What a reservation is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Use {
    /// Work: it must leave the agent's own final-answer reserve.
    Work,
    /// The final answer: it may use everything past the reserves above.
    Final,
    /// A side request of the agent, not its own turn (a title, a
    /// classifier, a compaction, a memory or side question): it must leave
    /// the agent's own final-answer reserve like work, is admitted while the
    /// agent can still answer (`Working`, `WrapUp`), and a refusal leaves the
    /// agent's phase as it was.
    Side,
}

/// Why nothing was taken.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Why {
    /// No offer fits; the last one lacks this dimension first.
    Short(Dim),
    /// The id is already held.
    Held,
    /// The agent's phase does not admit the request.
    Stopped,
}

/// The answer to a reservation.
// One answer per reservation, read at once and never stored (as `Carve`).
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Grant {
    /// The offer at `index` is held under the id; `tight` says the same
    /// ask, started when this one ends, would not fit what is left.
    Granted {
        index: usize,
        ask: Ask,
        acct: Acct,
        tight: bool,
    },
    /// Nothing is held; `phase` is the agent's phase after the refusal (it
    /// moves when no offer fits).
    Refused { why: Why, phase: Phase },
}

/// The answer to a carve.
// One answer per carve, read at once and never stored: boxing the
// accounts would only add an allocation to every carve.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Carve {
    Carved { parent: Acct, child: Acct },
    Kept(Why),
}

/// The answer to a close.
// One answer per close, read at once and never stored (as `Carve`).
#[allow(clippy::large_enum_variant)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Close {
    Closed {
        parent: Acct,
        child: Acct,
    },
    /// The child has an open reservation or a live child of its own.
    Busy,
}

fn put_amt(w: &mut Writer, amt: Amt) {
    w.nat(amt.cost).nat(amt.tok).nat(amt.calls).nat(amt.reqs);
}

fn put_ask(w: &mut Writer, ask: Ask) {
    put_amt(w, ask.amt);
    w.nat(ask.ms);
}

fn put_phase(w: &mut Writer, phase: Phase) {
    w.tag(match phase {
        Phase::Working => 0,
        Phase::WrapUp => 1,
        Phase::Exhausted => 2,
    });
}

fn put_acct(w: &mut Writer, acct: &Acct) {
    put_amt(w, acct.free);
    put_amt(w, acct.spent);
    put_amt(w, acct.lent);
    put_amt(w, acct.over);
    w.count(acct.holds.len());
    for hold in &acct.holds {
        w.nat(hold.id);
        put_amt(w, hold.amt);
    }
    w.nat(acct.until);
}

fn get_amt(r: &mut Reader<'_>) -> Result<Amt, WireError> {
    Ok(Amt {
        cost: r.nat()?,
        tok: r.nat()?,
        calls: r.nat()?,
        reqs: r.nat()?,
    })
}

fn get_ask(r: &mut Reader<'_>) -> Result<Ask, WireError> {
    Ok(Ask {
        amt: get_amt(r)?,
        ms: r.nat()?,
    })
}

fn get_phase(r: &mut Reader<'_>) -> Result<Phase, WireError> {
    Ok(match r.tag_of(3, "a budget phase")? {
        0 => Phase::Working,
        1 => Phase::WrapUp,
        // `tag_of` answers a tag below 3: this is 2.
        _ => Phase::Exhausted,
    })
}

fn get_acct(r: &mut Reader<'_>) -> Result<Acct, WireError> {
    let free = get_amt(r)?;
    let spent = get_amt(r)?;
    let lent = get_amt(r)?;
    let over = get_amt(r)?;
    let n = r.count()?;
    let mut holds = Vec::with_capacity(n);
    for _ in 0..n {
        holds.push(Hold {
            id: r.nat()?,
            amt: get_amt(r)?,
        });
    }
    Ok(Acct {
        free,
        spent,
        lent,
        over,
        holds,
        until: r.nat()?,
    })
}

fn get_why(r: &mut Reader<'_>) -> Result<Why, WireError> {
    Ok(match r.tag_of(3, "a budget refusal")? {
        0 => Why::Short(match r.tag_of(5, "a budget dimension")? {
            0 => Dim::Cost,
            1 => Dim::Tokens,
            2 => Dim::Time,
            3 => Dim::Calls,
            // `tag_of` answers a tag below 5: this is 4.
            _ => Dim::Reqs,
        }),
        1 => Why::Held,
        // `tag_of` answers a tag below 3: this is 2.
        _ => Why::Stopped,
    })
}

fn ask<T>(
    write: impl FnOnce(&mut Writer),
    read: impl FnOnce(&mut Reader<'_>) -> Result<T, WireError>,
) -> Result<T, Error> {
    let mut request = Writer::new();
    write(&mut request);
    let reply = call(Entry::Budget, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let value = read(&mut reader)?;
    reader.end()?;
    Ok(value)
}

/// Reserves under `id`, for an agent in `phase` at `now` (Unix ms), the
/// first of `want` and then `less` that fits what is free in `acct` and
/// ends before its deadline, leaving `base` (the final-answer reserves of
/// the agents above) and, for work and a side request, `keep` (the agent's
/// own).
///
/// # Errors
///
/// A number past the wire, or a failure of the compiled core.
// The core's request, field for field (bend/ffi_budget.bend): bundling
// them would only restate the wire.
#[allow(clippy::too_many_arguments)]
pub fn reserve(
    use_: Use,
    phase: Phase,
    id: u64,
    now: u64,
    base: Ask,
    keep: Ask,
    want: Ask,
    less: &[Ask],
    acct: &Acct,
) -> Result<Grant, Error> {
    ask(
        |w| {
            w.tag(0).tag(match use_ {
                Use::Work => 0,
                Use::Final => 1,
                Use::Side => 2,
            });
            put_phase(w, phase);
            w.nat(id).nat(now);
            put_ask(w, base);
            put_ask(w, keep);
            put_ask(w, want);
            w.count(less.len());
            for offer in less {
                put_ask(w, *offer);
            }
            put_acct(w, acct);
        },
        |r| {
            Ok(if r.tag_of(2, "a budget grant")? == 0 {
                let index = r.count()?;
                let ask = get_ask(r)?;
                let acct = get_acct(r)?;
                let tight = r.bool()?;
                Grant::Granted {
                    index,
                    ask,
                    acct,
                    tight,
                }
            } else {
                let why = get_why(r)?;
                let phase = get_phase(r)?;
                Grant::Refused { why, phase }
            })
        },
    )
}

/// The account after the actual spend `spend` replaced what `id` held; an
/// id that is not held changes nothing.
///
/// # Errors
///
/// A number past the wire, or a failure of the compiled core.
pub fn settle(id: u64, spend: Amt, acct: &Acct) -> Result<Acct, Error> {
    ask(
        |w| {
            w.tag(1).nat(id);
            put_amt(w, spend);
            put_acct(w, acct);
        },
        get_acct,
    )
}

/// Carves, for an agent in `phase` at `now`, a child's own budget `want`
/// (its amount and its duration from now) out of `acct`, which keeps
/// `base` (the reserves of the agents above the child).
///
/// # Errors
///
/// A number past the wire, or a failure of the compiled core.
pub fn carve(phase: Phase, now: u64, want: Ask, base: Ask, acct: &Acct) -> Result<Carve, Error> {
    ask(
        |w| {
            w.tag(2);
            put_phase(w, phase);
            w.nat(now);
            put_ask(w, want);
            put_ask(w, base);
            put_acct(w, acct);
        },
        |r| {
            Ok(if r.tag_of(2, "a budget carve")? == 0 {
                let parent = get_acct(r)?;
                let child = get_acct(r)?;
                Carve::Carved { parent, child }
            } else {
                Carve::Kept(get_why(r)?)
            })
        },
    )
}

/// Closes the idle `child` into `parent`: what it has free returns, its
/// spend becomes the parent's; the child is left empty, its deadline
/// passed.
///
/// # Errors
///
/// A number past the wire, or a failure of the compiled core.
pub fn close(child: &Acct, parent: &Acct) -> Result<Close, Error> {
    ask(
        |w| {
            w.tag(3);
            put_acct(w, child);
            put_acct(w, parent);
        },
        |r| {
            Ok(if r.tag_of(2, "a budget close")? == 0 {
                let parent = get_acct(r)?;
                let child = get_acct(r)?;
                Close::Closed { parent, child }
            } else {
                Close::Busy
            })
        },
    )
}

/// The account after `n` more budget and `n`'s duration more time: an
/// overrun is repaid first.
///
/// # Errors
///
/// A number past the wire, or a failure of the compiled core.
pub fn fund(n: Ask, acct: &Acct) -> Result<Acct, Error> {
    ask(
        |w| {
            w.tag(4);
            put_ask(w, n);
            put_acct(w, acct);
        },
        get_acct,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn amt(cost: u64, tok: u64, calls: u64, reqs: u64) -> Amt {
        Amt {
            cost,
            tok,
            calls,
            reqs,
        }
    }

    fn ask_of(amt: Amt, ms: u64) -> Ask {
        Ask { amt, ms }
    }

    fn funded(free: Amt, until: u64) -> Acct {
        Acct {
            free,
            until,
            ..Acct::default()
        }
    }

    #[test]
    fn work_takes_the_first_offer_that_fits_and_leaves_the_reserves() {
        let acct = funded(amt(10, 10, 10, 10), 100);
        let grant = reserve(
            Use::Work,
            Phase::Working,
            7,
            0,
            ask_of(amt(1, 0, 0, 0), 0),
            ask_of(amt(1, 2, 2, 0), 5),
            ask_of(amt(9, 1, 1, 1), 10),
            &[ask_of(amt(8, 1, 1, 1), 10)],
            &acct,
        )
        .unwrap();
        assert_eq!(
            grant,
            Grant::Granted {
                index: 1,
                ask: ask_of(amt(8, 1, 1, 1), 10),
                acct: Acct {
                    free: amt(2, 9, 9, 9),
                    holds: vec![Hold {
                        id: 7,
                        amt: amt(8, 1, 1, 1)
                    }],
                    until: 100,
                    ..Acct::default()
                },
                tight: true,
            }
        );
    }

    #[test]
    fn work_that_fits_nowhere_wraps_the_agent_up_and_then_only_a_final_answer_is_admitted() {
        let acct = funded(amt(10, 10, 10, 10), 100);
        let none = Ask::default();
        let keep = ask_of(amt(2, 2, 2, 0), 0);
        assert_eq!(
            reserve(
                Use::Work,
                Phase::Working,
                1,
                0,
                none,
                keep,
                ask_of(amt(9, 9, 9, 9), 0),
                &[],
                &acct
            )
            .unwrap(),
            Grant::Refused {
                why: Why::Short(Dim::Cost),
                phase: Phase::WrapUp
            }
        );
        assert_eq!(
            reserve(
                Use::Work,
                Phase::WrapUp,
                2,
                0,
                none,
                none,
                ask_of(amt(1, 1, 1, 1), 0),
                &[],
                &acct
            )
            .unwrap(),
            Grant::Refused {
                why: Why::Stopped,
                phase: Phase::WrapUp
            }
        );
        let last = reserve(
            Use::Final,
            Phase::WrapUp,
            3,
            0,
            none,
            keep,
            ask_of(amt(10, 10, 10, 0), 0),
            &[],
            &acct,
        )
        .unwrap();
        assert!(matches!(last, Grant::Granted { index: 0, .. }));
        // a final answer that fits nowhere exhausts the agent
        assert_eq!(
            reserve(
                Use::Final,
                Phase::WrapUp,
                4,
                0,
                none,
                none,
                ask_of(amt(1, 1, 1, 11), 0),
                &[],
                &acct
            )
            .unwrap(),
            Grant::Refused {
                why: Why::Short(Dim::Reqs),
                phase: Phase::Exhausted
            }
        );
    }

    #[test]
    fn a_side_request_leaves_the_final_answer_reserve_and_never_moves_the_phase() {
        let acct = funded(amt(10, 10, 10, 10), 100);
        let none = Ask::default();
        let keep = ask_of(amt(2, 2, 2, 0), 0);
        // it must leave keep like work: 9 + 2 is past 10, so it is short and
        // the agent stays Working
        assert_eq!(
            reserve(
                Use::Side,
                Phase::Working,
                1,
                0,
                none,
                keep,
                ask_of(amt(9, 1, 1, 1), 0),
                &[],
                &acct
            )
            .unwrap(),
            Grant::Refused {
                why: Why::Short(Dim::Cost),
                phase: Phase::Working
            }
        );
        // a WrapUp agent is admitted a side request that fits, and one that
        // does not leaves it in WrapUp
        assert!(matches!(
            reserve(
                Use::Side,
                Phase::WrapUp,
                2,
                0,
                none,
                keep,
                ask_of(amt(8, 1, 1, 1), 0),
                &[],
                &acct
            )
            .unwrap(),
            Grant::Granted { index: 0, .. }
        ));
        assert_eq!(
            reserve(
                Use::Side,
                Phase::WrapUp,
                3,
                0,
                none,
                keep,
                ask_of(amt(9, 1, 1, 1), 0),
                &[],
                &acct
            )
            .unwrap(),
            Grant::Refused {
                why: Why::Short(Dim::Cost),
                phase: Phase::WrapUp
            }
        );
        // an exhausted agent is stopped
        assert_eq!(
            reserve(
                Use::Side,
                Phase::Exhausted,
                4,
                0,
                none,
                none,
                ask_of(amt(1, 1, 1, 1), 0),
                &[],
                &acct
            )
            .unwrap(),
            Grant::Refused {
                why: Why::Stopped,
                phase: Phase::Exhausted
            }
        );
    }

    #[test]
    fn an_ask_that_runs_past_the_deadline_is_short_of_time() {
        let acct = funded(amt(10, 10, 10, 10), 1_000);
        let none = Ask::default();
        // 900 + 60 + 50 (the reserve above) runs past 1000
        assert_eq!(
            reserve(
                Use::Final,
                Phase::Working,
                1,
                900,
                ask_of(Amt::default(), 50),
                none,
                ask_of(amt(1, 1, 1, 1), 60),
                &[],
                &acct
            )
            .unwrap(),
            Grant::Refused {
                why: Why::Short(Dim::Time),
                phase: Phase::Exhausted
            }
        );
        // a shorter offer ends in time
        assert!(matches!(
            reserve(
                Use::Final,
                Phase::Working,
                1,
                900,
                ask_of(Amt::default(), 50),
                none,
                ask_of(amt(1, 1, 1, 1), 60),
                &[ask_of(amt(1, 1, 1, 1), 50)],
                &acct
            )
            .unwrap(),
            Grant::Granted { index: 1, .. }
        ));
    }

    #[test]
    fn a_settlement_returns_the_rest_once() {
        let held = Acct {
            free: amt(5, 5, 5, 9),
            holds: vec![Hold {
                id: 7,
                amt: amt(5, 5, 5, 1),
            }],
            until: 50,
            ..Acct::default()
        };
        let settled = settle(7, amt(3, 2, 1, 1), &held).unwrap();
        assert_eq!(
            settled,
            Acct {
                free: amt(7, 8, 9, 9),
                spent: amt(3, 2, 1, 1),
                until: 50,
                ..Acct::default()
            }
        );
        assert_eq!(settle(7, amt(3, 2, 1, 1), &settled).unwrap(), settled);
    }

    #[test]
    fn a_spend_past_its_hold_is_taken_from_free_and_then_recorded_as_an_overrun() {
        let held = Acct {
            free: amt(1, 0, 0, 0),
            holds: vec![Hold {
                id: 1,
                amt: amt(2, 0, 0, 0),
            }],
            ..Acct::default()
        };
        assert_eq!(
            settle(1, amt(5, 0, 0, 0), &held).unwrap(),
            Acct {
                spent: amt(5, 0, 0, 0),
                over: amt(2, 0, 0, 0),
                ..Acct::default()
            }
        );
    }

    #[test]
    fn a_carve_lends_the_allotment_and_a_close_returns_what_is_left() {
        let parent = funded(amt(10, 10, 10, 10), 1_000);
        let base = ask_of(amt(1, 1, 1, 0), 50);
        let Carve::Carved { parent, child } = carve(
            Phase::Working,
            100,
            ask_of(amt(4, 4, 4, 1), 300),
            base,
            &parent,
        )
        .unwrap() else {
            panic!("a carve that fits was refused");
        };
        assert_eq!(
            parent,
            Acct {
                free: amt(6, 6, 6, 9),
                lent: amt(4, 4, 4, 1),
                until: 1_000,
                ..Acct::default()
            }
        );
        assert_eq!(child, funded(amt(4, 4, 4, 1), 400));
        let spent = Acct {
            free: amt(1, 4, 4, 1),
            spent: amt(3, 0, 0, 0),
            until: 400,
            ..Acct::default()
        };
        assert_eq!(
            close(&spent, &parent).unwrap(),
            Close::Closed {
                parent: Acct {
                    free: amt(7, 10, 10, 10),
                    spent: amt(3, 0, 0, 0),
                    until: 1_000,
                    ..Acct::default()
                },
                child: Acct::default(),
            }
        );
        let busy = Acct {
            holds: vec![Hold {
                id: 1,
                amt: amt(1, 0, 0, 0),
            }],
            ..spent
        };
        assert_eq!(close(&busy, &parent).unwrap(), Close::Busy);
        assert_eq!(
            carve(
                Phase::Working,
                100,
                ask_of(amt(10, 1, 1, 1), 0),
                base,
                &parent
            )
            .unwrap(),
            Carve::Kept(Why::Short(Dim::Cost))
        );
        assert_eq!(
            carve(
                Phase::Working,
                100,
                ask_of(amt(1, 1, 1, 1), 900),
                base,
                &parent
            )
            .unwrap(),
            Carve::Kept(Why::Short(Dim::Time))
        );
        assert_eq!(
            carve(
                Phase::WrapUp,
                100,
                ask_of(amt(1, 1, 1, 1), 0),
                base,
                &parent
            )
            .unwrap(),
            Carve::Kept(Why::Stopped)
        );
    }

    #[test]
    fn funding_repays_an_overrun_first_and_extends_the_deadline() {
        let overrun = Acct {
            over: amt(1, 0, 0, 0),
            until: 100,
            ..Acct::default()
        };
        assert_eq!(
            fund(ask_of(amt(3, 3, 3, 3), 50), &overrun).unwrap(),
            funded(amt(2, 3, 3, 3), 150)
        );
    }

    #[test]
    fn a_number_past_the_wire_is_an_error_not_a_stop() {
        let acct = funded(amt(u64::MAX, 0, 0, 0), 0);
        assert!(settle(0, Amt::default(), &acct).is_err());
    }
}
