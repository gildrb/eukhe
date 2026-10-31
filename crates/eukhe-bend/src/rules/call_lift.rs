//! Stored tool calls lifted to the current dialect of their families
//! (`bend/call_lift.bend`, entry `bend/ffi_call_lift.bend`;
//! `laws/call_lift.bend`). Every tool result's details carry the call's
//! stamp `family@rev`; the lift table (Bend `table()`) holds each family's
//! current rev and the steps from its older revs, with the argument ops of
//! each step. Rust sends each stamped call's family, rev and argument
//! names (never the values) and reads, per call, whether it is untouched
//! (unknown family, current rev), stranded (a rev the table cannot lift),
//! or lifted: the current rev, where each stored argument goes, the
//! arguments a step added, and the receipts of what changed.

use crate::wire::{Reader, WireError, Writer};
use crate::{call, expect_core, Entry, Error};

/// A stored call as the lift reads it: its stamp's family and rev, and
/// its argument names in order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoredCall<'a> {
    pub family: &'a str,
    pub rev: &'a str,
    pub keys: Vec<&'a str>,
}

/// The lift of one stored call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lift {
    /// The table has no such family: the call is untouched.
    Unknown,
    /// The call is at its family's current rev: untouched.
    Current,
    /// No chain of steps lifts the call's rev to the current one: the call
    /// is kept as stored.
    Stranded,
    /// The call speaks the current rev `rev` with `args`, in order.
    Lifted {
        rev: String,
        args: Vec<Arg>,
        receipts: Vec<Receipt>,
    },
}

/// An argument of a lifted call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Arg {
    /// The stored argument at `index` (in the stored order), named `key`.
    Kept { index: usize, key: String },
    /// An argument a step added, with its JSON value.
    Added { key: String, json: String },
}

/// What a step did to the arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Receipt {
    /// The argument `from` is now named `to`.
    Renamed { from: String, to: String },
    /// `from` was not renamed: `to` was taken; both are kept.
    Clashed { from: String, to: String },
    /// `key` was missing and added.
    Filled { key: String },
}

/// The lift of each call, in order: one entry call for a transcript's
/// calls. A call's names come from a stored model reply, far below the
/// wire's longest string, so the request always fits.
#[must_use]
pub fn lift(calls: &[StoredCall<'_>]) -> Vec<Lift> {
    expect_core(Entry::CallLift, lift_calls(calls))
}

fn lift_calls(calls: &[StoredCall<'_>]) -> Result<Vec<Lift>, Error> {
    let mut request = Writer::new();
    request.count(calls.len());
    for stored in calls {
        request
            .str(stored.family)
            .str(stored.rev)
            .count(stored.keys.len());
        for key in &stored.keys {
            request.str(key);
        }
    }
    let reply = call(Entry::CallLift, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let n = reply.count()?;
    if n != calls.len() {
        return Err(WireError::Malformed {
            at: 0,
            expected: "one lift per call",
        }
        .into());
    }
    let mut lifts = Vec::with_capacity(n);
    for _ in 0..n {
        lifts.push(get_lift(&mut reply)?);
    }
    reply.end()?;
    Ok(lifts)
}

fn get_lift(reply: &mut Reader<'_>) -> Result<Lift, WireError> {
    Ok(match reply.tag_of(4, "a lift")? {
        0 => Lift::Unknown,
        1 => Lift::Current,
        2 => Lift::Stranded,
        _ => {
            let rev = reply.str()?.to_string();
            let n = reply.count()?;
            let mut args = Vec::with_capacity(n);
            for _ in 0..n {
                args.push(match reply.tag_of(2, "an argument")? {
                    0 => Arg::Kept {
                        index: usize::try_from(reply.nat()?).map_err(|_| WireError::Malformed {
                            at: 0,
                            expected: "an argument index",
                        })?,
                        key: reply.str()?.to_string(),
                    },
                    _ => Arg::Added {
                        key: reply.str()?.to_string(),
                        json: reply.str()?.to_string(),
                    },
                });
            }
            let n = reply.count()?;
            let mut receipts = Vec::with_capacity(n);
            for _ in 0..n {
                receipts.push(match reply.tag_of(3, "a receipt")? {
                    0 => Receipt::Renamed {
                        from: reply.str()?.to_string(),
                        to: reply.str()?.to_string(),
                    },
                    1 => Receipt::Clashed {
                        from: reply.str()?.to_string(),
                        to: reply.str()?.to_string(),
                    },
                    _ => Receipt::Filled {
                        key: reply.str()?.to_string(),
                    },
                });
            }
            Lift::Lifted {
                rev,
                args,
                receipts,
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::{lift, Arg, Lift, StoredCall};

    /// The shipped table: a zoom@1 call (before 9695afec6) lifts to zoom@2
    /// with its arguments as stored; current, foreign and never-existing
    /// revs are answered as such, each in its call's place.
    #[test]
    fn the_core_lifts_a_transcript() {
        let calls = [
            StoredCall {
                family: "zoom",
                rev: "1",
                keys: vec!["i", "id", "n"],
            },
            StoredCall {
                family: "edit",
                rev: "hl.1",
                keys: vec!["i", "input"],
            },
            StoredCall {
                family: "mcp",
                rev: "1",
                keys: vec![],
            },
            StoredCall {
                family: "zoom",
                rev: "0",
                keys: vec!["id"],
            },
        ];
        let kept = |index: usize, key: &str| Arg::Kept {
            index,
            key: key.to_string(),
        };
        assert_eq!(
            lift(&calls),
            vec![
                Lift::Lifted {
                    rev: "2".to_string(),
                    args: vec![kept(0, "i"), kept(1, "id"), kept(2, "n")],
                    receipts: vec![],
                },
                Lift::Current,
                Lift::Unknown,
                Lift::Stranded,
            ]
        );
    }
}
