//! The account of one provider a run goes on with (`bend/account.bend`,
//! entry `bend/ffi_account.bend`; `laws/account.bend`): the first usable
//! account in order; with none usable, the earliest limit to reset: a wait
//! for it within the run's wait limit while the run may still wait, else
//! a hand-off to the model fallback with that reset; with no account
//! limited, no login is left.

use crate::wire::{Reader, Writer, NAT_MAX};
use crate::{call, Entry, Error};

/// The state of one account.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mark {
    /// Usable.
    Free,
    /// Its usage limit holds until `until_ms` (epoch ms); usable from then.
    Until { until_ms: u64 },
    /// Its login cannot refresh.
    Dead,
}

/// What the run does.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Choice {
    /// It goes on now with the account at this place.
    Use(u64),
    /// It waits until `until_ms`, then goes on with the account at `at`.
    Hold { at: u64, until_ms: u64 },
    /// Every account is limited past the wait: the account at `at` resets
    /// first, at `until_ms`.
    Quota { at: u64, until_ms: u64 },
    /// No login is left.
    Login,
}

/// The account the run goes on with at `now_ms`, with the run's wait
/// limit `cap_ms`, the `waits` it has left and the accounts' marks in
/// order (`A.choose`). Every number above the wire's largest Nat
/// saturates there.
///
/// # Errors
///
/// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
pub fn choose(now_ms: u64, cap_ms: u64, waits: u64, marks: &[Mark]) -> Result<Choice, Error> {
    let mut nats: Vec<u64> = vec![now_ms, cap_ms, waits];
    for mark in marks {
        match mark {
            Mark::Free => nats.push(0),
            Mark::Until { until_ms } => nats.extend([1, *until_ms]),
            Mark::Dead => nats.push(2),
        }
    }
    let mut request = Writer::new();
    request.count(nats.len());
    for nat in nats {
        request.nat(nat.min(NAT_MAX));
    }
    let reply = call(Entry::Account, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let choice = match reader.tag_of(4, "an account choice")? {
        0 => Choice::Use(reader.nat()?),
        1 => Choice::Hold {
            at: reader.nat()?,
            until_ms: reader.nat()?,
        },
        2 => Choice::Quota {
            at: reader.nat()?,
            until_ms: reader.nat()?,
        },
        // `tag_of` answers a tag below 4: this is 3.
        _ => Choice::Login,
    };
    reader.end()?;
    Ok(choice)
}

#[cfg(test)]
mod tests {
    use super::{choose, Choice, Mark};

    /// The choice comes from the compiled core (the rule itself is pinned
    /// by `laws/account.bend`).
    #[test]
    fn the_core_chooses_the_first_usable_account() {
        let until = |until_ms| Mark::Until { until_ms };
        assert_eq!(
            [
                choose(10, 25, 1, &[Mark::Dead, until(50), Mark::Free]).unwrap(),
                choose(10, 25, 1, &[until(40), until(30)]).unwrap(),
                choose(10, 25, 0, &[until(40), until(30)]).unwrap(),
                choose(10, 25, 1, &[Mark::Dead]).unwrap(),
            ],
            [
                Choice::Use(2),
                Choice::Hold {
                    at: 1,
                    until_ms: 30
                },
                Choice::Quota {
                    at: 1,
                    until_ms: 30
                },
                Choice::Login,
            ]
        );
    }
}
