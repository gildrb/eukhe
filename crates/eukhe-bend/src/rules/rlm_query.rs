//! rlm.query admission and result cut (`bend/rlm_query.bend`, entry
//! `bend/ffi_rlm_query.bend`; `laws/rlm_query.bend`, spec
//! `spec/rlm/query.bend`). A batch of `rlm.query` calls is admitted whole or
//! refused: first over the session's query budget, then for a full
//! concurrency cap; an admitted batch runs in waves, one after another,
//! each at most the room under the cap and the caller's width. A result
//! past its limit is cut after its longest prefix of whole chars within the
//! limit in UTF-8 bytes.
//!
//! Numbers the wire cannot carry (above [`NAT_MAX`]) are saturated to
//! [`NAT_MAX`], below the runtime's bound on a Nat ([`CORE_NAT_MAX`]). The
//! core tests the budget by taking each size from what is left of it, so
//! no sum is formed there; only a refusal for the budget sums the sizes, to
//! name them. A batch whose saturated sizes add up past [`CORE_NAT_MAX`]
//! under a set budget would stop the process there, so [`plan`] refuses it
//! with [`PlanError::TooLarge`] before the call. This is a trusted boundary:
//! the laws reason about unbounded numbers and cannot see the runtime's.

use crate::wire::{Reader, Writer, NAT_MAX, STR_MAX};
use crate::{call, expect_core, Entry, Error};

/// The largest Nat the compiled core holds (2^48 - 1): forming a larger one
/// stops the process.
pub const CORE_NAT_MAX: u64 = (1 << 48) - 1;

/// Why a batch has no decision.
#[derive(Debug, thiserror::Error)]
pub enum PlanError {
    /// Under a set budget the batch's input bytes, each saturated to
    /// [`NAT_MAX`], add up past [`CORE_NAT_MAX`]: the core would name that
    /// sum in its refusal and stop the process, so it is not asked.
    #[error(
        "rlm.query batch of {calls} calls sends more input bytes than the compiled core can count ({CORE_NAT_MAX})"
    )]
    TooLarge { calls: usize },
    /// The compiled core failed (an inconsistent build).
    #[error("the compiled Bend core failed on rlm.query: {0}")]
    Core(#[from] Error),
}

/// The facts a batch of rlm.query calls is admitted on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlanFacts<'a> {
    /// The session's query calls in flight now.
    pub running: u64,
    /// The session's query concurrency cap.
    pub cap: u64,
    /// The caller's `concurrency=`; 0: as wide as allowed.
    pub width: u64,
    /// `rlm.queryBudgetBytes`; 0: no budget.
    pub budget: u64,
    /// The input bytes the session's queries already sent.
    pub used: u64,
    /// The input bytes of each call of the batch, in order.
    pub sizes: &'a [u64],
}

/// The decision on a batch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Plan {
    /// The batch runs in waves, one after another: wave `i` runs the next
    /// `waves[i]` calls of the batch at once. Every call is in one wave.
    Admit { waves: Vec<usize> },
    /// Nothing runs; the text says why (the error the caller shows).
    Refuse(String),
}

/// Where a result is cut.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cut {
    /// The whole text is within the limit.
    Fits,
    /// Keep the text's first bytes up to this index: a char boundary, at
    /// most the limit.
    At(usize),
}

/// The decision on the batch `facts`, from the compiled core.
///
/// # Errors
///
/// [`PlanError::TooLarge`] when a budget is set and the sizes, each
/// saturated to [`NAT_MAX`], add up past [`CORE_NAT_MAX`] (the core is not
/// called); [`PlanError::Core`] when the core fails.
pub fn plan(facts: &PlanFacts<'_>) -> Result<Plan, PlanError> {
    let countable = facts
        .sizes
        .iter()
        .try_fold(0u64, |sum, size| {
            sum.checked_add((*size).min(NAT_MAX))
                .filter(|sum| *sum <= CORE_NAT_MAX)
        })
        .is_some();
    if facts.budget > 0 && !countable {
        return Err(PlanError::TooLarge {
            calls: facts.sizes.len(),
        });
    }
    Ok(plan_call(facts)?)
}

fn plan_call(facts: &PlanFacts<'_>) -> Result<Plan, Error> {
    let mut request = Writer::new();
    request
        .tag(0)
        .nat(facts.running.min(NAT_MAX))
        .nat(facts.cap.min(NAT_MAX))
        .nat(facts.width.min(NAT_MAX))
        .nat(facts.budget.min(NAT_MAX))
        .nat(facts.used.min(NAT_MAX))
        .count(facts.sizes.len());
    for size in facts.sizes {
        request.nat((*size).min(NAT_MAX));
    }
    let reply = call(Entry::RlmQuery, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let plan = if reader.tag_of(2, "an rlm.query plan")? == 0 {
        let n = reader.count()?;
        let mut waves = Vec::with_capacity(n);
        for _ in 0..n {
            waves.push(reader.count()?);
        }
        Plan::Admit { waves }
    } else {
        Plan::Refuse(reader.str()?.to_owned())
    };
    reader.end()?;
    Ok(plan)
}

/// Where `text` is cut under `max_bytes` UTF-8 bytes, from the compiled
/// core. The text goes to the core in pieces of at most [`STR_MAX`] chars,
/// and of at most one char more than the room left (a char takes a byte at
/// least, so a longer piece cannot fit): a piece that is cut decides the
/// cut, a piece that fits leaves the room less its bytes to the rest
/// (`rlm_query_cut_append`).
#[must_use]
pub fn cut(max_bytes: u64, text: &str) -> Cut {
    let mut room = max_bytes.min(NAT_MAX);
    let mut at = 0;
    let mut rest = text;
    loop {
        let limit = usize::try_from(room).map_or(STR_MAX, |r| r.saturating_add(1).min(STR_MAX));
        let piece = rest
            .char_indices()
            .nth(limit)
            .map_or(rest, |(end, _)| &rest[..end]);
        match expect_core(Entry::RlmQuery, cut_call(room, piece)) {
            Cut::At(k) => return Cut::At(at + k),
            Cut::Fits if piece.len() == rest.len() => return Cut::Fits,
            Cut::Fits => {
                at += piece.len();
                room = room.saturating_sub(u64::try_from(piece.len()).unwrap_or(u64::MAX));
                rest = &rest[piece.len()..];
            }
        }
    }
}

fn cut_call(room: u64, piece: &str) -> Result<Cut, Error> {
    let mut request = Writer::new();
    request.tag(1).nat(room).str(piece);
    let reply = call(Entry::RlmQuery, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let cut = if reader.tag_of(2, "an rlm.query cut")? == 0 {
        Cut::Fits
    } else {
        Cut::At(reader.count()?)
    };
    reader.end()?;
    Ok(cut)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn facts(running: u64, width: u64, budget: u64, used: u64, sizes: &[u64]) -> PlanFacts<'_> {
        PlanFacts {
            running,
            cap: 4,
            width,
            budget,
            used,
            sizes,
        }
    }

    fn decide(facts: &PlanFacts<'_>) -> Plan {
        plan(facts).expect("the core decides")
    }

    fn admit(waves: &[usize]) -> Plan {
        Plan::Admit {
            waves: waves.to_vec(),
        }
    }

    /// The anchors of `rlm_query_plan_example` and `rlm_query_text_example`:
    /// ten calls under the cap 4 run 4, 4, 2; with width 3, 3, 3, 3, 1;
    /// with 3 of 4 running, one at a time; a batch over budget and a full
    /// cap are refused; a budget exactly met admits; no calls, no waves.
    #[test]
    fn the_core_plans_batches() {
        let ten = [1; 10];
        assert_eq!(
            [
                decide(&facts(0, 0, 0, 0, &ten)),
                decide(&facts(0, 3, 0, 0, &ten)),
                decide(&facts(3, 0, 0, 0, &[1, 1, 1])),
                decide(&facts(0, 0, 10, 4, &[5, 5])),
                decide(&facts(0, 0, 10, 4, &[3, 3])),
                decide(&facts(4, 0, 0, 0, &[1])),
                decide(&facts(0, 0, 0, 0, &[])),
            ],
            [
                admit(&[4, 4, 2]),
                admit(&[3, 3, 3, 1]),
                admit(&[1, 1, 1]),
                Plan::Refuse(
                    "rlm.query needs 10 bytes of input; the session's query budget has 6 of 10 bytes left (rlm.queryBudgetBytes)"
                        .to_owned()
                ),
                admit(&[2]),
                Plan::Refuse("rlm.query concurrency limit 4 is already full".to_owned()),
                admit(&[]),
            ]
        );
    }

    /// Regression (ATTACK `0,0,4,0,0,0,3,99999999999999,...` and
    /// `0,0,4,0,1000000,0,1,5,`): numbers that pass the runtime's 2^48 - 1
    /// when added never stop the process. A large budget, or no budget with
    /// sizes adding up past it, decides; spent bytes plus sizes past it
    /// decide; a refusal naming exactly 2^48 - 1 bytes decides; one byte
    /// more under a set budget is refused before the core is asked.
    #[test]
    fn sums_past_the_core_bound_never_stop_the_process() {
        let huge = [NAT_MAX, NAT_MAX, u64::MAX];
        let edge = [NAT_MAX, NAT_MAX, CORE_NAT_MAX - 2 * NAT_MAX];
        let past = [NAT_MAX, NAT_MAX, CORE_NAT_MAX - 2 * NAT_MAX + 1];
        assert_eq!(
            [
                decide(&facts(0, 0, 1_000_000, 0, &[5])),
                decide(&facts(0, 0, 0, 0, &huge)),
                decide(&facts(0, 0, NAT_MAX, NAT_MAX, &[NAT_MAX, 1, 1])),
                decide(&facts(0, 0, 1, NAT_MAX, &edge)),
            ],
            [
                admit(&[1]),
                admit(&[3]),
                Plan::Refuse(
                    "rlm.query needs 100000000000001 bytes of input; the session's query budget has 0 of 99999999999999 bytes left (rlm.queryBudgetBytes)"
                        .to_owned()
                ),
                Plan::Refuse(
                    "rlm.query needs 281474976710655 bytes of input; the session's query budget has 0 of 1 bytes left (rlm.queryBudgetBytes)"
                        .to_owned()
                ),
            ]
        );
        assert!(matches!(
            plan(&facts(0, 0, 1, 0, &past)),
            Err(PlanError::TooLarge { calls: 3 })
        ));
        assert!(matches!(
            plan(&facts(0, 0, 1, 0, &huge)),
            Err(PlanError::TooLarge { calls: 3 })
        ));
    }

    /// The anchors of `rlm_query_cut_example`: "héllo" under 2 keeps "h",
    /// "ab" under 2 fits, an emoji past the limit is dropped whole, and the
    /// chars U+7F, U+80, U+7FF, U+800, U+FFFF, U+10000 take 1, 2, 2, 3, 3
    /// and 4 bytes.
    #[test]
    fn the_core_cuts_results() {
        let wide = "\u{7f}\u{80}\u{7ff}\u{800}\u{ffff}\u{10000}";
        assert_eq!(
            [
                cut(2, "héllo"),
                cut(2, "ab"),
                cut(3, "a😀"),
                cut(0, "a"),
                cut(1, wide),
                cut(4, wide),
                cut(5, wide),
                cut(10, wide),
                cut(14, wide),
                cut(15, wide),
            ],
            [
                Cut::At(1),
                Cut::Fits,
                Cut::At(1),
                Cut::At(0),
                Cut::At(1),
                Cut::At(3),
                Cut::At(5),
                Cut::At(8),
                Cut::At(11),
                Cut::Fits,
            ]
        );
    }

    /// A text past [`STR_MAX`] chars goes in pieces and cuts as the whole.
    #[test]
    fn a_long_text_cuts_in_pieces() {
        let text = "é".repeat(STR_MAX + 3);
        let all = u64::try_from(text.len()).unwrap_or(u64::MAX);
        assert_eq!(
            [cut(all, &text), cut(all - 1, &text), cut(5, &text)],
            [Cut::Fits, Cut::At(text.len() - 2), Cut::At(4)]
        );
    }
}
