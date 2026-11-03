//! Which compaction threshold a request compacts at and where a compaction
//! cuts (`bend/infer_threshold.bend` `plan`, entry
//! `bend/ffi_infer_threshold.bend`; `laws/infer_threshold.bend`). A
//! compaction runs once the context actually crossed a threshold: the
//! thresholds read the tokens the last turn reached, and the request only
//! has to stay within the window. The caller counts the request's tokens
//! and the last turn's, sizes the entries after the head and gives the
//! policy's reserve and margin in whole tokens ([`whole`]);
//! [`Compaction::plan`] encodes them, calls [`Entry::InferThreshold`] and
//! decodes the decision.

use crate::wire::{Reader, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error};

/// The threshold a request compacts at (`Over`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Over {
    /// None: no compaction.
    Under,
    /// The background threshold: compaction runs beside the request.
    Background,
    /// The blocking threshold: the request waits for compaction.
    Blocking,
}

/// The compaction policy as the decision reads it, in whole tokens.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Compaction {
    /// Automatic compaction is on.
    pub enabled: bool,
    /// The model's context window; 0: unknown.
    pub window: u64,
    /// The room kept free for the answer: the limit is `window - reserve`.
    pub reserve: i64,
    /// How far below the limit background compaction starts; a margin
    /// that is not positive never starts it.
    pub margin: i64,
    /// The most tokens a compaction keeps (`keepRecentTokens`).
    pub keep: u64,
}

/// The transcript after the compaction head, as the cut reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range<'a> {
    /// The request's tokens: it blocks past the window, and a compaction
    /// cuts them down to the target.
    pub tokens: u64,
    /// The tokens the last turn since the head reached (its request and
    /// answer, as the provider counted them): the thresholds read them.
    /// 0 reads no turn: none since the head, or a later request of the
    /// same run (a turn compacts once it ended).
    pub last: u64,
    /// The entries' tokens, newest first.
    pub sizes: &'a [u64],
    /// The numbers of newest entries a cut may keep (`k`: the cut keeps
    /// the `k` newest entries), in any order.
    pub cuts: &'a [u64],
    /// A cut keeping `k` entries leaves something to summarize when
    /// `k < full`: the oldest entry with a message is the `full`-th
    /// newest (0: no entry has one).
    pub full: u64,
}

/// The decision for one context (`Plan`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Plan {
    /// The threshold the context compacts at.
    pub over: Over,
    /// How many of the newest entries a compaction keeps; `None`: no cut.
    pub cut: Option<u64>,
}

/// A token count of the policy in whole tokens: rounded up, NaN as 0,
/// saturated at the ends of `i64`. A context of whole tokens is compared
/// strictly with the policy's thresholds (`tokens > window - reserve`,
/// `tokens > window - reserve - margin`), so a reserve rounded up decides
/// exactly as itself, and so does a margin when the reserve is whole.
#[must_use]
#[expect(
    clippy::cast_possible_truncation,
    reason = "a float to integer cast saturates, and reads NaN as 0"
)]
pub fn whole(tokens: f64) -> i64 {
    tokens.ceil() as i64
}

/// A whole number on the wire (`Z`): 0 then n for n, 1 then n for -(1+n);
/// magnitudes past [`NAT_MAX`] saturate (no context reaches 10^14 tokens).
fn signed(request: &mut Writer, n: i64) {
    match u64::try_from(n) {
        Ok(up) => request.tag(0).nat(up.min(NAT_MAX)),
        Err(_) => request.tag(1).nat((-(n + 1)).unsigned_abs().min(NAT_MAX)),
    };
}

impl Compaction {
    /// The threshold `range` compacts at and where a compaction cuts it
    /// (`plan`).
    #[must_use]
    pub fn plan(self, range: &Range<'_>) -> Plan {
        expect_core(Entry::InferThreshold, self.plan_call(range))
    }

    fn plan_call(self, range: &Range<'_>) -> Result<Plan, Error> {
        let mut request = Writer::new();
        request
            .bool(self.enabled)
            .nat(range.tokens.min(NAT_MAX))
            .nat(range.last.min(NAT_MAX))
            .nat(self.window.min(NAT_MAX));
        signed(&mut request, self.reserve);
        signed(&mut request, self.margin);
        request
            .nat(self.keep.min(NAT_MAX))
            .nat(range.full.min(NAT_MAX))
            .count(range.sizes.len());
        for size in range.sizes {
            request.nat((*size).min(NAT_MAX));
        }
        request.count(range.cuts.len());
        for cut in range.cuts {
            request.nat((*cut).min(NAT_MAX));
        }
        let reply = call(Entry::InferThreshold, &request.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let over = match reader.tag_of(3, "a compaction threshold")? {
            0 => Over::Under,
            1 => Over::Background,
            // `tag_of` answers a tag below 3: this is 2.
            _ => Over::Blocking,
        };
        let cut = if reader.maybe()? {
            Some(reader.nat()?)
        } else {
            None
        };
        reader.end()?;
        Ok(Plan { over, cut })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The decision comes from the compiled core: window 10, reserve 2
    /// (start 6, target 3), margin 3, keep 9, two entries of 1 and 3
    /// tokens (newest first) and a cut that keeps the newest: after a turn
    /// of 5 a request of 5 or 9 is under, after a turn of 6 a request of 6
    /// compacts early as the cut brings it to the target, after a turn of
    /// 9 it blocks, and a request of 11 blocks after any turn; without a
    /// cut nothing compacts. Reserve and margin round up, NaN reads 0.
    #[test]
    fn the_compaction_plan_comes_from_the_compiled_core() {
        let policy = Compaction {
            enabled: true,
            window: 10,
            reserve: 2,
            margin: 3,
            keep: 9,
        };
        let range = |tokens, last, cuts| Range {
            tokens,
            last,
            sizes: &[1, 3],
            cuts,
            full: 2,
        };
        let cut = |over| Plan { over, cut: Some(1) };
        assert_eq!(
            (
                [(5, 5), (9, 5), (6, 6), (9, 9), (11, 0)]
                    .map(|(tokens, last)| policy.plan(&range(tokens, last, &[1]))),
                policy.plan(&range(9, 9, &[])),
                [whole(2.5), whole(-2.5), whole(f64::NAN), whole(-0.5)],
            ),
            (
                [
                    cut(Over::Under),
                    cut(Over::Under),
                    cut(Over::Background),
                    cut(Over::Blocking),
                    cut(Over::Blocking)
                ],
                Plan {
                    over: Over::Under,
                    cut: None
                },
                [3, -2, 0, 0],
            )
        );
    }
}
