//! Which compaction threshold a request's context is over
//! (`bend/infer_threshold.bend`, entry `bend/ffi_infer_threshold.bend`;
//! `laws/infer_threshold.bend`). The caller counts
//! the context's tokens and gives the policy's reserve and margin in whole
//! tokens ([`whole`]); [`Compaction::over`] encodes them, calls
//! [`Entry::InferThreshold`] and decodes the decision.

use crate::wire::{Reader, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error};

/// The threshold a context is over (`Over`).
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
    /// The threshold a context of `tokens` tokens is over (`over`).
    #[must_use]
    pub fn over(self, tokens: u64) -> Over {
        expect_core(Entry::InferThreshold, self.over_call(tokens))
    }

    fn over_call(self, tokens: u64) -> Result<Over, Error> {
        let mut request = Writer::new();
        request
            .bool(self.enabled)
            .nat(tokens.min(NAT_MAX))
            .nat(self.window.min(NAT_MAX));
        signed(&mut request, self.reserve);
        signed(&mut request, self.margin);
        let reply = call(Entry::InferThreshold, &request.finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let over = match reader.tag_of(3, "a compaction threshold")? {
            0 => Over::Under,
            1 => Over::Background,
            // `tag_of` answers a tag below 3: this is 2.
            _ => Over::Blocking,
        };
        reader.end()?;
        Ok(over)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The decision comes from the compiled core: window 10, reserve 2
    /// (limit 8), margin 3; a negative reserve -3 (limit 13) blocks above
    /// it only. Reserve and margin round up, NaN reads 0.
    #[test]
    fn the_compaction_threshold_comes_from_the_compiled_core() {
        let policy = Compaction {
            enabled: true,
            window: 10,
            reserve: 2,
            margin: 3,
        };
        let negative = Compaction {
            reserve: -3,
            margin: 0,
            ..policy
        };
        assert_eq!(
            (
                [5, 6, 9].map(|tokens| policy.over(tokens)),
                [13, 14].map(|tokens| negative.over(tokens)),
                [whole(2.5), whole(-2.5), whole(f64::NAN), whole(-0.5)],
            ),
            (
                [Over::Under, Over::Background, Over::Blocking],
                [Over::Under, Over::Blocking],
                [3, -2, 0, 0],
            )
        );
    }
}
