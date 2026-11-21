//! The model a run goes on with after its model failed
//! (`bend/fallback.bend`, entry `bend/ffi_fallback.bend`;
//! `laws/fallback.bend`): a retryable failure keeps the run on its model
//! while the run's retries remain; past that the run switches to the first
//! candidate it has not tried; with none left a usage limit holds until its
//! reset and every other failure ends.

use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, Entry, Error};

/// Why the model cannot go on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Why {
    /// The `failures`-th retryable failure in a row of the model, with the
    /// run's `retries` (`retry.maxRetries`, 0 when retries are off).
    Failed { failures: u64, retries: u64 },
    /// The model's provider has no usable login: it expired and its
    /// refresh failed, or the provider has no key.
    Login,
    /// The provider's usage limit holds until `until_ms` (epoch ms).
    Quota { until_ms: u64 },
    /// No model was chosen.
    Unset,
}

/// What the run does.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Choice {
    /// The run's own retry goes on with the model.
    Keep,
    /// The run goes on with this candidate.
    Switch(u64),
    /// The run waits for the usage limit's reset at `until_ms`.
    Hold { until_ms: u64 },
    /// The request ends with the failure.
    End,
}

/// What the run does after its model failed for `why`, with the
/// candidates in order and the models it already tried (`F.choose`). A
/// model is any number the caller names it by; every number above the
/// wire's largest Nat saturates there.
///
/// # Errors
///
/// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
pub fn choose(why: Why, candidates: &[u64], tried: &[u64]) -> Result<Choice, Error> {
    let mut nats: Vec<u64> = match why {
        Why::Failed { failures, retries } => vec![0, failures, retries],
        Why::Login => vec![1],
        Why::Quota { until_ms } => vec![2, until_ms],
        Why::Unset => vec![3],
    };
    nats.push(u64::try_from(candidates.len()).unwrap_or(u64::MAX));
    nats.extend_from_slice(candidates);
    nats.extend_from_slice(tried);
    let mut request = Writer::new();
    request.count(nats.len());
    for nat in nats {
        request.nat(nat.min(NAT_MAX));
    }
    let reply = call(Entry::Fallback, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let choice = match reader.tag_of(4, "a fallback choice")? {
        0 => Choice::Keep,
        1 => Choice::Switch(candidate(&mut reader, candidates)?),
        2 => Choice::Hold {
            until_ms: reader.nat()?,
        },
        // `tag_of` answers a tag below 4: this is 3.
        _ => Choice::End,
    };
    reader.end()?;
    Ok(choice)
}

/// The switch's model, one of the candidates.
fn candidate(reader: &mut Reader<'_>, candidates: &[u64]) -> Result<u64, WireError> {
    let model = reader.nat()?;
    if candidates
        .iter()
        .any(|candidate| candidate.min(&NAT_MAX) == &model)
    {
        Ok(model)
    } else {
        Err(WireError::Malformed {
            at: 0,
            expected: "one of the candidates",
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{choose, Choice, Why};

    /// The choice comes from the compiled core (the rule itself is pinned
    /// by `laws/fallback.bend`).
    #[test]
    fn the_core_chooses_the_first_untried_candidate() {
        let failed = |failures| Why::Failed {
            failures,
            retries: 2,
        };
        assert_eq!(
            [
                choose(failed(2), &[4, 7], &[0]).unwrap(),
                choose(failed(3), &[4, 7], &[0, 4]).unwrap(),
                choose(Why::Login, &[], &[0]).unwrap(),
                choose(Why::Quota { until_ms: 99 }, &[5], &[0, 5]).unwrap(),
                choose(Why::Quota { until_ms: 99 }, &[5], &[0]).unwrap(),
                choose(Why::Unset, &[3, 1], &[]).unwrap(),
            ],
            [
                Choice::Keep,
                Choice::Switch(7),
                Choice::End,
                Choice::Hold { until_ms: 99 },
                Choice::Switch(5),
                Choice::Switch(3),
            ]
        );
    }
}
