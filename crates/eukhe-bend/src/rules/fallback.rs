//! The model a run goes on with after its model failed
//! (`bend/fallback.bend`, entry `bend/ffi_fallback.bend`;
//! `laws/fallback.bend`): a retryable failure keeps the run on its model
//! while the run's retries remain; past that the run switches to the first
//! configured candidate it has not tried, then to the first such default
//! model of a signed-in provider; with none left a usage limit holds until
//! its reset and every other failure ends, the end carrying the failure.

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
    /// The run goes on with this model, a candidate or a default.
    Switch(u64),
    /// The run waits for the usage limit's reset at `until_ms`.
    Hold { until_ms: u64 },
    /// The request ends with this failure: the cause the end report names.
    End(Why),
}

/// What the run does after its model failed for `why`, with the
/// configured candidates in order, the default models of the signed-in
/// providers in order, and the models it already tried (`F.choose`). A
/// model is any number the caller names it by; every number above the
/// wire's largest Nat saturates there.
///
/// # Errors
///
/// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
pub fn choose(
    why: Why,
    candidates: &[u64],
    defaults: &[u64],
    tried: &[u64],
) -> Result<Choice, Error> {
    let mut nats = why_nats(why);
    nats.push(u64::try_from(candidates.len()).unwrap_or(u64::MAX));
    nats.extend_from_slice(candidates);
    nats.push(u64::try_from(defaults.len()).unwrap_or(u64::MAX));
    nats.extend_from_slice(defaults);
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
        1 => Choice::Switch(offered(&mut reader, candidates, defaults)?),
        2 => Choice::Hold {
            until_ms: reader.nat()?,
        },
        // `tag_of` answers a tag below 4: this is 3.
        _ => Choice::End(read_why(&mut reader)?),
    };
    reader.end()?;
    Ok(choice)
}

/// The Nats of a failure: `0, failures, retries` | `1` | `2, until` | `3`.
fn why_nats(why: Why) -> Vec<u64> {
    match why {
        Why::Failed { failures, retries } => vec![0, failures, retries],
        Why::Login => vec![1],
        Why::Quota { until_ms } => vec![2, until_ms],
        Why::Unset => vec![3],
    }
}

/// The failure an end carries.
fn read_why(reader: &mut Reader<'_>) -> Result<Why, WireError> {
    Ok(match reader.tag_of(4, "a fallback failure")? {
        0 => Why::Failed {
            failures: reader.nat()?,
            retries: reader.nat()?,
        },
        1 => Why::Login,
        2 => Why::Quota {
            until_ms: reader.nat()?,
        },
        // `tag_of` answers a tag below 4: this is 3.
        _ => Why::Unset,
    })
}

/// The switch's model, one of the candidates or the defaults.
fn offered(
    reader: &mut Reader<'_>,
    candidates: &[u64],
    defaults: &[u64],
) -> Result<u64, WireError> {
    let model = reader.nat()?;
    if candidates
        .iter()
        .chain(defaults)
        .any(|offered| offered.min(&NAT_MAX) == &model)
    {
        Ok(model)
    } else {
        Err(WireError::Malformed {
            at: 0,
            expected: "one of the candidates or the defaults",
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{choose, Choice, Why};

    /// The choice comes from the compiled core (the rule itself is pinned
    /// by `laws/fallback.bend`).
    #[test]
    fn the_core_chooses_the_first_untried_candidate_then_default() {
        let failed = |failures| Why::Failed {
            failures,
            retries: 2,
        };
        assert_eq!(
            [
                choose(failed(2), &[4, 7], &[], &[0]).unwrap(),
                choose(failed(3), &[4, 7], &[9], &[0, 4]).unwrap(),
                choose(Why::Login, &[], &[], &[0]).unwrap(),
                choose(Why::Login, &[4], &[4, 6], &[0, 4]).unwrap(),
                choose(failed(3), &[], &[], &[0]).unwrap(),
                choose(Why::Quota { until_ms: 99 }, &[5], &[], &[0, 5]).unwrap(),
                choose(Why::Quota { until_ms: 99 }, &[5], &[], &[0]).unwrap(),
                choose(Why::Unset, &[3, 1], &[], &[]).unwrap(),
            ],
            [
                Choice::Keep,
                Choice::Switch(7),
                Choice::End(Why::Login),
                Choice::Switch(6),
                Choice::End(failed(3)),
                Choice::Hold { until_ms: 99 },
                Choice::Switch(5),
                Choice::Switch(3),
            ]
        );
    }
}
