//! The cache-mark budget of one provider request (`bend/cache_marks.bend`,
//! entry `bend/ffi_cache_marks.bend`; `laws/cache_marks.bend`): a request
//! carries at most four cache marks; the marks on its messages (the marked
//! user text blocks and the end-of-request mark) come first, and the
//! provider's optional marks take the slots left, in its priority order,
//! each only when the request wants it. More than three marked blocks is a
//! caller bug the request fails with ([`excess`]).

use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error};

/// The error text of a request that marks `marked` user text blocks, when
/// that is more than one request may carry.
#[must_use]
pub fn excess(marked: usize) -> Option<String> {
    expect_core(Entry::CacheMarks, excess_call(marked))
}

fn excess_call(marked: usize) -> Result<Option<String>, Error> {
    let mut request = Writer::new();
    request.tag(0).nat(saturated(marked));
    let reply = call(Entry::CacheMarks, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let error = if reader.maybe()? {
        Some(reader.str()?.to_owned())
    } else {
        None
    };
    reader.end()?;
    Ok(error)
}

/// Which of the optional marks `wants` (in the provider's priority order)
/// the request carries after `placed` marks on its messages.
#[must_use]
pub fn grant<const N: usize>(placed: usize, wants: [bool; N]) -> [bool; N] {
    expect_core(Entry::CacheMarks, grant_call(placed, wants))
}

fn grant_call<const N: usize>(placed: usize, wants: [bool; N]) -> Result<[bool; N], Error> {
    let mut request = Writer::new();
    request.tag(1).nat(saturated(placed)).count(N);
    for want in wants {
        request.bool(want);
    }
    let reply = call(Entry::CacheMarks, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    if reader.count()? != N {
        return Err(WireError::Malformed {
            at: 0,
            expected: "one answer per wanted mark",
        }
        .into());
    }
    let mut granted = [false; N];
    for slot in &mut granted {
        *slot = reader.bool()?;
    }
    reader.end()?;
    Ok(granted)
}

/// A count as the wire carries it: a count past [`NAT_MAX`] is as far past
/// every limit of the budget as `NAT_MAX` itself.
fn saturated(count: usize) -> u64 {
    u64::try_from(count).map_or(NAT_MAX, |count| count.min(NAT_MAX))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The budget comes from the compiled core: after one placed mark three
    /// wanted marks fit and an unwanted one spends nothing; four marked
    /// blocks are too many, three are not.
    #[test]
    fn the_core_decides_the_cache_marks() {
        assert_eq!(
            (
                grant(1, [true, false, true, true, true]),
                excess(3),
                excess(4)
            ),
            (
                [true, false, true, true, false],
                None,
                Some(
                    "Too many cache breakpoints: the request marks 4 blocks, at most 3 are allowed"
                        .to_owned()
                )
            )
        );
    }
}
