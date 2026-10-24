//! The steps of a forced tool call (`bend/infer_force.bend`, entry
//! `bend/ffi_infer_force.bend`; `laws/infer_force.bend`, docs/inference.md
//! S6.2): the native flag of each request, and what follows each reply.
//! The caller counts the requests it made (from 0); each function encodes
//! the request, calls [`Entry::InferForce`] and decodes the decision.

use crate::wire::{Reader, Writer};
use crate::{call, expect_core, Entry, Error};

/// What the provider offers a forced call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Offer {
    /// The provider has a native forced tool choice.
    pub native: bool,
    /// Setting it costs no prompt-cache invalidation.
    pub free: bool,
}

/// A reply to a request of a forced call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reply {
    /// The reply called the forced tool.
    Called,
    /// The reply went without the call.
    Missed,
}

/// What follows a reply to a forced call (`Next`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Step {
    /// The model called the tool: the reply goes on as any other.
    Called,
    /// The reply went without the call and a retry remains.
    Retry,
    /// The last request went without the call: the forced call fails.
    Failed,
}

/// Whether request `attempt` (0: the first) of a forced call sets the
/// native forced choice (`flag`).
#[must_use]
pub fn flag(attempt: u32, offer: Offer) -> bool {
    expect_core(Entry::InferForce, flag_call(attempt, offer))
}

fn flag_call(attempt: u32, offer: Offer) -> Result<bool, Error> {
    let mut request = Writer::new();
    request
        .tag(0)
        .nat(u64::from(attempt))
        .bool(offer.native)
        .bool(offer.free);
    let reply = call(Entry::InferForce, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let flag = reader.bool()?;
    reader.end()?;
    Ok(flag)
}

/// The step after `reply`, the reply to request `attempt` (0: the first)
/// of a forced call with `retries` retries (`after`).
#[must_use]
pub fn after(attempt: u32, retries: u32, reply: Reply) -> Step {
    expect_core(Entry::InferForce, after_call(attempt, retries, reply))
}

fn after_call(attempt: u32, retries: u32, reply: Reply) -> Result<Step, Error> {
    let mut request = Writer::new();
    request
        .tag(1)
        .nat(u64::from(attempt))
        .nat(u64::from(retries))
        .bool(reply == Reply::Called);
    let reply = call(Entry::InferForce, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let step = match reader.tag_of(3, "a forced call's step")? {
        0 => Step::Called,
        1 => Step::Retry,
        // `tag_of` answers a tag below 3: this is 2.
        _ => Step::Failed,
    };
    reader.end()?;
    Ok(step)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Each step comes from the compiled core: the first request sets the
    /// flag only when it is free, a retry whenever the provider has one; a
    /// miss retries within the retries and fails past them.
    #[test]
    fn the_forced_call_steps_come_from_the_compiled_core() {
        let offer = Offer {
            native: true,
            free: false,
        };
        assert_eq!(
            (
                flag(0, offer),
                flag(1, offer),
                after(0, 1, Reply::Missed),
                after(1, 1, Reply::Missed),
                after(1, 1, Reply::Called),
            ),
            (false, true, Step::Retry, Step::Failed, Step::Called)
        );
    }
}
