//! The retry decisions (`bend/retry.bend`, entry `bend/ffi_retry.bend`;
//! `laws/retry.bend`): the classifier of a failed request, the
//! wait before a retry, the failover walk over a provider chain, and the
//! idle deadline after a stall; and the stream-idle deadline's decisions
//! (entry `bend/ffi_retry_idle.bend`; `laws/retry_idle.bend`): whether it
//! is armed, and what its timer does when it fires. Each function encodes
//! its input, calls [`Entry::Retry`] or [`Entry::RetryIdle`] and decodes
//! the reply; every number is saturated at the wire's largest Nat
//! ([`NAT_MAX`]) first, where the laws state the model's answer does not
//! change (or saturates with it).

use crate::wire::{Reader, Writer, NAT_MAX};
use crate::{call, Entry, Error};

/// The kind a stream failure recorded, in the order of `Cause` in
/// `bend/retry.bend` (its wire tag).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cause {
    Refusal,
    Safety,
    PaymentRequired,
    Overloaded,
    RateLimit,
    ServerError,
    Auth,
    Permission,
    InvalidRequest,
    MalformedResponse,
    StreamDrop,
    StreamStalled,
    StreamRepeating,
    Unknown,
}

impl Cause {
    const fn tag(self) -> u64 {
        match self {
            Cause::Refusal => 0,
            Cause::Safety => 1,
            Cause::PaymentRequired => 2,
            Cause::Overloaded => 3,
            Cause::RateLimit => 4,
            Cause::ServerError => 5,
            Cause::Auth => 6,
            Cause::Permission => 7,
            Cause::InvalidRequest => 8,
            Cause::MalformedResponse => 9,
            Cause::StreamDrop => 10,
            Cause::StreamStalled => 11,
            Cause::StreamRepeating => 12,
            Cause::Unknown => 13,
        }
    }
}

/// What the classifier reads of a failed request (`R.Facts`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Facts {
    pub parked: bool,
    pub limit: bool,
    pub status: Option<u16>,
    pub kind: Option<Cause>,
    pub transient_text: bool,
}

/// Whether a retry may cure the failure (`R.retryable`).
///
/// # Errors
///
/// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
pub fn retryable(facts: Facts) -> Result<bool, Error> {
    let mut request = Writer::new();
    request.tag(0).bool(facts.parked).bool(facts.limit);
    match facts.status {
        Some(status) => request.some().nat(u64::from(status)),
        None => request.none(),
    };
    match facts.kind {
        Some(kind) => request.some().nat(kind.tag()),
        None => request.none(),
    };
    request.bool(facts.transient_text);
    let reply = call(Entry::Retry, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let retry = reply.bool()?;
    reply.end()?;
    Ok(retry)
}

/// What the wait of a retry reads (`R.retry_wait`), in whole ms.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WaitInput {
    /// The policy's base step.
    pub base_ms: u64,
    /// The retry: 1 for the first.
    pub attempt: u32,
    /// The policy's cap; `0`: no cap on the server's wait.
    pub cap_ms: u64,
    /// A draw uniform in [0, 2^46): the jitter is the draw modulo the step.
    pub draw: u64,
    /// The server's requested wait, if any.
    pub server_ms: Option<u64>,
}

/// When the retry may go out (`R.Delay`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Wait {
    /// After this many ms: never before the server's wait.
    After(u64),
    /// The server asked for `server_ms`, more than the cap `cap_ms`.
    Refused { server_ms: u64, cap_ms: u64 },
}

/// The wait of a retry (`R.retry_wait`): the jitter of the draw under the
/// step (the base doubled per retry before this one, at most the cap),
/// never before the server's wait, refused past a positive cap.
///
/// # Errors
///
/// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
pub fn wait(input: WaitInput) -> Result<Wait, Error> {
    let mut request = Writer::new();
    request
        .tag(1)
        .nat(input.base_ms.min(NAT_MAX))
        .nat(u64::from(input.attempt))
        .nat(input.cap_ms.min(NAT_MAX))
        .nat(input.draw.min(NAT_MAX));
    match input.server_ms {
        Some(ms) => request.some().nat(ms.min(NAT_MAX)),
        None => request.none(),
    };
    let reply = call(Entry::Retry, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let wait = if reply.tag_of(2, "a Delay")? == 0 {
        Wait::After(reply.nat()?)
    } else {
        Wait::Refused {
            server_ms: reply.nat()?,
            cap_ms: reply.nat()?,
        }
    };
    reply.end()?;
    Ok(wait)
}

/// One failed attempt of a request (`R.Tried`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Tried {
    /// The chain index of its provider.
    pub at: usize,
    /// The wait its server asked for, if any (ms).
    pub server_wait_ms: Option<u64>,
}

/// The failover policy (`R.Policy`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Policy {
    pub max_switches: u32,
    pub base_delay_ms: u64,
    pub max_delay_ms: u64,
}

/// The next attempt (`R.Switch`): the chain index, after `delay_ms`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Switch {
    pub to: usize,
    pub delay_ms: u64,
}

/// The next attempt of a request whose chain holds `len` providers, after
/// the failed attempts `tried`, oldest first (`R.next`).
///
/// # Errors
///
/// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
pub fn next_switch(len: usize, tried: &[Tried], policy: Policy) -> Result<Option<Switch>, Error> {
    let mut request = Writer::new();
    request.tag(2).count(len).count(tried.len());
    for attempt in tried {
        request.count(attempt.at);
        match attempt.server_wait_ms {
            Some(ms) => request.some().nat(ms.min(NAT_MAX)),
            None => request.none(),
        };
    }
    request
        .nat(u64::from(policy.max_switches))
        .nat(policy.base_delay_ms.min(NAT_MAX))
        .nat(policy.max_delay_ms.min(NAT_MAX));
    let reply = call(Entry::Retry, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let next = if reply.maybe()? {
        Some(Switch {
            to: reply.count()?,
            delay_ms: reply.nat()?,
        })
    } else {
        None
    };
    reply.end()?;
    Ok(next)
}

/// The idle deadline (ms) of the retry after a stream stalled under
/// `idle_ms` (`R.stall.next`): twice it. The deadline saturates at half the
/// wire's largest Nat, so twice it stays one.
///
/// # Errors
///
/// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
pub fn idle_after_stall(idle_ms: u64) -> Result<u64, Error> {
    let mut request = Writer::new();
    request.tag(3).nat(idle_ms.min(NAT_MAX / 2));
    let reply = call(Entry::Retry, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let idle = reply.nat()?;
    reply.end()?;
    Ok(idle)
}

/// Whether `stream_idle_timeout_ms` arms the stream-idle deadline
/// (`R.idle.arm`, entry `bend/ffi_retry_idle.bend`): NaN, a negative
/// number and 0 disable it. The facts of the number go to the core: NaN,
/// negative, its whole part (saturated at [`NAT_MAX`]), a fraction.
///
/// # Errors
///
/// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
pub fn idle_armed(timeout_ms: f64) -> Result<bool, Error> {
    let magnitude = timeout_ms.abs();
    #[expect(
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "a whole, non-negative f64 saturates into u64; the wire saturates it once more"
    )]
    let whole = (magnitude.trunc() as u64).min(NAT_MAX);
    let mut request = Writer::new();
    request
        .tag(0)
        .bool(timeout_ms.is_nan())
        .bool(timeout_ms < 0.0)
        .nat(whole)
        .bool(magnitude.fract() != 0.0);
    let reply = call(Entry::RetryIdle, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let armed = reply.bool()?;
    reply.end()?;
    Ok(armed)
}

/// What the stream-idle deadline's timer does when it fires (`R.Wake`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Wake {
    /// The stream stalled.
    Stall,
    /// Sleep this many us more from now.
    Sleep(u64),
}

/// The timer's decision (`R.idle.wake`): it fired `since_us` after the
/// stream last showed life, under a deadline of `deadline_us`; `held`:
/// a hold stops the clock. `since_us` saturates at [`NAT_MAX`], where the
/// stream has stalled under every deadline the wire carries.
///
/// # Errors
///
/// [`Error`] only from an inconsistent build (see [`crate::expect_core`]).
pub fn idle_wake(clock: IdleClock, since_us: u64, deadline_us: u64) -> Result<Wake, Error> {
    let mut request = Writer::new();
    request
        .tag(1)
        .bool(clock == IdleClock::Held)
        .nat(since_us.min(NAT_MAX))
        .nat(deadline_us);
    let reply = call(Entry::RetryIdle, &request.finish()?)?;
    let mut reply = Reader::reply(&reply)?;
    let wake = if reply.tag_of(2, "a Wake")? == 0 {
        Wake::Stall
    } else {
        Wake::Sleep(reply.nat()?)
    };
    reply.end()?;
    Ok(wake)
}

/// Whether a hold stops the stream's clock when its timer fires.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IdleClock {
    /// No hold: the clock runs from the stream's last life.
    Free,
    /// At least one hold is alive.
    Held,
}

#[cfg(test)]
mod tests {
    use super::{
        idle_after_stall, idle_armed, idle_wake, next_switch, retryable, wait, Cause, Facts,
        IdleClock, Policy, Switch, Tried, Wait, WaitInput, Wake,
    };

    #[test]
    fn the_idle_deadline_decisions_run_in_the_core() {
        assert_eq!(
            [0.5, 0.0, -1.0, f64::NAN].map(|ms| idle_armed(ms).unwrap()),
            [true, false, false, false]
        );
        assert_eq!(
            [
                idle_wake(IdleClock::Free, 250, 1000).unwrap(),
                idle_wake(IdleClock::Free, u64::MAX, 1000).unwrap(),
                idle_wake(IdleClock::Held, 4000, 1000).unwrap(),
            ],
            [Wake::Sleep(750), Wake::Stall, Wake::Sleep(1000)]
        );
    }

    #[test]
    fn the_codec_carries_each_decision_through_the_core() {
        let facts = Facts {
            parked: false,
            limit: false,
            status: None,
            kind: Some(Cause::Unknown),
            transient_text: true,
        };
        assert!(retryable(facts).unwrap());
        let input = WaitInput {
            base_ms: 100,
            attempt: 4,
            cap_ms: 600,
            draw: 12_345,
            server_ms: None,
        };
        assert_eq!(wait(input).unwrap(), Wait::After(345));
        let tried = [
            Tried {
                at: 0,
                server_wait_ms: None,
            },
            Tried {
                at: 1,
                server_wait_ms: None,
            },
            Tried {
                at: 2,
                server_wait_ms: None,
            },
        ];
        let policy = Policy {
            max_switches: 8,
            base_delay_ms: 10,
            max_delay_ms: 200,
        };
        assert_eq!(
            next_switch(3, &tried, policy).unwrap(),
            Some(Switch {
                to: 0,
                delay_ms: 10
            })
        );
        assert_eq!(idle_after_stall(300_000).unwrap(), 600_000);
    }

    /// Regression: `base * 2^returns` past 2^48-1 stopped the process.
    #[test]
    fn saturated_inputs_never_stop_the_process() {
        let tried: Vec<Tried> = (0..60)
            .map(|i| Tried {
                at: i % 2,
                server_wait_ms: Some(u64::MAX),
            })
            .collect();
        let policy = Policy {
            max_switches: u32::MAX,
            base_delay_ms: u64::MAX,
            max_delay_ms: u64::MAX,
        };
        assert!(next_switch(2, &tried, policy).unwrap().is_some());
        let input = WaitInput {
            base_ms: u64::MAX,
            attempt: u32::MAX,
            cap_ms: 0,
            draw: 7,
            server_ms: Some(u64::MAX),
        };
        assert!(matches!(wait(input).unwrap(), Wait::After(_)));
        assert_eq!(
            idle_after_stall(u64::MAX).unwrap(),
            crate::wire::NAT_MAX / 2 * 2
        );
    }
}
