//! The retry decisions (`bend/retry.bend`, entry `bend/ffi_retry.bend`;
//! `laws/retry.bend`): the classifier of a failed request, the
//! wait before a retry, the failover walk over a provider chain, and the
//! idle deadline after a stall; and the stream-idle deadline of one
//! watched stream ([`Idle`], the stepper `bend/ffi_retry_idle.bend`;
//! `laws/retry_idle.bend`). Each function encodes its input, calls
//! [`Entry::Retry`] or steps [`Entry::RetryIdle`] and decodes the reply;
//! every number is saturated at the wire's largest Nat ([`NAT_MAX`])
//! first, where the laws state the model's answer does not change (or
//! saturates with it).

use crate::wire::{Reader, WireError, Writer, NAT_MAX};
use crate::{call, expect_core, Entry, Error, Stepper};

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

/// What the stream-idle deadline's timer does when it fires (`R.Wake`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Wake {
    /// The stream stalled.
    Stall,
    /// Sleep this many us more from now.
    Sleep(u64),
}

/// The stream-idle deadline of one watched stream, kept in the compiled
/// core (`R.idle.step`): its deadline, the stream's latest life, the
/// holds of its clock alive, and whether it stalled. The caller sends each
/// event of the stream's life as it comes, with its time in us since the
/// deadline was armed (saturated at [`NAT_MAX`], where every deadline has
/// passed), and acts on the answer; only a fire answers. The laws hold for
/// every order of events (`idle_fire_exact`, `idle_stalls_once`).
#[derive(Debug)]
pub struct Idle {
    stepper: Stepper,
}

impl Idle {
    /// Arm the deadline of `deadline_us` us that `stream_idle_timeout_ms`
    /// selects (`R.idle.arm`: NaN, a negative number and 0 disable it:
    /// `None`), and the timer's first decision. The facts of the number go
    /// to the core: NaN, negative, its whole part (saturated at
    /// [`NAT_MAX`]), a fraction.
    #[must_use]
    pub fn arm(timeout_ms: f64, deadline_us: u64) -> Option<(Self, Wake)> {
        let magnitude = timeout_ms.abs();
        #[expect(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "a whole, non-negative f64 saturates into u64; the wire saturates it once more"
        )]
        let whole = (magnitude.trunc() as u64).min(NAT_MAX);
        let request = expect_core(
            Entry::RetryIdle,
            Writer::new()
                .bool(timeout_ms.is_nan())
                .bool(timeout_ms < 0.0)
                .nat(whole)
                .bool(magnitude.fract() != 0.0)
                .nat(deadline_us.min(NAT_MAX))
                .finish(),
        );
        let (stepper, reply) =
            expect_core(Entry::RetryIdle, Stepper::open(Entry::RetryIdle, &request));
        expect_core(Entry::RetryIdle, read_answer(&reply)).map(|first| (Idle { stepper }, first))
    }

    /// The stream showed life at `now_us`.
    pub fn life(&mut self, now_us: u64) {
        self.quiet(Writer::new().tag(0).nat(now_us.min(NAT_MAX)));
    }

    /// A hold of the stream's clock starts.
    pub fn hold(&mut self) {
        self.quiet(Writer::new().tag(1));
    }

    /// A hold of the stream's clock ends at `now_us`.
    pub fn free(&mut self, now_us: u64) {
        self.quiet(Writer::new().tag(2).nat(now_us.min(NAT_MAX)));
    }

    /// The deadline's timer fired at `now_us`: what it does now; `None`:
    /// nothing (the deadline had already stalled).
    pub fn fire(&mut self, now_us: u64) -> Option<Wake> {
        let reply = self.step(Writer::new().tag(3).nat(now_us.min(NAT_MAX)));
        expect_core(Entry::RetryIdle, read_answer(&reply))
    }

    /// Send an event that answers nothing to do (`idle_only_fires_answer`).
    fn quiet(&mut self, event: &mut Writer) {
        let reply = self.step(event);
        expect_core(Entry::RetryIdle, read_nothing(&reply));
    }

    fn step(&mut self, event: &mut Writer) -> String {
        let event = expect_core(Entry::RetryIdle, event.finish());
        expect_core(Entry::RetryIdle, self.stepper.step(&event))
    }
}

/// A reply: nothing to do, or the timer's decision.
fn read_answer(reply: &str) -> Result<Option<Wake>, WireError> {
    let mut r = Reader::reply(reply)?;
    let wake = if r.maybe()? {
        Some(if r.tag_of(2, "a Wake")? == 0 {
            Wake::Stall
        } else {
            Wake::Sleep(r.nat()?)
        })
    } else {
        None
    };
    r.end()?;
    Ok(wake)
}

/// The reply to an event that is not a fire: nothing to do.
fn read_nothing(reply: &str) -> Result<(), WireError> {
    let mut r = Reader::reply(reply)?;
    if r.maybe()? {
        return Err(WireError::Malformed {
            at: 0,
            expected: "nothing to do",
        });
    }
    r.end()
}

#[cfg(test)]
mod tests {
    use super::{
        idle_after_stall, next_switch, retryable, wait, Cause, Facts, Idle, Policy, Switch, Tried,
        Wait, WaitInput, Wake,
    };

    /// The compiled core is reached: which timeouts arm, and a fire after
    /// a life, during a hold and past the deadline (the rule itself is
    /// pinned by `laws/retry_idle.bend`).
    #[test]
    fn the_idle_deadline_runs_in_the_core() {
        assert_eq!(
            [0.0, -1.0, f64::NAN].map(|ms| Idle::arm(ms, 1000).is_some()),
            [false, false, false]
        );
        let (mut idle, first) = Idle::arm(0.5, 1000).unwrap();
        idle.life(250);
        let after_life = idle.fire(1000);
        idle.hold();
        let held = idle.fire(5000);
        idle.free(5000);
        let fires = [after_life, held, idle.fire(6000), idle.fire(7000)];
        assert_eq!(
            (first, fires),
            (
                Wake::Sleep(1000),
                [
                    Some(Wake::Sleep(250)),
                    Some(Wake::Sleep(1000)),
                    Some(Wake::Stall),
                    None
                ]
            )
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
