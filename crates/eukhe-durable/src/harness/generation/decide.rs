//! The run's decisions (docs/harness.md H4), one per phase transition:
//! what preparation does before its request ([`before_request`]), whether
//! it goes on after the compaction it waited for ([`after_compaction`]),
//! what follows a model reply ([`after_reply`]), and how a finished tool
//! round ends the run or hands it to a new generation ([`Rounds::finish`],
//! [`RoundEnd`]). Pure functions of the counters that bound a run; the
//! phases in `generation.rs` and `round.rs` call them and act on what they
//! return. The Bend model `bend/run.bend` makes the same decisions;
//! `LAWS.bend` (H4) proves that every run ends under them, and the bridge
//! test (`bridge.rs`) runs both on the same scenarios.

use std::num::NonZeroU32;

use serde::{Deserialize, Serialize};

use crate::harness::types::CompactionPolicy;

/// Deferred fetches of one request before the run fails (H4.4): a day of
/// polls at the default 5 s interval.
pub(crate) const MAX_POLLS: u32 = 17_280;

/// Rounds in a row with the same calls and the same results that end the
/// run as a loop (H4.3).
pub(crate) const LOOP_ROUNDS: u32 = 6;

/// The limits the decisions read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Limits {
    /// `maxToolRounds`.
    pub(crate) max_rounds: NonZeroU32,
    /// [`MAX_POLLS`].
    pub(crate) max_polls: u32,
    /// `retry.maxRetries`.
    pub(crate) max_retries: u32,
    /// [`LOOP_ROUNDS`].
    pub(crate) loop_rounds: u32,
}

/// The counters of one request of a generation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Counts {
    /// 1 for the generation's first request; a retry adds 1.
    pub(crate) attempt: u64,
    /// The deferred fetch that gave the reply: 0 for the request itself.
    pub(crate) polls: u32,
    /// The generation compacted; it compacts at most once.
    pub(crate) compacted: bool,
}

/// How a model call ended; `D` is what a deferred reply is polled with.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Reply<D> {
    /// A final answer: stop, length, or tool use without calls.
    Text,
    /// Tool calls.
    Calls,
    /// Deferred, with its handle.
    Deferred(D),
    /// Any other end; retryable under the retry policy.
    Error { retryable: bool },
    /// A context overflow; `cut`: compaction is on and finds a cut.
    Overflow { cut: bool },
}

/// What follows a reply.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Step<D> {
    Answer,
    Tools,
    /// Poll with the handle; the number is this fetch's, counted from 1.
    Poll(D, u32),
    Retry,
    Compact,
    Fail(Failure),
}

/// Why a reply ends the run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Failure {
    /// The model failed: an error not retried, or an overflow that cannot
    /// compact.
    Model,
    /// The reply was still deferred after [`Limits::max_polls`] fetches.
    Polls,
}

/// The step after a reply to the request or poll counted by `at`.
pub(crate) fn after_reply<D>(at: Counts, reply: Reply<D>, limits: &Limits) -> Step<D> {
    match reply {
        Reply::Text => Step::Answer,
        Reply::Calls => Step::Tools,
        Reply::Deferred(handle) if at.polls < limits.max_polls => Step::Poll(handle, at.polls + 1),
        Reply::Deferred(_) => Step::Fail(Failure::Polls),
        Reply::Error { retryable: true } if at.attempt <= u64::from(limits.max_retries) => {
            Step::Retry
        }
        Reply::Overflow { cut: true } if !at.compacted => Step::Compact,
        Reply::Error { .. } | Reply::Overflow { .. } => Step::Fail(Failure::Model),
    }
}

/// Which threshold compaction preparation may start before its request
/// (spec §8.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Threshold {
    /// Above `contextWindow - reserveTokens`: the request waits for it.
    Blocking,
    /// Above the background threshold: it runs beside the request.
    Background,
}

/// Which threshold compaction a context of `tokens` is over (spec §8.3):
/// [`Threshold::Blocking`] when `tokens > contextWindow - reserveTokens`,
/// [`Threshold::Background`] when `tokens > blocking - margin` with a
/// positive margin ([`BackgroundMargin`]). None when the policy is disabled
/// or the window is unknown (`0`). Whether a cut exists is the caller's.
#[expect(
    clippy::cast_precision_loss,
    reason = "TS compares token counts as doubles; blocking may be negative"
)]
pub(crate) fn threshold_for(
    tokens: f64,
    context_window: u64,
    policy: &CompactionPolicy,
) -> Option<Threshold> {
    if !policy.enabled || context_window == 0 {
        return None;
    }
    let window = context_window as f64;
    let blocking = window - policy.reserve_tokens;
    let margin = policy.background.tokens(window);
    if tokens > blocking {
        Some(Threshold::Blocking)
    } else if margin > 0.0 && tokens > blocking - margin {
        Some(Threshold::Background)
    } else {
        None
    }
}

/// What preparation does with its request.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Prepared {
    /// Wait for a blocking threshold compaction, then prepare again.
    Compact,
    /// Send the request; `background`: start a background compaction too.
    Request { background: bool },
}

/// What preparation does before the request counted by `at`: a generation
/// compacts at most once, so only one that has not reads `threshold`
/// (which compaction the context is over, given a cut exists).
pub(crate) fn before_request(
    at: Counts,
    threshold: impl FnOnce() -> Option<Threshold>,
) -> Prepared {
    match (!at.compacted).then(threshold).flatten() {
        Some(Threshold::Blocking) => Prepared::Compact,
        over => Prepared::Request {
            background: over == Some(Threshold::Background),
        },
    }
}

/// The compaction a generation waited for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Compaction {
    /// Started by a context overflow ([`Step::Compact`]).
    Overflow,
    /// A blocking threshold one ([`Prepared::Compact`]).
    Threshold,
}

/// How that compaction ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Compacted {
    /// It appended a compaction entry.
    Entry,
    /// It completed without one: nothing to compact, or declined.
    Nothing,
    /// It failed, faulted, was aborted or orphaned.
    Failed,
}

/// Whether preparation goes on after the compaction it waited for. An
/// overflow's needs its entry: without one the request overflows again. A
/// threshold one that found nothing leaves a request that may still fit;
/// one that failed left a context it judged too large, and sending it
/// would at best leave no room for the answer.
pub(crate) fn after_compaction(
    compaction: Compaction,
    compacted: Compacted,
) -> Result<(), Failure> {
    match (compaction, compacted) {
        (_, Compacted::Entry) | (Compaction::Threshold, Compacted::Nothing) => Ok(()),
        (Compaction::Overflow, Compacted::Nothing) | (_, Compacted::Failed) => Err(Failure::Model),
    }
}

/// The tool rounds a run has finished, and how many of the last ones in a
/// row made the same calls with the same results. Each generation's input
/// carries it, so a restart keeps it.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Rounds {
    /// Tool rounds finished.
    pub(crate) count: u32,
    /// Rounds in a row that ended with `hash`; 0 before the first round.
    pub(crate) same: u32,
    /// The last round's hash of its calls and results.
    pub(crate) hash: u64,
}

/// Why a finished round ends the run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Limit {
    /// The run made [`Limits::max_rounds`] rounds.
    Rounds,
    /// The last [`Limits::loop_rounds`] rounds were the same.
    Loop,
}

/// How a finished round ends: [`RoundEnd::Stop`] when a control ends the
/// run (the round does not count), else [`Rounds::finish`]'s verdict, which
/// a queued reset at the post-tools boundary may still end
/// ([`RoundEnd::reset`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RoundEnd {
    /// A control ended the run (terminate, handoff): it is answered.
    Stop,
    /// A queued reset at the round's boundary cut the run's context.
    Reset,
    /// The round reached a limit.
    Fail(Limit),
    /// The next generation goes on with these rounds.
    Next(Rounds),
}

impl RoundEnd {
    /// The end after a queued reset applied at the post-tools boundary: it
    /// ends a round that would hand the run on; the cap and the loop guard
    /// came first, and a run that ends anyway stays as it ends.
    pub(crate) fn reset(self) -> Self {
        match self {
            Self::Next(_) => Self::Reset,
            end @ (Self::Stop | Self::Reset | Self::Fail(_)) => end,
        }
    }
}

impl Rounds {
    pub(crate) fn is_first(&self) -> bool {
        *self == Self::default()
    }

    /// The rounds after one more that ended with `hash`, or why the run
    /// ends there.
    pub(crate) fn finish(self, hash: u64, limits: &Limits) -> RoundEnd {
        let same = if self.same > 0 && self.hash == hash {
            self.same.saturating_add(1)
        } else {
            1
        };
        let count = self.count.saturating_add(1);
        if same >= limits.loop_rounds {
            return RoundEnd::Fail(Limit::Loop);
        }
        if count >= limits.max_rounds.get() {
            return RoundEnd::Fail(Limit::Rounds);
        }
        RoundEnd::Next(Self { count, same, hash })
    }
}
