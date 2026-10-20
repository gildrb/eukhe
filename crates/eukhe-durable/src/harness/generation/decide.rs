//! The run's decisions (docs/harness.md H4), one per phase transition:
//! what preparation does before its request ([`before_request`]), whether
//! it goes on after the compaction it waited for ([`after_compaction`]),
//! what a recovery does with a stuck reply ([`recover`], H4.8), what
//! follows a model reply ([`after_reply`]) and which note a retry's
//! request carries ([`retry_note`]), and how a finished tool round ends the
//! run or hands it to a new generation ([`Rounds::finish`], [`RoundEnd`]).
//! Pure functions of the counters that bound a run; the phases in
//! `generation.rs` and `round.rs` call them and act on what they return.
//! The Bend model `bend/run.bend` makes the same decisions; `LAWS.bend`
//! (H4) proves that every run ends under them, that a retry never
//! resends a request it cut and that every recovery stops at its cap, and
//! the bridge test (`bridge.rs`) runs both on the same scenarios.

use std::num::NonZeroU32;

use serde::{Deserialize, Serialize};

use super::note::{NoteCause, Recovery, RetryNote};
use crate::harness::types::CompactionPolicy;

/// Noted retries of one generation before a noted reply fails the run
/// (H4.7, H4.8): their own budget, apart from `retry.maxRetries`. It
/// bounds every row of notes together: each recovery caps its own row,
/// and rows of different causes can alternate.
pub(crate) const MAX_NOTES: u32 = 8;

/// Length notes in a row before a length stop with no answer fails the
/// run (H4.8; omp `INCOMPLETE_RECOVERY_MAX_RETRIES`).
pub(crate) const LENGTH_NOTES: u32 = 3;

/// Leak notes in a row before leaked tool calls that the harness could
/// not rebuild answer as text (H4.8; omp `MAX_DSML_LEAK_NUDGES`).
pub(crate) const LEAK_NOTES: u32 = 2;

/// Redirect notes in a row before a repeated call fails the run (H4.8).
pub(crate) const REDIRECT_NOTES: u32 = 2;

/// Rounds in a row with the same calls (names and arguments) and the same
/// results that calls may make: calls that would make this many do not
/// run (H4.8; omp `toolCallLoopGuard.threshold`).
pub(crate) const REPEAT_CALLS: u32 = 5;

/// The caps of the recoveries (H4.8).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Caps {
    /// [`LENGTH_NOTES`].
    pub(crate) length: u32,
    /// [`LEAK_NOTES`].
    pub(crate) leak: u32,
    /// [`REDIRECT_NOTES`].
    pub(crate) redirect: u32,
    /// [`REPEAT_CALLS`].
    pub(crate) repeat: u32,
}

/// The production caps.
pub(crate) const CAPS: Caps = Caps {
    length: LENGTH_NOTES,
    leak: LEAK_NOTES,
    redirect: REDIRECT_NOTES,
    repeat: REPEAT_CALLS,
};

/// What a stuck reply holds, as a recovery reads it (H4.8).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Stuck {
    /// A length stop with no text and no tool call: the model still
    /// reasoned when it hit the output limit.
    Length,
    /// Tool-call markup in the text and no tool call, and the harness
    /// could not rebuild every leaked call.
    Leak,
    /// Tool calls (made as tool calls, or rebuilt from leaked markup) that
    /// would make `rounds` rounds in a row with the same calls.
    Calls { rounds: u32 },
}

/// What a recovery does with a stuck reply.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Act {
    /// The calls run.
    Run,
    /// A noted error, retried with a note: the `row`th note of the
    /// recovery in a row.
    Redo { row: u32 },
    /// The reply answers as text.
    Stand,
    /// The recovery reached its cap: the run fails on the model.
    Quit,
}

/// What a recovery does with a stuck reply (H4.8), given the note of the
/// request (`note`), whose recovery and row count the notes in a row: a
/// length stop is redone under its cap, then quits; leaked calls are
/// redone under their cap, then stand as text; calls run below the repeat
/// cap, else are redone under the redirect cap, then quit. A recovery
/// does not read the retry policy: its note is a new request, not a
/// transient error.
pub(crate) fn recover(stuck: Stuck, note: Option<&NoteCause>, caps: &Caps) -> Act {
    let row = |recovery| note.map_or(0, |note| note.row(recovery));
    match stuck {
        Stuck::Length => {
            let row = row(Recovery::Length);
            if row < caps.length {
                Act::Redo { row: row + 1 }
            } else {
                Act::Quit
            }
        }
        Stuck::Leak => {
            let row = row(Recovery::Leak);
            if row < caps.leak {
                Act::Redo { row: row + 1 }
            } else {
                Act::Stand
            }
        }
        Stuck::Calls { rounds } if rounds < caps.repeat => Act::Run,
        Stuck::Calls { .. } => {
            let row = row(Recovery::Redirect);
            if row < caps.redirect {
                Act::Redo { row: row + 1 }
            } else {
                Act::Quit
            }
        }
    }
}

/// The limits the decisions read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[expect(
    clippy::struct_field_names,
    reason = "each field is the maximum of one counter of `Counts` or `Rounds`"
)]
pub(crate) struct Limits {
    /// `maxToolRounds`.
    pub(crate) max_rounds: NonZeroU32,
    /// The ms the request's deferred job may run (H4.4): its provider's
    /// expiry, else the requested window, else the longest window.
    pub(crate) max_wait: u64,
    /// `retry.maxRetries`.
    pub(crate) max_retries: u32,
    /// [`MAX_NOTES`].
    pub(crate) max_notes: u32,
}

/// The counters of one request of a generation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Counts {
    /// 1 for the generation's first request; a retry adds 1.
    pub(crate) attempt: u64,
    /// The noted retries of the generation so far (each spends a note,
    /// not a retry).
    pub(crate) notes: u32,
    /// The ms since the request was sent, at this reply.
    pub(crate) waited: u64,
    /// The generation compacted; it compacts at most once.
    pub(crate) compacted: bool,
}

/// How a model call ended; `D` is what a deferred reply is polled with.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Reply<D> {
    /// A final answer: stop, length, or tool use with text and no tool
    /// call ([`Ended::reply`]).
    Text,
    /// Tool calls, whatever the stop reason.
    Calls,
    /// Deferred, with its handle.
    Deferred(D),
    /// Any other end, or an end with no text and no tool call (the model
    /// gave no answer, H4.7). `noted`: the reply was cut (the repetition
    /// guard cut its stream, it gave no answer, or a recovery redid it),
    /// so its retry carries a note ([`retry_note`]) and spends a note, not
    /// a retry; `retryable` (the retry policy) reads only an error that is
    /// not noted.
    Error { retryable: bool, noted: bool },
    /// A context overflow; `cut`: compaction is on and finds a cut.
    Overflow { cut: bool },
}

/// What a message that ends the model's turn (stop reason stop, length, or
/// tool use) holds, as [`Ended::reply`] reads it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Ended {
    /// The message has a text block whose text is not blank.
    pub(crate) text: bool,
    /// The message has a tool call.
    pub(crate) calls: bool,
}

impl Ended {
    /// The reply the message makes (H4.1, H4.7): its calls when it has
    /// calls, whatever the stop reason (vLLM, llama.cpp and Ollama send
    /// `stop` with tool calls); else an answer when it has text. With no
    /// text and no call, the model gave no answer: the reply is a noted
    /// model error, so it never ends the run as answered.
    pub(crate) fn reply<D>(self) -> Reply<D> {
        if self.calls {
            Reply::Calls
        } else if self.text {
            Reply::Text
        } else {
            Reply::Error {
                retryable: false,
                noted: true,
            }
        }
    }
}

/// What follows a reply.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Step<D> {
    Answer,
    Tools,
    /// Poll the same deferred job with the handle.
    Poll(D),
    /// A transient retry, after the retry policy's wait.
    Retry,
    /// A noted retry: a new request, sent at once.
    Note,
    Compact,
    Fail(Failure),
}

/// Why a reply ends the run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Failure {
    /// The model failed: an error not retried, a noted reply past
    /// [`Limits::max_notes`], or an overflow that cannot compact.
    Model,
    /// The reply was still deferred at the job's deadline
    /// ([`Limits::max_wait`]).
    Polls,
}

/// The step after a reply to the request or poll counted by `at`. A noted
/// reply spends a note and a transient error a retry: neither shrinks
/// the other's budget.
pub(crate) fn after_reply<D>(at: Counts, reply: Reply<D>, limits: &Limits) -> Step<D> {
    let retries = (at.attempt - 1).saturating_sub(u64::from(at.notes));
    match reply {
        Reply::Text => Step::Answer,
        Reply::Calls => Step::Tools,
        Reply::Deferred(handle) if at.waited < limits.max_wait => Step::Poll(handle),
        Reply::Deferred(_) => Step::Fail(Failure::Polls),
        Reply::Error { noted: true, .. } if at.notes < limits.max_notes => Step::Note,
        Reply::Error {
            retryable: true,
            noted: false,
        } if retries < u64::from(limits.max_retries) => Step::Retry,
        Reply::Overflow { cut: true } if !at.compacted => Step::Compact,
        Reply::Error { .. } | Reply::Overflow { .. } => Step::Fail(Failure::Model),
    }
}

/// The note the retry of the request counted by `at` ends with (H4.7): after
/// a noted reply (`cause`), a new note that names the retry's attempt and
/// the cause and counts one more noted retry, so the retry never sends the
/// request that was cut; after any other error, the note of that request
/// (`note`), so the retry sends it again.
pub(crate) fn retry_note(
    at: Counts,
    cause: Option<NoteCause>,
    note: Option<RetryNote>,
) -> Option<RetryNote> {
    match cause {
        Some(cause) => Some(RetryNote {
            attempt: at.attempt + 1,
            cause,
            spent: at.notes + 1,
        }),
        None => note,
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

/// The tool rounds a run has finished. Each generation's input carries
/// it, so a restart keeps it. (The loop guard of H4.3, which counted
/// rounds with the same calls and results here, is replaced by the
/// repeat recovery of H4.8, which stops such a row before it.)
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Rounds {
    /// Tool rounds finished.
    pub(crate) count: u32,
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
    /// The run made [`Limits::max_rounds`] rounds.
    Capped,
    /// The next generation goes on with these rounds.
    Next(Rounds),
}

impl RoundEnd {
    /// The end after a queued reset applied at the post-tools boundary: it
    /// ends a round that would hand the run on; the cap came first, and a
    /// run that ends anyway stays as it ends.
    pub(crate) fn reset(self) -> Self {
        match self {
            Self::Next(_) => Self::Reset,
            end @ (Self::Stop | Self::Reset | Self::Capped) => end,
        }
    }
}

impl Rounds {
    #[expect(
        clippy::trivially_copy_pass_by_ref,
        reason = "serde `skip_serializing_if` passes a reference"
    )]
    pub(crate) fn is_first(&self) -> bool {
        *self == Self::default()
    }

    /// The rounds after one more, or the cap that ends the run there.
    pub(crate) fn finish(self, limits: &Limits) -> RoundEnd {
        let count = self.count.saturating_add(1);
        if count >= limits.max_rounds.get() {
            return RoundEnd::Capped;
        }
        RoundEnd::Next(Self { count })
    }
}
