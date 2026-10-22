//! The run's decisions (docs/harness.md H4), one per phase transition:
//! what preparation does before its request ([`before_request`]), whether
//! it goes on after the compaction it waited for ([`after_compaction`]),
//! what a recovery does with a stuck reply ([`recover`], H4.8), what
//! follows a model reply ([`after_reply`]) and which note a retry's
//! request carries ([`retry_note`]), and how a finished tool round ends the
//! run or hands it to a new generation ([`round_end`]). Each is one pure
//! call over plain data (the counters that bound a run); the phases in
//! `generation.rs` and `round.rs` do the IO around it and act on what it
//! returns.
//! The Bend model `bend/run.bend` makes the same decisions; `LAWS.bend`
//! (H4) proves that every run ends under them, that a retry never
//! resends a request it cut and that every recovery stops at its cap, and
//! the bridge test (`bridge.rs`) runs both on the same scenarios.

use std::num::NonZeroU32;

use eukhe_bend::wire::Writer;
use serde::{Deserialize, Serialize};

use super::entry::{self, Ask};
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
    /// would make `rounds` rounds in a row with the same calls (they count
    /// themselves, so at least 1).
    Calls { rounds: NonZeroU32 },
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

/// What a recovery does with a stuck reply (H4.8), given the recovery and
/// the row of notes in a row that the request's note counts (`note`,
/// [`NoteCause::recovery`]): a length stop is redone under its cap, then
/// quits; leaked calls are redone under their cap, then stand as text;
/// calls run below the repeat cap, else are redone under the redirect
/// cap, then quit. A recovery does not read the retry policy: its note is
/// a new request, not a transient error. The decision is `decide.recover`
/// of `bend/run.bend` (law `rec_recover_is_the_rust_rule`).
pub(crate) fn recover(stuck: Stuck, note: Option<(Recovery, u32)>, caps: &Caps) -> Act {
    entry::ask(
        Ask::Recover,
        |w| {
            w.nat(u64::from(caps.length))
                .nat(u64::from(caps.leak))
                .nat(u64::from(caps.redirect))
                .nat(u64::from(caps.repeat));
            match stuck {
                Stuck::Length => w.tag(0),
                Stuck::Leak => w.tag(1),
                Stuck::Calls { rounds } => w.tag(2).nat(u64::from(rounds.get() - 1)),
            };
            match note {
                None => w.tag(0).nat(0),
                Some((Recovery::Length, row)) => w.tag(1).nat(u64::from(row)),
                Some((Recovery::Leak, row)) => w.tag(2).nat(u64::from(row)),
                Some((Recovery::Redirect, row)) => w.tag(3).nat(u64::from(row)),
            };
        },
        |r| match r.tag_of(4, "a recovery's act")? {
            0 => Ok(Act::Run),
            1 => {
                let row = r.nat()?;
                let row = u32::try_from(row).map_err(|_| entry::mismatch("a u32 row"))?;
                Ok(Act::Redo { row })
            }
            2 => Ok(Act::Stand),
            3 => Ok(Act::Quit),
            4..=u32::MAX => Err(entry::mismatch("a recovery's act")),
        },
    )
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
    /// model error, so it never ends the run as answered. The decision is
    /// `Ended.reply` of `bend/run.bend` (laws `run_no_answer_is_an_error`,
    /// `run_calls_never_answer`).
    pub(crate) fn reply<D>(self) -> Reply<D> {
        entry::ask(
            Ask::Ended,
            |w| {
                w.bool(self.text).bool(self.calls);
            },
            |r| match r.tag_of(5, "a reply")? {
                0 => Ok(Reply::Text),
                1 => Ok(Reply::Calls),
                3 => {
                    let retryable = r.bool()?;
                    let noted = r.bool()?;
                    Ok(Reply::Error { retryable, noted })
                }
                4 => Ok(Reply::Overflow { cut: r.bool()? }),
                2 | 5..=u32::MAX => Err(entry::mismatch("the reply of a message")),
            },
        )
    }
}

/// The limits as the run's entry reads them (`Lim`).
fn write_limits(w: &mut Writer, limits: &Limits) {
    w.nat(u64::from(limits.max_rounds.get()))
        .nat(entry::saturated(limits.max_wait))
        .nat(u64::from(limits.max_retries))
        .nat(u64::from(limits.max_notes));
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
/// the other's budget. The decision is `decide.reply` of `bend/run.bend`
/// (law `run_reply_is_the_rust_rule`); a poll goes on with the deferred
/// reply's handle.
pub(crate) fn after_reply<D>(at: Counts, reply: Reply<D>, limits: &Limits) -> Step<D> {
    let (shape, handle) = match reply {
        Reply::Deferred(handle) => (Reply::Deferred(()), Some(handle)),
        Reply::Text => (Reply::Text, None),
        Reply::Calls => (Reply::Calls, None),
        Reply::Error { retryable, noted } => (Reply::Error { retryable, noted }, None),
        Reply::Overflow { cut } => (Reply::Overflow { cut }, None),
    };
    entry::ask(
        Ask::Reply,
        |w| {
            write_limits(w, limits);
            w.nat(entry::saturated(at.attempt))
                .nat(u64::from(at.notes))
                .nat(entry::saturated(at.waited))
                .bool(at.compacted);
            match shape {
                Reply::Text => w.tag(0),
                Reply::Calls => w.tag(1),
                Reply::Deferred(()) => w.tag(2),
                Reply::Error { retryable, noted } => w.tag(3).bool(retryable).bool(noted),
                Reply::Overflow { cut } => w.tag(4).bool(cut),
            };
        },
        |r| match r.tag_of(8, "a step")? {
            0 => Ok(Step::Answer),
            1 => Ok(Step::Tools),
            2 => handle
                .map(Step::Poll)
                .ok_or_else(|| entry::mismatch("a poll only of a deferred reply")),
            3 => Ok(Step::Retry),
            4 => Ok(Step::Note),
            5 => Ok(Step::Compact),
            6 => Ok(Step::Fail(Failure::Model)),
            7 => Ok(Step::Fail(Failure::Polls)),
            8..=u32::MAX => Err(entry::mismatch("a step")),
        },
    )
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

/// What preparation does before the request counted by `at`, its context
/// over `threshold` (which compaction the context is over, given a cut
/// exists). A generation compacts at most once, so one that compacted
/// reads no threshold (law `run_prepare_compacted_reads_no_threshold`): the
/// caller need not measure its context and passes `None`. The decision is
/// `decide.prepare` of `bend/run.bend` (law `run_prepare_is_the_rust_rule`).
pub(crate) fn before_request(at: Counts, threshold: Option<Threshold>) -> Prepared {
    entry::ask(
        Ask::Prepare,
        |w| {
            w.bool(at.compacted).tag(match threshold {
                None => 0,
                Some(Threshold::Background) => 1,
                Some(Threshold::Blocking) => 2,
            });
        },
        |r| match r.tag_of(2, "a preparation")? {
            0 => Ok(Prepared::Compact),
            1 => Ok(Prepared::Request {
                background: r.bool()?,
            }),
            2..=u32::MAX => Err(entry::mismatch("a preparation")),
        },
    )
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
/// would at best leave no room for the answer. The decision is
/// `decide.compact` of `bend/run.bend` (law `run_compact_is_the_rust_rule`).
pub(crate) fn after_compaction(
    compaction: Compaction,
    compacted: Compacted,
) -> Result<(), Failure> {
    let goes = entry::ask(
        Ask::Compact,
        |w| {
            w.bool(compaction == Compaction::Overflow)
                .tag(match compacted {
                    Compacted::Entry => 0,
                    Compacted::Nothing => 1,
                    Compacted::Failed => 2,
                });
        },
        entry::bool,
    );
    if goes {
        Ok(())
    } else {
        Err(Failure::Model)
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

/// How a finished round ends ([`round_end`]).
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

impl Rounds {
    #[expect(
        clippy::trivially_copy_pass_by_ref,
        reason = "serde `skip_serializing_if` passes a reference"
    )]
    pub(crate) fn is_first(&self) -> bool {
        *self == Self::default()
    }
}

/// What may end a finished round before the cap: a control (terminate,
/// handoff) ends the run, and a queued reset applied at the round's
/// post-tools boundary ends a round that would hand the run on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Ending {
    pub(crate) control: bool,
    pub(crate) reset: bool,
}

/// How the round after `rounds` ends: [`RoundEnd::Stop`] when a control
/// ends the run (the round does not count), else the cap ends the run at
/// [`Limits::max_rounds`] rounds, else a queued reset ends it, else the
/// next generation goes on with one more round. A control wins over a
/// reset, and the cap over a reset. The decision is `decide.round` of
/// `bend/run.bend` (law `run_round_is_the_rust_rule`).
pub(crate) fn round_end(rounds: Rounds, ending: Ending, limits: &Limits) -> RoundEnd {
    entry::ask(
        Ask::Round,
        |w| {
            write_limits(w, limits);
            w.nat(u64::from(rounds.count))
                .bool(ending.control)
                .bool(ending.reset);
        },
        |r| match r.tag_of(4, "a round's end")? {
            0 => Ok(RoundEnd::Stop),
            1 => Ok(RoundEnd::Reset),
            2 => Ok(RoundEnd::Capped),
            3 => {
                let count = u32::try_from(r.nat()?).map_err(|_| entry::mismatch("a u32 count"))?;
                Ok(RoundEnd::Next(Rounds { count }))
            }
            4..=u32::MAX => Err(entry::mismatch("a round's end")),
        },
    )
}
