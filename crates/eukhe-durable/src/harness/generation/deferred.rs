//! The deferred job of a request and the stall of a stream (LAWS.bend
//! H4.4, H4.5): what a failed poll of the job does ([`PollFailure::next`])
//! and the idle deadline of the retry after a stall ([`idle_after_stall`]).
//! The time check of a job (its deadline) is [`after_reply`]'s.
//!
//! The Bend model is `bend/retry.bend` (§4 the deferred job, §5 the
//! stall). `laws/retry.bend` states its laws (`deferred_pays_once`,
//! `deferred_bounded_in_time`, `deferred_failed_poll_repolls`,
//! `stall_retry_extends`) and `PROOF.bend` proves them. A failed poll runs
//! as `decide.poll` of `bend/run/decision.bend` in the compiled core; with the time
//! check of [`after_reply`] it is the job of §4 (laws
//! `run_failed_poll_is_the_job_model`, `run_deferred_reply_is_the_job_model`,
//! `run_first_deferred_reply_is_the_job_model`). The stall runs as
//! `stall.next` of `bend/retry.bend` in the compiled core
//! (`bend/ffi_retry.bend`).
//!
//! [`after_reply`]: super::decide::after_reply

use super::entry::{self, Ask};

/// What a failed poll of a deferred job does.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FailedPoll {
    /// Poll the same job again. The job can still run, so a new request
    /// would pay for the work two times.
    Repoll,
    /// Cancel the job, then fail the run. No new request goes out while
    /// the job can run.
    Cancel,
}

/// A failed fetch of a deferred job (the poll's message is an error).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PollFailure {
    /// The retry policy can cure the failure (`retry.enabled` and
    /// `is_retryable_assistant_error`).
    pub(crate) retryable: bool,
    /// The fetches of the job that failed in a row before this one. A
    /// reply that is still deferred sets it to 0.
    pub(crate) failures: u32,
}

impl PollFailure {
    /// What the failed poll does: a retryable failure below
    /// `retry.maxRetries` (`max_retries`) failures in a row polls the
    /// same job again; any other failure cancels the job. The job's
    /// deadline still applies to the next poll: the run sends it through
    /// `after_reply` as a deferred reply. The decision is `decide.poll` of
    /// `bend/run/decision.bend`; with `after_reply` it is the job of
    /// `bend/retry.bend` §4 (law `run_failed_poll_is_the_job_model`).
    pub(crate) fn next(self, max_retries: u32) -> FailedPoll {
        let repoll = entry::ask(
            Ask::Poll,
            |w| {
                w.bool(self.retryable)
                    .nat(u64::from(self.failures))
                    .nat(u64::from(max_retries));
            },
            entry::bool,
        );
        if repoll {
            FailedPoll::Repoll
        } else {
            FailedPoll::Cancel
        }
    }
}

/// The idle deadline (ms) of the retry after a stream stalled under
/// `idle_ms` (M3): two times that deadline, decided by the compiled Bend
/// core (`bend/retry.bend` `stall.next`, law `stall_retry_doubles`; the
/// deadline saturates at half the wire's largest Nat). The same deadline
/// would stall the same request again.
pub(crate) fn idle_after_stall(idle_ms: u64) -> u64 {
    eukhe_bend::expect_core(
        eukhe_bend::Entry::Retry,
        eukhe_bend::rules::retry::idle_after_stall(idle_ms),
    )
}
