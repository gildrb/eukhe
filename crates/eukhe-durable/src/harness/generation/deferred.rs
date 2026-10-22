//! The deferred job of a request and the stall of a stream (docs/harness.md
//! H4.4, H4.5): what a failed poll of the job does ([`PollFailure::next`])
//! and the idle deadline of the retry after a stall ([`idle_after_stall`]).
//! The time check of a job (its deadline) is [`after_reply`]'s.
//!
//! The Bend model is `bend/retry.bend` (§4 the deferred job, §5 the
//! stall). `LAWS.bend` section `retry` states its laws (`deferred_pays_once`,
//! `deferred_bounded_in_time`, `deferred_failed_poll_repolls`,
//! `stall_retry_extends`) and `PROOF.bend` proves them. The bridge test
//! (`retry_bridge.rs`) runs these decisions and the model on the same
//! scenarios.
//!
//! [`after_reply`]: super::decide::after_reply

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
    /// `after_reply` as a deferred reply.
    pub(crate) fn next(self, max_retries: u32) -> FailedPoll {
        if self.retryable && self.failures < max_retries {
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
