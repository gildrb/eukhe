//! The provider request as an exactly-once effect (spec O2, O4, O7).
//!
//! A request is intended when its `Request` checkpoint commits, started
//! each time the `request` phase commits one more send before it goes out,
//! and finished when its reply commits (the assistant entry, its usage and
//! the next checkpoint in one commit, so a reply that arrived is never
//! asked for again). A restart that finds it sent and unanswered cannot
//! tell what the provider did: the compiled core (`bend/once.bend`,
//! `eukhe_bend::rules::once`) says whether it goes out again. A request is
//! a keyed effect: every send carries the same idempotency key ([`key`],
//! the `Idempotency-Key` header, committed in the `Request` checkpoint
//! with the first send and read back by every resend), so a provider that
//! honors the key answers a repeat without running it twice, and it goes
//! out again at most `request_resends` times (the setting
//! `retry.maxResends`, default 2; `once_keyed_sends_capped`): a crash loop
//! cannot send, and bill, one request without bound. Past the cap, and
//! when its run was stopped, the request ends unknown: the run ends with
//! an error that says so and the request is noted in the conversation's
//! `eukhe.effects` ledger.

use eukhe_bend::rules::once::{self, Mode, Policy, Record, Seen, Verdict};
use eukhe_chord::context::Context;
use eukhe_chord::json::to_json;

use super::{end_failed_run, failed, queue_modes, Runtime};
use crate::harness::effects::{note_unknown, EffectKind, UnknownEffect};
use crate::harness::inbox::prepare_boundary;
use crate::harness::live::LIVE_DOC;
use crate::session::{SessionError, SessionResult};
use crate::types::{SubmissionSettlement, TaskId};

/// The header every send of a request carries its idempotency key in.
pub(super) const IDEMPOTENCY_KEY_HEADER: &str = "Idempotency-Key";

/// What the `request` phase does with its request.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Send {
    /// Record one more send, then send it.
    Go,
    /// It ends unknown: nothing is sent.
    Interrupted,
    /// It never went out and its run was stopped: nothing to report.
    Unsent,
}

/// What a run of `mode` does with a request that went out `sends` times
/// before, which may go out again `resends` times after the first: the
/// compiled core's verdict for its journal (intended, then one start per
/// send).
///
/// # Errors
///
/// A verdict the core never gives a request that is not ended (an
/// inconsistent build).
pub(super) fn decide(sends: u32, resends: u32, mode: Mode) -> SessionResult<Send> {
    let journal = std::iter::once(Record::Intended).chain((0..sends).map(|_| Record::Started));
    let (_, verdict) = once::restart(journal, mode, Policy::Keyed { cap: resends }, Seen::Dark);
    match verdict {
        Verdict::Launch => Ok(Send::Go),
        Verdict::Interrupt => Ok(Send::Interrupted),
        Verdict::Abandon => Ok(Send::Unsent),
        Verdict::Skip | Verdict::Adopt | Verdict::Settled => Err(SessionError::error(
            "A provider request is sent, interrupted or unsent at a restart",
        )),
    }
}

/// The idempotency key of the request of attempt `attempt` of the
/// generation `task`, in the provider session `provider_session`: the
/// same for every send of that request, another for every other request.
pub(super) fn key(provider_session: &str, task: TaskId, attempt: u64) -> String {
    once::key(provider_session, &format!("request:{task}:{attempt}"))
}

/// The ledger's record of the request of attempt `attempt` of the
/// runtime's generation, sent `sends` times and never answered.
fn unknown(runtime: &Runtime, attempt: u64, sends: u32) -> SessionResult<UnknownEffect> {
    Ok(UnknownEffect {
        id: format!("request:{}:{attempt}", runtime.task_id()),
        kind: EffectKind::Request,
        what: format!("model request (attempt {attempt}, sent {sends} times)"),
        at: runtime.now()?,
        resolution: None,
    })
}

/// The request a stopped run leaves unknown: the ledger's record of the
/// request of attempt `attempt` when it went out (`sends` times) and no
/// reply came, else nothing.
///
/// # Errors
///
/// The clock, or an inconsistent build ([`decide`]).
pub(super) fn cut_by_stop(
    runtime: &Runtime,
    attempt: u64,
    sends: u32,
) -> SessionResult<Option<UnknownEffect>> {
    match decide(sends, runtime.settings().request_resends, Mode::Stop)? {
        Send::Interrupted => unknown(runtime, attempt, sends).map(Some),
        Send::Go | Send::Unsent => Ok(None),
    }
}

/// End the run: its request of attempt `attempt` went out `sends` times,
/// a restart cut each, and it is not sent again. The run's inputs settle
/// `unanswered` with `request_interrupted`, and the request is noted
/// unknown in the same commit.
pub(super) async fn fail_interrupted(
    runtime: &Runtime,
    attempt: u64,
    sends: u32,
    cx: &Context,
) -> SessionResult<()> {
    let text = format!(
        "The model request was interrupted by a restart {sends} times and was not sent again: \
         its reply is unknown. Send your message again to continue."
    );
    let effect = unknown(runtime, attempt, sends)?;
    let conversation_id = runtime.conversation_id();
    let commit_runtime = runtime.clone();
    runtime
        .commit(
            move |tx, _current| async move {
                let runtime = commit_runtime;
                let boundary =
                    prepare_boundary(&tx, conversation_id, queue_modes(&runtime)).await?;
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                note_unknown(&tx, conversation_id, &effect).await?;
                end_failed_run(
                    &tx,
                    &runtime,
                    &live,
                    boundary,
                    &SubmissionSettlement::Unanswered {
                        reason: "request_interrupted".to_owned(),
                        detail: Some(to_json(&text)?),
                    },
                )
                .await?;
                failed(text, "request_interrupted").map(Some)
            },
            cx,
        )
        .await
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A request goes out once, then again after each restart that found it
    /// sent and unanswered, `resends` times; the next restart ends it
    /// unknown (spec O7).
    #[test]
    fn a_request_goes_out_again_at_most_its_resends() {
        let sent = |sends, resends| decide(sends, resends, Mode::Resume).unwrap();
        assert_eq!(
            [sent(0, 2), sent(1, 2), sent(2, 2), sent(3, 2), sent(4, 2)],
            [
                Send::Go,
                Send::Go,
                Send::Go,
                Send::Interrupted,
                Send::Interrupted
            ]
        );
        assert_eq!(
            [sent(0, 0), sent(1, 0), sent(1, 5), sent(6, 5)],
            [Send::Go, Send::Interrupted, Send::Go, Send::Interrupted]
        );
    }

    /// A stopped run sends nothing: an unsent request is reported unsent, a
    /// sent one unknown, whatever the resends left (spec O4, O5).
    #[test]
    fn a_stopped_run_sends_nothing() {
        let stopped = |sends, resends| decide(sends, resends, Mode::Stop).unwrap();
        assert_eq!(
            [stopped(0, 2), stopped(1, 2), stopped(3, 2), stopped(1, 0)],
            [
                Send::Unsent,
                Send::Interrupted,
                Send::Interrupted,
                Send::Interrupted
            ]
        );
    }

    /// Every send of one request carries one key; another request (another
    /// attempt, generation or provider session) another key.
    #[test]
    fn one_key_per_request() {
        let task = TaskId::from_number(7);
        let first = key("session-a", task, 1);
        assert_eq!(first, key("session-a", task, 1));
        let others = [
            key("session-a", task, 2),
            key("session-a", TaskId::from_number(8), 1),
            key("session-b", task, 1),
        ];
        assert!(others.iter().all(|other| *other != first), "{others:?}");
    }
}
