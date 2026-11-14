//! The provider request as an exactly-once effect (spec O2, O4, O7).
//!
//! A request is intended when its `Request` checkpoint commits, started
//! each time the `request` phase commits one more send before it goes out,
//! and finished when its reply commits (the assistant entry, its usage and
//! the next checkpoint in one commit, so a reply that arrived is never
//! asked for again). A restart that finds it sent and unanswered cannot
//! tell what the provider did: the compiled core (`bend/once.bend`,
//! `eukhe_bend::rules::once`) says whether it goes out again. Every send
//! carries the same idempotency key ([`key`], the `Idempotency-Key`
//! header, committed in the `Request` checkpoint with the first send and
//! read back by every resend). It goes out again only when its provider
//! declares that it drops every repeat of the key (`dedups_requests`,
//! models.json `"requestDedup": "lasting"`; no shipped provider does), at
//! most `request_resends` times (`retry.maxResends`, default 2; laws
//! `once_undeduped_sends_once`, `once_keyed_sends_capped`). Otherwise the
//! request ends unknown: it is noted in the conversation's
//! `eukhe.effects` ledger, its reservation stays charged, and the run goes
//! on with a new request (the next attempt: a new effect with its own key
//! and reservation, sr141), at most `retry.maxRetries` times in a row;
//! past that, and when its run was stopped, the run ends with an error
//! that says so.

use eukhe_bend::rules::once::{self, Dedup, Mode, Policy, Record, Seen, Verdict};
use eukhe_chord::context::Context;
use eukhe_chord::json::to_json;
use eukhe_types::budget::dollars;

use super::{
    end_failed_run, failed, live_generation, queue_modes, GenerationCheckpoint, Next, Runtime,
};
use crate::harness::effects::{note_unknown, EffectKind, UnknownEffect};
use crate::harness::inbox::prepare_boundary;
use crate::harness::live::run::convert_partial;
use crate::harness::live::LIVE_DOC;
use crate::session::{SessionError, SessionResult};
use crate::types::{SubmissionSettlement, TaskId};

/// The header every send of a request carries its idempotency key in.
pub const IDEMPOTENCY_KEY_HEADER: &str = "Idempotency-Key";

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
/// before, to a provider that drops every repeat of its key or not
/// (`dedups`), which may then go out again `resends` times after the
/// first: the compiled core's verdict for its journal (intended, then one
/// start per send).
///
/// # Errors
///
/// A verdict the core never gives a request that is not ended (an
/// inconsistent build).
pub(super) fn decide(sends: u32, dedups: bool, resends: u32, mode: Mode) -> SessionResult<Send> {
    let journal = std::iter::once(Record::Intended).chain((0..sends).map(|_| Record::Started));
    let dedup = if dedups {
        Dedup::Lasting
    } else {
        Dedup::Undeclared
    };
    let policy = Policy::Keyed {
        dedup,
        cap: resends,
    };
    let (_, verdict) = once::restart(journal, mode, policy, Seen::Dark);
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

/// Why a cut request is not sent again.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Cut {
    /// A restart found it cut; its provider declares no deduplication.
    Undeclared,
    /// A restart found it cut; it went out again as often as
    /// `retry.maxResends` allows.
    Capped,
    /// Its run was stopped.
    Stopped,
}

impl Cut {
    /// Why a restart of a run of `mode` does not send again a request to a
    /// provider that drops every repeat of its key or not (`dedups`).
    pub(super) fn of(mode: Mode, dedups: bool) -> Self {
        match (mode, dedups) {
            (Mode::Stop, _) => Self::Stopped,
            (Mode::Resume, false) => Self::Undeclared,
            (Mode::Resume, true) => Self::Capped,
        }
    }
}

/// The ledger's record of the request of attempt `attempt` of the
/// runtime's generation to `model` (`provider/model-id`), sent under the
/// idempotency key `key`, cut as `cut` says and never answered: what was
/// cut, why it is not sent again, and the money the host's budget keeps
/// counted for it (its reservation, charged in full by the restart) until
/// its usage is known. A model request's outcome is settled by its
/// provider's usage report, never by the user, so the record asks
/// nothing of the user.
fn unknown(
    runtime: &Runtime,
    attempt: u64,
    model: &str,
    key: Option<&str>,
    cut: Cut,
) -> SessionResult<UnknownEffect> {
    let why = match cut {
        Cut::Undeclared => {
            format!(
                "Model request to {model} cut by a crash, not resent (no deduplication declared)"
            )
        }
        Cut::Capped => {
            format!("Model request to {model} cut by a crash, not resent (resend limit reached)")
        }
        Cut::Stopped => format!("Model request to {model} cut by a stop"),
    };
    let what = match key.and_then(|key| runtime.lost_request_cost(key)) {
        Some(held) => format!(
            "{why}. Up to {} stays counted until its usage is known.",
            dollars(held)
        ),
        None => format!("{why}."),
    };
    Ok(UnknownEffect {
        id: format!("request:{}:{attempt}", runtime.task_id()),
        kind: EffectKind::Request,
        what,
        at: runtime.now()?,
        resolution: None,
    })
}

/// The request a stopped run leaves unknown: the ledger's record of the
/// request of attempt `attempt` (key `key`) when it went out (`sends`
/// times) and no reply came, else nothing.
///
/// # Errors
///
/// The clock, or an inconsistent build ([`decide`]).
pub(super) fn cut_by_stop(
    runtime: &Runtime,
    attempt: u64,
    model: &str,
    key: Option<&str>,
    sends: u32,
) -> SessionResult<Option<UnknownEffect>> {
    match decide(sends, false, runtime.settings().request_resends, Mode::Stop)? {
        Send::Interrupted => unknown(runtime, attempt, model, key, Cut::Stopped).map(Some),
        Send::Go | Send::Unsent => Ok(None),
    }
}

/// The run goes on after its request of attempt `attempt` to `model`
/// (key `key`) was cut and is not sent again (`cut`): the request is
/// noted unknown and, in the same commit, what it streamed before the cut
/// (a committed partial) becomes its aborted entry with its usage, and the
/// generation prepares a new request (`next`, the next attempt: a new
/// effect with its own key and reservation, sr141).
pub(super) async fn go_on_interrupted(
    runtime: &Runtime,
    attempt: u64,
    model: &str,
    key: Option<&str>,
    cut: Cut,
    next: GenerationCheckpoint,
    cx: &Context,
) -> SessionResult<()> {
    let effect = unknown(runtime, attempt, model, key, cut)?;
    let conversation_id = runtime.conversation_id();
    runtime
        .commit(
            move |tx, _current| async move {
                note_unknown(&tx, conversation_id, &effect).await?;
                let live = tx.doc(&LIVE_DOC, conversation_id).await?;
                convert_partial(&tx, &live, conversation_id).await?;
                live.set("generation", to_json(&live_generation(attempt + 1))?)?;
                Ok(Some(Next::Running { checkpoint: next }))
            },
            cx,
        )
        .await
}

/// End the run: its request of attempt `attempt` to `model` (key `key`)
/// was cut, is not sent again (`cut`), and the run made as many new
/// requests after cut ones as `retry.maxRetries` allows. The run's inputs
/// settle `unanswered` with `request_interrupted`, and, in the same
/// commit, the request is noted unknown and what it streamed before the
/// cut becomes its aborted entry with its usage.
pub(super) async fn fail_interrupted(
    runtime: &Runtime,
    attempt: u64,
    model: &str,
    key: Option<&str>,
    cut: Cut,
    cx: &Context,
) -> SessionResult<()> {
    let text = format!(
        "The model request to {model} was cut by a restart {attempt} times in a row and was \
         not sent again: its reply is unknown. Send your message again to continue."
    );
    let effect = unknown(runtime, attempt, model, key, cut)?;
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
                convert_partial(&tx, &live, conversation_id).await?;
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

    /// A request to a provider that drops every repeat of its key goes
    /// out once, then again after each restart that found it sent and
    /// unanswered, `resends` times; the next restart ends it unknown
    /// (spec O7).
    #[test]
    fn a_deduplicated_request_goes_out_again_at_most_its_resends() {
        let sent = |sends, resends| decide(sends, true, resends, Mode::Resume).unwrap();
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

    /// A request to a provider that declares no deduplication goes out
    /// once: a restart that found it sent ends it unknown, whatever the
    /// resends (spec O7, sr01).
    #[test]
    fn an_undeclared_request_goes_out_once() {
        let sent = |sends, resends| decide(sends, false, resends, Mode::Resume).unwrap();
        assert_eq!(
            [sent(0, 2), sent(1, 2), sent(1, 9), sent(2, 9)],
            [
                Send::Go,
                Send::Interrupted,
                Send::Interrupted,
                Send::Interrupted
            ]
        );
    }

    /// A stopped run sends nothing: an unsent request is reported unsent, a
    /// sent one unknown, whatever the resends left (spec O4, O5).
    #[test]
    fn a_stopped_run_sends_nothing() {
        for dedups in [false, true] {
            let stopped = |sends, resends| decide(sends, dedups, resends, Mode::Stop).unwrap();
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
