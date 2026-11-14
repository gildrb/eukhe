//! Acceptance operations over a conversation: the state every surface
//! reads, the owner's change of the checks, and the worker's claim. Each
//! change is one commit that asks the compiled core
//! (`eukhe_bend::rules::verify::act`) whether the actor may make it.

use std::path::Path;

use eukhe_bend::rules::verify::{self, Actor, Label, Op};
use eukhe_chord::context::Context;
use eukhe_durable::harness::{Conversation, Harness};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, DocumentReader};
use eukhe_types::acceptance::{
    AcceptanceCheck, AcceptanceLabel, AcceptanceSeed, AcceptanceState, CheckSpec,
};

use super::docs::{AcceptanceDoc, ACCEPTANCE_DOC};
use super::evidence::protect;
use super::workspace::state_now;
use crate::durable::goals::{conversation_of, open_doc, read_doc, write_doc};

pub(crate) fn core_error(error: eukhe_bend::Error) -> SessionError {
    SessionError::other(error)
}

pub(crate) fn label_of(label: Label) -> AcceptanceLabel {
    match label {
        Label::Verified => AcceptanceLabel::Verified,
        Label::Failed => AcceptanceLabel::Failed,
        Label::Unverified => AcceptanceLabel::Unverified,
        Label::Passed => AcceptanceLabel::ChecksPassedUnconfined,
    }
}

/// The state of `conversation` now for `doc`: its newest effect, its
/// newest user message and the fingerprint of the workspace the checks
/// judge ([`state_now`]).
///
/// # Errors
///
/// Read failures.
pub(crate) async fn doc_state(
    conversation: &Conversation,
    doc: &AcceptanceDoc,
    cx: &Context,
) -> SessionResult<u64> {
    state_now(conversation, doc.workspace.as_deref(), cx).await
}

/// `doc` as every surface reads it on the state `now`: its label is the
/// compiled core's.
pub(crate) fn served(doc: &AcceptanceDoc, now: u64) -> SessionResult<AcceptanceState> {
    Ok(AcceptanceState {
        label: label_of(verify::label(now, &doc.slots()).map_err(core_error)?),
        state: now,
        revision: doc.revision,
        checks: doc.checks.clone(),
        claimed: doc.claimed,
        tries: doc.tries,
        max_returns: doc.max_returns,
        last_end: doc.last_end.clone(),
    })
}

/// The acceptance of `conversation_id`: its checks, each one's last
/// verdict and evidence, and the label of the result on the conversation's
/// state now (`unverified` with no checks).
///
/// # Errors
///
/// Read failures, or no such conversation.
pub async fn acceptance_state(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<AcceptanceState> {
    let doc = read_doc(harness, &ACCEPTANCE_DOC, conversation_id, cx)
        .await?
        .unwrap_or_default();
    let conversation = conversation_of(harness, conversation_id, cx).await?;
    served(&doc, doc_state(&conversation, &doc, cx).await?)
}

/// The slots of `conversation_id`'s checks, for the exit rule; none when
/// the conversation has no acceptance.
pub(crate) async fn stored(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<Option<AcceptanceDoc>> {
    read_doc(reader, &ACCEPTANCE_DOC, conversation_id, cx).await
}

/// The exit code of a headless run of `conversation_id` whose own code is
/// `base`: the compiled core's (`verify::exit`): `base` when every
/// acceptance check is confirmed on the final state (also with no checks),
/// else nonzero.
///
/// # Errors
///
/// Read failures, or no such conversation.
pub async fn acceptance_exit_code(
    harness: &Harness,
    conversation_id: ConversationId,
    base: u64,
    cx: &Context,
) -> SessionResult<u64> {
    let doc = stored(harness, conversation_id, cx)
        .await?
        .unwrap_or_default();
    let conversation = conversation_of(harness, conversation_id, cx).await?;
    let now = doc_state(&conversation, &doc, cx).await?;
    verify::exit(base, now, &doc.slots()).map_err(core_error)
}

/// Why a check is no check.
fn refusal(spec: &CheckSpec) -> Option<&'static str> {
    let blank = |text: &str| text.trim().is_empty();
    match spec {
        CheckSpec::Command { command, .. } | CheckSpec::Until { command, .. } => {
            blank(command).then_some("an acceptance check needs a command")
        }
        CheckSpec::Judge { condition, .. } => {
            blank(condition).then_some("a judge check needs a condition")
        }
        CheckSpec::Intent { .. } => None,
    }
}

/// Set the checks of `conversation_id` as `who`: the compiled core admits
/// only the task's owner. An admitted change starts a new revision: every
/// check unjudged, no claim, no tries; the protected files of each command
/// check are hashed as they are now under `cwd`. `max_returns` replaces
/// the cap of returns in a row when given. Returns the new state.
///
/// # Errors
///
/// A check with no command or condition; the core refuses the change (not
/// the owner, or more checks than a task may carry); read or commit
/// failures.
pub(crate) async fn assign(
    harness: &Harness,
    conversation_id: ConversationId,
    who: Actor,
    specs: Vec<CheckSpec>,
    max_returns: Option<u64>,
    cwd: &Path,
    cx: &Context,
) -> SessionResult<AcceptanceState> {
    if let Some(reason) = specs.iter().find_map(refusal) {
        return Err(SessionError::error(reason));
    }
    let checks: Vec<AcceptanceCheck> = specs
        .into_iter()
        .map(|spec| {
            let protected = match &spec {
                CheckSpec::Command { protect: paths, .. } => protect(cwd, paths),
                CheckSpec::Judge { .. } | CheckSpec::Until { .. } | CheckSpec::Intent { .. } => {
                    Vec::new()
                }
            };
            AcceptanceCheck {
                spec,
                protected,
                result: None,
            }
        })
        .collect();
    let conversation = conversation_of(harness, conversation_id, cx).await?;
    let workspace = cwd.to_path_buf();
    let doc = conversation
        .commit(
            move |tx| async move {
                let (draft, mut doc) = open_doc(&tx, &ACCEPTANCE_DOC, conversation_id).await?;
                let count = u64::try_from(checks.len()).unwrap_or(u64::MAX);
                let (admitted, next) =
                    verify::act(who, Op::Assign { checks: count }, &doc.core()).map_err(core_error)?;
                if !admitted {
                    return Err(SessionError::error(match who {
                        Actor::Owner => {
                            "the acceptance checks were refused: a task carries at most 64 checks"
                        }
                        Actor::Worker | Actor::Verifier => {
                            "only the task's owner sets its acceptance checks: this change was refused"
                        }
                    }));
                }
                doc.checks = checks;
                doc.adopt(&next, None)?;
                if let Some(max_returns) = max_returns {
                    doc.max_returns = max_returns;
                }
                doc.last_end = None;
                doc.yield_record = None;
                doc.workspace = Some(workspace);
                write_doc(&draft, &doc)?;
                Ok(doc)
            },
            cx,
        )
        .await?;
    served(&doc, doc_state(&conversation, &doc, cx).await?)
}

/// Set the acceptance checks of `conversation_id` as its owner (the user,
/// an SDK client, the CLI): `specs` replace the current checks (none
/// clears them), every verdict is discarded, and `max_returns` replaces
/// the cap of returns in a row when given. Returns the new state.
///
/// # Errors
///
/// A check with no command or condition, more than 64 checks, read or
/// commit failures, or no such conversation.
pub async fn set_acceptance(
    harness: &Harness,
    conversation_id: ConversationId,
    specs: Vec<CheckSpec>,
    max_returns: Option<u64>,
    cwd: &Path,
    cx: &Context,
) -> SessionResult<AcceptanceState> {
    assign(
        harness,
        conversation_id,
        Actor::Owner,
        specs,
        max_returns,
        cwd,
        cx,
    )
    .await
}

/// Start `conversation_id` with the checks of `seed`, as its owner (the
/// CLI's `--accept-*` flags, a client's create config). A conversation
/// that already carries exactly these checks keeps them and their
/// verdicts (a resumed session); any other gets them as a new revision.
/// Returns whether the checks were set.
///
/// # Errors
///
/// As [`set_acceptance`].
pub async fn seed_acceptance(
    harness: &Harness,
    conversation_id: ConversationId,
    seed: &AcceptanceSeed,
    cwd: &Path,
    cx: &Context,
) -> SessionResult<bool> {
    let current = stored(harness, conversation_id, cx)
        .await?
        .unwrap_or_default();
    let specs = seed.specs();
    let same_checks = current
        .checks
        .iter()
        .map(|check| &check.spec)
        .eq(specs.iter());
    let same_cap = seed
        .max_returns
        .is_none_or(|max_returns| max_returns == current.max_returns);
    if same_checks && same_cap {
        return Ok(false);
    }
    set_acceptance(harness, conversation_id, specs, seed.max_returns, cwd, cx).await?;
    Ok(true)
}

/// What a claim of "done" met.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Claimed {
    /// The task has no acceptance checks: the claim stands, unverified.
    Unchecked,
    /// The claim waits: the verifier judges this many checks at the final
    /// answer.
    Pending { checks: usize },
}

/// The worker's claim that the goal of `conversation` is achieved
/// (`goal.complete()`). With checks the claim waits for the verifier,
/// marked as the goal's; with none nothing is written.
///
/// # Errors
///
/// Read or commit failures.
pub(crate) async fn claim(
    reader: &(impl DocumentReader + ?Sized),
    conversation: &Conversation,
    cx: &Context,
) -> SessionResult<Claimed> {
    let conversation_id = conversation.id();
    let checked = stored(reader, conversation_id, cx)
        .await?
        .is_some_and(|doc| !doc.checks.is_empty());
    if !checked {
        return Ok(Claimed::Unchecked);
    }
    conversation
        .commit(
            move |tx| async move {
                let (draft, mut doc) = open_doc(&tx, &ACCEPTANCE_DOC, conversation_id).await?;
                if doc.checks.is_empty() {
                    return Ok(Claimed::Unchecked);
                }
                let (_, next) =
                    verify::act(Actor::Worker, Op::Claim, &doc.core()).map_err(core_error)?;
                doc.adopt(&next, None)?;
                doc.goal_claim = doc.claimed;
                write_doc(&draft, &doc)?;
                Ok(Claimed::Pending {
                    checks: doc.checks.len(),
                })
            },
            cx,
        )
        .await
}
