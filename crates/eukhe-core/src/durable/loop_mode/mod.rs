//! `eukhe.loop`: `/loop`, the prompt sent again after every turn until its
//! stop condition is confirmed (spec/README.md L1-L10).
//!
//! Every decision is the compiled core's (`bend/loop.bend`, laws
//! `laws/loop/`, called through `eukhe_bend::rules::loop_mode`): Rust keeps
//! the state in the conversation document `eukhe.loop`, gathers the facts
//! (the clock, the exit status of the condition command, whether the
//! session is idle, whether the budget funds a turn) and carries out the
//! core's answer. The `pi.generation` hooks drive the loop at each final
//! answer; the run-end observer at each run that ends without one; the
//! `/loop` session command starts and stops it. [`watch_loop_updates`]
//! feeds the `loop_update` event.

mod args;
mod docs;
mod drive;
mod hooks;
mod observer;
mod watch;

#[cfg(test)]
pub(crate) mod tests;

use std::sync::Arc;

use eukhe_bend::rules::loop_mode::{verdict, LoopAct};
use eukhe_chord::context::Context;
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::Extension;
use eukhe_durable::harness::{Conversation, Harness, InboxItem, InboxState, INBOX_DOC};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{ConversationId, DocumentReader};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::loop_mode::{LoopPhase, LoopStatus};

pub use self::docs::{LoopDoc, LOOP_MODE_DOC};
pub use self::watch::{watch_loop_updates, LoopUpdates};

use self::args::{parse_loop_command, status_message, LoopCommand};
use self::drive::{decide, Input, LoopHost, Mode};
use super::goals::{open_doc, read_doc, write_doc};
use super::HostDeps;
use crate::autonomous::{now_millis, GateCommandRunner, ShellGateRunner};

/// The extension's name.
pub const LOOP_EXTENSION: &str = "eukhe.loop";

/// The `customType` of the display row a loop appends when it ends by
/// itself (a command that ends it reports in its own result row).
pub const LOOP_NOTICE_CUSTOM_TYPE: &str = "eukhe.loop";

/// Whether the session's budget funds one more turn of the loop: the fact
/// `funded` of the core's next-iteration decision. No budget is set on a
/// session yet, so every turn is funded; the budget pillar points this at
/// its phase (`budget.phase() == BudgetPhase::Working`).
fn loop_budget_ok() -> bool {
    true
}

/// The loop extension of one session: the `pi.generation` hooks and the
/// run-end observer. The condition command runs in the session cwd.
/// Installed before the goal extension: while a loop continues a final
/// answer, the goal's continuation waits.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    loop_extension(
        deps,
        Arc::new(ShellGateRunner::new(deps.cwd.clone())),
        Arc::new(loop_budget_ok),
    )
}

/// [`extension`] over explicit services (the condition runner and the
/// budget fact are the seams the tests script).
pub(crate) fn loop_extension(
    deps: &Arc<HostDeps>,
    gates: Arc<dyn GateCommandRunner>,
    funded: Arc<dyn Fn() -> bool + Send + Sync>,
) -> Arc<Extension> {
    let host = LoopHost {
        harness: deps.harness.clone(),
        gates,
        funded,
    };
    observer::install(deps, &host);
    define_extension(Extension {
        name: LOOP_EXTENSION.to_owned(),
        hooks: vec![hooks::generation_hooks(&host)],
        ..Extension::default()
    })
}

/// The loop services of a session outside its hooks (the `/loop` command,
/// the compaction hold).
fn host_of(deps: &Arc<HostDeps>) -> LoopHost {
    LoopHost {
        harness: deps.harness.clone(),
        gates: Arc::new(ShellGateRunner::new(deps.cwd.clone())),
        funded: Arc::new(loop_budget_ok),
    }
}

/// What every surface shows of the loop of `conversation_id` (no loop
/// when the document does not exist).
///
/// # Errors
///
/// Read failures, or a failed call to the compiled core.
pub async fn loop_status(
    reader: &(impl DocumentReader + ?Sized),
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<LoopStatus> {
    let doc = read_doc(reader, &LOOP_MODE_DOC, conversation_id, cx)
        .await?
        .unwrap_or_default();
    status_of(&doc)
}

fn status_of(doc: &LoopDoc) -> SessionResult<LoopStatus> {
    let last_verdict = match (&doc.state.condition, doc.state.last_check) {
        (Some(condition), Some(check)) => {
            Some(verdict(condition.until, check.evidence).map_err(|error| {
                SessionError::error(format!("the loop's verdict failed: {error}"))
            })?)
        }
        (None, _) | (_, None) => None,
    };
    Ok(LoopStatus {
        state: doc.state.clone(),
        limit: doc.limit,
        started_at_ms: doc.started_at_ms,
        verdict: last_verdict,
        message: doc.message.clone(),
    })
}

/// Why `/loop` failed: the malformed-arguments message, or the session's
/// failure.
#[derive(Debug, thiserror::Error)]
pub enum LoopCommandError {
    /// The arguments did not parse.
    #[error("{0}")]
    Args(String),
    /// The session failed to read, commit or submit.
    #[error(transparent)]
    Session(#[from] SessionError),
}

/// Withdraw the queued iterations of the loop: a loop that ended or
/// paused never lets a stale iteration run behind it.
async fn withdraw_queued_iterations(
    harness: &Harness,
    conversation_id: ConversationId,
    cx: &Context,
) -> SessionResult<()> {
    let inbox: InboxState = read_doc(harness, &INBOX_DOC, conversation_id, cx)
        .await?
        .unwrap_or_default();
    for item in inbox.items {
        let queued = match &item {
            InboxItem::Steer { origin, .. } | InboxItem::FollowUp { origin, .. } => {
                matches!(origin, InputOrigin::Loop { .. })
            }
            InboxItem::Write { .. } => false,
        };
        if queued {
            harness
                .abort_submission(item.id(), Some(conversation_id), cx)
                .await?;
        }
    }
    Ok(())
}

/// `/loop <args>` on `conversation`: start a loop, end the one that is on,
/// stop, or show the status. Returns the line to show.
///
/// # Errors
///
/// The malformed-arguments message; read, commit or submission failures.
pub(crate) async fn execute_loop_command(
    deps: &Arc<HostDeps>,
    conversation: &Conversation,
    args: &str,
    cx: &Context,
) -> Result<String, LoopCommandError> {
    let host = host_of(deps);
    let harness = host.harness.require()?;
    let input = match parse_loop_command(args).map_err(LoopCommandError::Args)? {
        LoopCommand::Status => {
            let doc = read_doc(&harness, &LOOP_MODE_DOC, conversation.id(), cx)
                .await?
                .unwrap_or_default();
            return Ok(status_message(&doc, now_millis()));
        }
        LoopCommand::Stop => Input::Stop,
        LoopCommand::Enter {
            limit,
            condition,
            prompt,
        } => Input::Enter {
            limit,
            condition,
            prompt,
        },
    };
    let facts = host
        .facts(&harness, conversation.id(), Mode::Idle, cx)
        .await?;
    let (doc, act) = decide(conversation, input, facts, Mode::Idle, false, cx).await?;
    let rested = act == LoopAct::Rest;
    match act {
        LoopAct::Submit { iteration, text } => {
            host.start(conversation, &doc, iteration, text, cx).await?;
        }
        LoopAct::Report(_) => {
            withdraw_queued_iterations(&harness, conversation.id(), cx).await?;
        }
        LoopAct::Rest
        | LoopAct::Adopt { .. }
        | LoopAct::Judge { .. }
        | LoopAct::Resume { .. }
        | LoopAct::Defer => {}
    }
    // A stop that found no loop changed nothing.
    if rested && !doc.state.phase.is_on() {
        return Ok("Loop mode is not enabled.".to_owned());
    }
    Ok(doc
        .message
        .unwrap_or_else(|| "Loop mode disabled.".to_owned()))
}

/// Before a manual compaction aborts the run: a loop with a turn in
/// flight is held, so the abort is not read as the user's interrupt.
/// Returns whether a loop is held.
///
/// # Errors
///
/// Read or commit failures.
pub async fn hold_loop_for_compaction(
    harness: &Harness,
    conversation: &Conversation,
    cx: &Context,
) -> SessionResult<bool> {
    let conversation_id = conversation.id();
    let pending = read_doc(harness, &LOOP_MODE_DOC, conversation_id, cx)
        .await?
        .is_some_and(|doc| matches!(doc.state.phase, LoopPhase::Turn | LoopPhase::Judging));
    if !pending {
        return Ok(false);
    }
    conversation
        .commit(
            move |tx| async move {
                let (draft, mut doc) = open_doc(&tx, &LOOP_MODE_DOC, conversation_id).await?;
                let held = matches!(doc.state.phase, LoopPhase::Turn | LoopPhase::Judging);
                if held && !doc.held {
                    doc.held = true;
                    write_doc(&draft, &doc)?;
                }
                Ok(held)
            },
            cx,
        )
        .await
}

/// After the manual compaction (done, skipped or failed): a held loop
/// takes its work up again: the cut turn is sent again as the same
/// iteration, a cut check runs again.
///
/// # Errors
///
/// Read, commit or submission failures.
pub async fn resume_loop_after_compaction(
    deps: &Arc<HostDeps>,
    conversation: &Conversation,
    cx: &Context,
) -> SessionResult<()> {
    let conversation_id = conversation.id();
    let released = conversation
        .commit(
            move |tx| async move {
                let (draft, mut doc) = open_doc(&tx, &LOOP_MODE_DOC, conversation_id).await?;
                if !doc.held {
                    return Ok(false);
                }
                doc.held = false;
                // The cut turn is sent again under a new request id.
                doc.resends += 1;
                doc.yield_record = None;
                doc.adopted = None;
                write_doc(&draft, &doc)?;
                Ok(true)
            },
            cx,
        )
        .await?;
    if released {
        host_of(deps)
            .drive(conversation, Input::TakeUp, Mode::Idle, cx)
            .await?;
    }
    Ok(())
}
