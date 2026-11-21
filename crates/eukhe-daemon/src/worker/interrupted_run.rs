//! The reopen of a session whose run the supervisor interrupted
//! (`supervisor/interrupted_runs.rs`): its worker stopped answering and was
//! killed, or crashed past the restart budget. The open stopped the run
//! (`StoredWork::Stop`), so the step that hung or crashed does not run
//! again by itself; the turn then goes on without anyone watching. The
//! compiled core decides from the automatic continues this turn already
//! made (`eukhe_bend::rules::restart_turn::reopened`): the turn continues
//! with a harness continuation, or, past the cap, the run ends. Either way
//! a display row says what happened, and the continuation asks the final
//! answer to say the worker was restarted. Effects a stopped step may have
//! left are not settled here.

use eukhe_bend::rules::restart_turn::{self, Reopened};
use eukhe_chord::context::Context;
use eukhe_durable::entries::{UserData, USER_ENTRY};
use eukhe_durable::errors::ConversationBusy;
use eukhe_durable::harness::types::{InputSubmissionDraft, WhenBusy, WriteSubmissionDraft};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::{EntryData, EntryRecord};
use eukhe_types::input_origin::InputOrigin;
use eukhe_types::pi_ai::UserContent;
use serde_json::Value;

/// How many entries one page of the count reads.
const PAGE: usize = 64;

/// The `interruptedRun` a reopen carries: what happened, and the
/// declaration's identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Interrupted {
    cause: String,
    declared_at: String,
}

impl Interrupted {
    /// The declaration in `value`.
    pub(super) fn parse(value: &Value) -> anyhow::Result<Self> {
        let field = |key: &str| {
            value
                .get(key)
                .and_then(Value::as_str)
                .map(str::to_owned)
                .ok_or_else(|| anyhow::anyhow!("interruptedRun carries no {key}"))
        };
        Ok(Self {
            cause: field("cause")?,
            declared_at: field("declaredAt")?,
        })
    }
}

/// The display row of a reopen that did `next`.
fn notice(cause: &str, next: Reopened) -> String {
    match next {
        Reopened::Continue { n } => format!(
            "{cause}; Eukhe restarted it and continued the turn (automatic continue {n} of this turn)."
        ),
        Reopened::End { n } => format!(
            "{cause}; Eukhe restarted it and ended the run: the turn already continued {n} times after restarts."
        ),
    }
}

/// The harness continuation of a turn the supervisor interrupted.
fn continuation(cause: &str) -> String {
    format!(
        "{cause}; Eukhe restarted the session worker, which stopped this turn mid-run. Continue the user's latest request from where it stopped. A tool call that was running when the worker stopped may or may not have taken effect: check its result or the state it changes before running it again. The final answer says the session worker was restarted."
    )
}

/// What one entry is to the count.
enum Counted {
    /// No input.
    Other,
    /// A restart continuation.
    Continuation,
    /// An input of another origin: the turn starts there.
    TurnStart,
}

/// What `entry` is to the count.
fn counted(entry: &EntryRecord) -> SessionResult<Counted> {
    if entry.kind != USER_ENTRY.kind() {
        return Ok(Counted::Other);
    }
    let origin = UserData::decode(entry.data.as_ref())
        .map_err(|error| SessionError::error(format!("a user entry's origin: {error}")))?
        .origin;
    Ok(if origin == InputOrigin::RestartResume {
        Counted::Continuation
    } else {
        Counted::TurnStart
    })
}

/// The automatic continues this turn made: the restart continuations since
/// the conversation's last input of another origin.
async fn continues_made(main: &Conversation, cx: &Context) -> SessionResult<u64> {
    let mut made = 0;
    let mut cursor = None;
    loop {
        let page = main
            .entries(ConversationEntryQuery::default(), PAGE, cursor, cx)
            .await?;
        for entry in &page.items {
            match counted(entry)? {
                Counted::Continuation => made += 1,
                Counted::TurnStart => return Ok(made),
                Counted::Other => {}
            }
        }
        match page.next {
            Some(next) => cursor = Some(next),
            None => return Ok(made),
        }
    }
}

/// Go on with the turn the supervisor interrupted: write the row that says
/// what happened and, below the cap, submit the continuation (queued input
/// that took the session first drives the turn instead). Request ids are
/// the declaration's, so a replayed declaration writes one row and one
/// continuation.
pub(super) async fn resume(
    main: &Conversation,
    interrupted: &Interrupted,
    cx: &Context,
) -> anyhow::Result<Reopened> {
    let next = restart_turn::reopened(continues_made(main, cx).await?);
    let entry = eukhe_core::durable::custom_entry_draft(
        eukhe_types::custom_type::WORKER_RESTART_NOTICE_CUSTOM_TYPE,
        UserContent::Text(notice(&interrupted.cause, next)),
        true,
        None,
        crate::util::now_ms(),
    )?;
    main.submit(
        WriteSubmissionDraft {
            request_id: Some(format!("worker-restart:{}", interrupted.declared_at)),
            entry,
        },
        cx,
    )
    .await?;
    match next {
        Reopened::Continue { .. } => {
            let draft = InputSubmissionDraft {
                request_id: Some(format!("worker-restart-resume:{}", interrupted.declared_at)),
                content: UserContent::Text(continuation(&interrupted.cause)),
                when_busy: Some(WhenBusy::Reject),
                origin: InputOrigin::RestartResume,
                entry: None,
            };
            match main.submit(draft, cx).await {
                Ok(_) => {}
                Err(SessionError::Other(inner))
                    if inner.downcast_ref::<ConversationBusy>().is_some() => {}
                Err(error) => return Err(error.into()),
            }
        }
        Reopened::End { .. } => {}
    }
    Ok(next)
}

#[cfg(test)]
#[path = "interrupted_run_tests.rs"]
mod tests;
