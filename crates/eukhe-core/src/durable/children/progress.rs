//! `rlm.progress.note`: a session's latest progress note with the 10-second
//! throttle, kept in the `eukhe.rlm.progress` conversation document so the
//! note and its throttle window survive a restart (the old store lived in
//! process memory).

use eukhe_chord::json::{from_json, to_json};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::session::{SessionResult, Tx};
use eukhe_durable::types::{ConversationId, LatestFork};
use serde::{Deserialize, Serialize};

/// Hard bound for one progress note, in UTF-16 code units.
pub(crate) const RLM_PROGRESS_NOTE_MAX_LENGTH: usize = 512;
/// Minimum spacing between accepted notes.
pub(crate) const RLM_PROGRESS_NOTE_MIN_INTERVAL_MS: f64 = 10_000.0;

/// The newest accepted note of a conversation.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct ProgressState {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) latest: Option<ProgressNote>,
}

/// One accepted note.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct ProgressNote {
    pub(crate) message: String,
    /// Wall-clock acceptance time (ms).
    pub(crate) at: f64,
}

pub(crate) static PROGRESS_DOC: ConversationDoc<ProgressState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.rlm.progress",
        version: 1,
        initial: ProgressState::default,
        migrate: None,
        checkpoint_when: None,
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.rlm.progress has a valid version"),
};

/// Outcome of one note.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum NoteOutcome {
    Accepted,
    /// Throttled; ms until the next note is accepted.
    Throttled {
        retry_after_ms: u64,
    },
}

/// Accept or throttle `message` (already validated) at `now` inside a
/// commit.
pub(crate) async fn tx_note(
    tx: &Tx,
    conversation_id: ConversationId,
    message: &str,
    now: f64,
) -> SessionResult<NoteOutcome> {
    let draft = tx.doc(&PROGRESS_DOC, conversation_id).await?;
    let state: ProgressState = from_json(&draft.value()?)?;
    if let Some(latest) = &state.latest {
        let elapsed = (now - latest.at).max(0.0);
        if elapsed < RLM_PROGRESS_NOTE_MIN_INTERVAL_MS {
            #[expect(
                clippy::cast_possible_truncation,
                clippy::cast_sign_loss,
                reason = "a positive remainder below the 10 s interval"
            )]
            let retry_after_ms = (RLM_PROGRESS_NOTE_MIN_INTERVAL_MS - elapsed).ceil() as u64;
            return Ok(NoteOutcome::Throttled { retry_after_ms });
        }
    }
    let note = ProgressNote {
        message: message.to_owned(),
        at: now,
    };
    draft.set("latest", to_json(&note)?)?;
    Ok(NoteOutcome::Accepted)
}

/// Message length in UTF-16 code units, matching the host-side bound.
pub(crate) fn utf16_length(message: &str) -> usize {
    message.chars().map(char::len_utf16).sum()
}
