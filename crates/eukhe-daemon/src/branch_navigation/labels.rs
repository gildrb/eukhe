//! Tree-node labels (TS `appendLabelChange` / `labelsById`): one
//! session-scope document, `eukhe.daemon.labels`, mapping an entry id to its
//! active label and the time it was set. Clearing a label removes its key.

use std::collections::BTreeMap;

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_durable::documents::{DocDefinition, SessionDoc};
use eukhe_durable::harness::json::assign_json;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::DocumentReaderExt;
use serde::{Deserialize, Serialize};

/// One active label.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct EntryLabel {
    pub(crate) label: String,
    /// ISO-8601 time the label was set (`labelTimestamp`).
    pub(crate) timestamp: String,
}

/// The `eukhe.daemon.labels` value: entry id -> its active label.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub(crate) struct EntryLabels(pub(crate) BTreeMap<String, EntryLabel>);

impl EntryLabels {
    /// `(label, timestamp)` of `entry_id`.
    pub(crate) fn get(&self, entry_id: &str) -> Option<(String, String)> {
        self.0
            .get(entry_id)
            .map(|label| (label.label.clone(), label.timestamp.clone()))
    }
}

/// The session-scope `eukhe.daemon.labels` document (version 1).
pub(crate) static LABELS_DOC: SessionDoc<EntryLabels> = match SessionDoc::define(DocDefinition {
    kind: "eukhe.daemon.labels",
    version: 1,
    initial: EntryLabels::default,
    migrate: None,
    checkpoint_when: None,
}) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.daemon.labels has a valid version"),
};

/// The session's active labels (empty when never written).
///
/// # Errors
///
/// The document cannot be read or decoded.
pub(crate) async fn read_labels(harness: &Harness, cx: &Context) -> SessionResult<EntryLabels> {
    match harness.snapshot(&LABELS_DOC, (), cx).await? {
        Some(value) => from_json(&JsonValue::Object(value)).map_err(SessionError::other),
        None => Ok(EntryLabels::default()),
    }
}

/// Set (`Some`) or clear (`None`) the label of `entry_id` in one commit.
///
/// # Errors
///
/// The commit fails.
pub(crate) async fn set_label(
    harness: &Harness,
    entry_id: String,
    label: Option<String>,
    cx: &Context,
) -> SessionResult<()> {
    let value = match label {
        Some(label) => Some(
            to_json(&EntryLabel {
                label,
                timestamp: crate::util::now_iso(),
            })
            .map_err(SessionError::other)?,
        ),
        None => None,
    };
    harness
        .commit(
            move |tx| async move {
                let draft = tx.doc(&LABELS_DOC, ()).await?;
                match value {
                    Some(value) => assign_json(&draft, entry_id.as_str(), &value)?,
                    None => {
                        if draft.get(entry_id.as_str())?.is_some() {
                            draft.delete(entry_id.as_str())?;
                        }
                    }
                }
                Ok(())
            },
            cx,
        )
        .await
}
