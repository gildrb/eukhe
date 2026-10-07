//! Daemon-owned session metadata kept in the durable storage: the session
//! name (`rename` / `set_session_name`) and the once-per-session Anthropic
//! warning marker. One session-scope document, `eukhe.daemon.session`.

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_durable::documents::{DocDefinition, SessionDoc};
use eukhe_durable::harness::json::assign_json;
use eukhe_durable::harness::Harness;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::DocumentReaderExt;
use serde::{Deserialize, Serialize};

/// The `eukhe.daemon.session` document value.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct SessionMeta {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) name: Option<String>,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub(crate) anthropic_warning_shown: bool,
    /// A `kill` (not a `shutdown`) archived the session.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub(crate) archived: bool,
}

/// The session-scope `eukhe.daemon.session` document (version 1).
pub(crate) static SESSION_META_DOC: SessionDoc<SessionMeta> =
    match SessionDoc::define(DocDefinition {
        kind: "eukhe.daemon.session",
        version: 1,
        initial: SessionMeta::default,
        migrate: None,
        checkpoint_when: None,
    }) {
        Ok(token) => token,
        Err(_) => panic!("eukhe.daemon.session has a valid version"),
    };

/// The session's metadata (defaults when never written).
///
/// # Errors
///
/// The document cannot be read or decoded.
pub(crate) async fn read_session_meta(
    harness: &Harness,
    cx: &Context,
) -> SessionResult<SessionMeta> {
    match harness.snapshot(&SESSION_META_DOC, (), cx).await? {
        Some(value) => from_json(&JsonValue::Object(value)).map_err(SessionError::other),
        None => Ok(SessionMeta::default()),
    }
}

/// Set (`Some`) or clear (`None`) the session name in one commit.
///
/// # Errors
///
/// The commit fails.
pub(crate) async fn set_session_name(
    harness: &Harness,
    name: Option<String>,
    cx: &Context,
) -> SessionResult<()> {
    let value = match name {
        Some(name) => to_json(&name).map_err(SessionError::other)?,
        None => JsonValue::Null,
    };
    harness
        .commit(
            move |tx| async move {
                let draft = tx.doc(&SESSION_META_DOC, ()).await?;
                if value.is_null() {
                    if draft.get("name")?.is_some() {
                        draft.delete("name")?;
                    }
                } else {
                    assign_json(&draft, "name", &value)?;
                }
                Ok(())
            },
            cx,
        )
        .await
}

/// Record that the session showed the Anthropic warning.
///
/// # Errors
///
/// The commit fails.
pub(crate) async fn mark_anthropic_warning_shown(
    harness: &Harness,
    cx: &Context,
) -> SessionResult<()> {
    harness
        .commit(
            move |tx| async move {
                let draft = tx.doc(&SESSION_META_DOC, ()).await?;
                assign_json(&draft, "anthropicWarningShown", &JsonValue::Bool(true))?;
                Ok(())
            },
            cx,
        )
        .await
}

/// Record that a `kill` archived the session.
///
/// # Errors
///
/// The commit fails.
pub(crate) async fn mark_archived(harness: &Harness, cx: &Context) -> SessionResult<()> {
    harness
        .commit(
            move |tx| async move {
                let draft = tx.doc(&SESSION_META_DOC, ()).await?;
                assign_json(&draft, "archived", &JsonValue::Bool(true))?;
                Ok(())
            },
            cx,
        )
        .await
}
