//! The conversation documents of `eukhe.optchat`: the pinned view of the
//! current call, and the chat logger's cursor.

use eukhe_chord::delta::Draft;
use eukhe_chord::json::{from_json, to_json, JsonObject, JsonValue};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{EntryId, LatestFork};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

/// The view a call starts from (§6, §7), rendered once and pinned: every
/// request of the call sends it byte-identical (the cache prefix), across
/// a crash too.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CallState {
    /// The run this view belongs to (a root's call); absent for a
    /// subagent, whose view is pinned once per conversation.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub run_key: Option<String>,
    /// The view cut at its cache marks; every piece but the last carries a
    /// cache breakpoint.
    pub pieces: Vec<String>,
    /// Chat messages the view covers (`T`).
    pub through: u64,
    /// When the view was rendered (ms since the epoch): the timestamp of
    /// the call's first message.
    pub timestamp: u64,
}

/// `eukhe.optchat.call`: a fork starts its own call.
pub static CALL_DOC: ConversationDoc<CallState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.optchat.call",
        version: 1,
        initial: CallState::default,
        migrate: None,
        checkpoint_when: None,
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("invalid eukhe.optchat.call definition"),
};

/// Where a root conversation's chat logging stands: every entry through
/// `through` is in the chat log, as `lines` lines in all (the next line's
/// idempotency key is `lines`).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct LoggedState {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub through: Option<EntryId>,
    pub lines: u64,
}

/// `eukhe.optchat.logged`: a fork carries its parent's cursor, so the
/// history it shares is not logged twice.
pub static LOGGED_DOC: ConversationDoc<LoggedState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.optchat.logged",
        version: 1,
        initial: LoggedState::default,
        migrate: None,
        checkpoint_when: None,
    },
    LatestFork::Current,
) {
    Ok(token) => token,
    Err(_) => panic!("invalid eukhe.optchat.logged definition"),
};

/// A committed document value as its type.
pub(crate) fn decode<T: serde::de::DeserializeOwned>(value: &Arc<JsonObject>) -> SessionResult<T> {
    Ok(from_json(&JsonValue::Object(Arc::clone(value)))?)
}

/// Write `value` over the document draft: every field set, absent
/// optional fields removed.
pub(crate) fn write<T: Serialize>(
    draft: &Draft,
    value: &T,
    optional: &[&str],
) -> SessionResult<()> {
    let JsonValue::Object(fields) = to_json(value)? else {
        return Err(eukhe_durable::session::SessionError::type_error(
            "an eukhe.optchat document must be an object",
        ));
    };
    for key in optional {
        if fields.get(key).is_none() {
            draft.delete(*key)?;
        }
    }
    for (key, field) in fields.iter() {
        draft.set(key.as_ref(), field.clone())?;
    }
    Ok(())
}
