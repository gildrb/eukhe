//! Conversations, transcript entries, and context edits (`types.ts`, spec §2, §2.1).

use std::ops::Deref;

use eukhe_chord::json::{from_json, to_json, JsonError, JsonValue};
use eukhe_types::pi_ai::Message;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::ids::{ConversationId, EntryId, TaskId};
use super::json_serde::present;

/// Ownership selected explicitly whenever a conversation is created.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "camelCase",
    rename_all_fields = "camelCase"
)]
pub enum ConversationOwnership {
    /// No owning task.
    Ownerless,
    /// Owned by a task; the Session derives the persisted owner's conversation from it.
    Task {
        /// The owning task.
        task_id: TaskId,
    },
}

/// Fork source and inclusive parent entry through which history is inherited.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ConversationParent {
    /// The parent conversation.
    pub conversation_id: ConversationId,
    /// The last inherited parent entry, visible to the parent.
    pub at: EntryId,
}

/// Creator edge used for attribution, subtree abort, and subtree idle waits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ConversationOwner {
    /// The owning task's conversation.
    pub conversation_id: ConversationId,
    /// The owning task.
    pub task_id: TaskId,
}

/// Immutable identity, history ancestry, and task ownership of a transcript scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ConversationRecord {
    /// The conversation's ID.
    pub id: ConversationId,
    /// Fork source and inclusive parent entry through which history is inherited.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parent: Option<ConversationParent>,
    /// Creator edge used for attribution, subtree abort, and subtree idle waits.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub owner: Option<ConversationOwner>,
}

/// An immutable override of one visible entry's contribution to model context.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ContextEdit {
    /// Entry whose model messages are omitted or replaced.
    pub target: EntryId,
    /// What the edit does to the target's messages.
    #[serde(flatten)]
    pub action: ContextEditAction,
}

/// The action of a [`ContextEdit`], tagged by `action`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "action", rename_all = "camelCase")]
pub enum ContextEditAction {
    /// The target contributes no model messages.
    Omit,
    /// The target contributes `messages` instead of its own model messages.
    Replace {
        /// Messages contributed instead of the target entry's model messages.
        messages: Vec<Message>,
    },
}

/// Immutable transcript event with separate model-facing and
/// application-facing payloads.
///
/// Fields serialize in the order the TS Session writes them for token-typed
/// appends (`{ ...draft, kind, id, conversationId, head, byTaskId }`), which
/// covers every built-in entry kind.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EntryRecord {
    /// Messages contributed to model context; absent for display or bookkeeping entries.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model: Option<Vec<Message>>,
    /// JSON payload consumed by views, extensions, or bookkeeping logic.
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "present"
    )]
    pub data: Option<JsonValue>,
    /// Context-only overrides of earlier visible entries.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub edits: Option<Vec<ContextEdit>>,
    /// Application-defined entry discriminator.
    pub kind: String,
    /// The entry's ID.
    pub id: EntryId,
    /// The conversation the entry was appended to.
    pub conversation_id: ConversationId,
    /// First entry in the active context selected by this entry.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub head: Option<EntryId>,
    /// Task that appended this entry, when it was produced by durable work.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub by_task_id: Option<TaskId>,
}

/// The `head` of an [`EntryDraft`]: an existing entry, or `"self"`, which
/// starts active context at the newly assigned entry ID.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntryHead {
    /// An existing entry.
    Entry(EntryId),
    /// `"self"`: the entry being appended.
    SelfEntry,
}

impl Serialize for EntryHead {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Entry(id) => id.serialize(serializer),
            Self::SelfEntry => serializer.serialize_str("self"),
        }
    }
}

impl<'de> Deserialize<'de> for EntryHead {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match JsonValue::deserialize(deserializer)? {
            JsonValue::String(text) if &*text == "self" => Ok(Self::SelfEntry),
            JsonValue::Number(number) => number
                .as_u64()
                .map(|value| Self::Entry(EntryId::from_number(value)))
                .ok_or_else(|| serde::de::Error::custom(format!("invalid entry head {number}"))),
            other => Err(serde::de::Error::custom(format!(
                "invalid entry head {other}"
            ))),
        }
    }
}

/// Entry content supplied before the Session assigns identity and task attribution.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct EntryDraft {
    /// Application-defined entry discriminator.
    pub kind: String,
    /// Messages contributed to model context.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model: Option<Vec<Message>>,
    /// JSON payload consumed by views, extensions, or bookkeeping logic.
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "present"
    )]
    pub data: Option<JsonValue>,
    /// `"self"` starts active context at the newly assigned entry ID.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub head: Option<EntryHead>,
    /// Context-only overrides of earlier visible entries.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub edits: Option<Vec<ContextEdit>>,
}

impl EntryDraft {
    /// A draft of `kind` with no other content.
    #[must_use]
    pub fn new(kind: impl Into<String>) -> Self {
        Self {
            kind: kind.into(),
            model: None,
            data: None,
            head: None,
            edits: None,
        }
    }
}

/// The data type of a typed entry kind ([`crate::entries::Entry`]): a JSON
/// value type, or [`NoData`] for kinds that carry none (TS `never`).
pub trait EntryData: Sized {
    /// Read the data of an entry already narrowed by kind. TS narrows with a
    /// cast; Rust decodes, so malformed data is an error.
    ///
    /// # Errors
    /// The stored data does not decode as `Self`.
    fn decode(data: Option<&JsonValue>) -> Result<Self, JsonError>;

    /// The `data` field of a draft; `None` omits it.
    ///
    /// # Errors
    /// The value is not strict JSON.
    fn encode(&self) -> Result<Option<JsonValue>, JsonError>;
}

/// Data of an entry kind that carries none (TS `Entry<never>`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct NoData;

impl EntryData for NoData {
    fn decode(_data: Option<&JsonValue>) -> Result<Self, JsonError> {
        Ok(Self)
    }

    fn encode(&self) -> Result<Option<JsonValue>, JsonError> {
        Ok(None)
    }
}

impl<T: Serialize + DeserializeOwned> EntryData for T {
    fn decode(data: Option<&JsonValue>) -> Result<Self, JsonError> {
        from_json(data.unwrap_or(&JsonValue::Null))
    }

    fn encode(&self) -> Result<Option<JsonValue>, JsonError> {
        to_json(self).map(Some)
    }
}

/// Entry whose `data` has type `D`. Dereferences to the complete record.
#[derive(Debug, Clone, PartialEq)]
pub struct TypedEntry<D> {
    entry: EntryRecord,
    data: D,
}

impl<D> TypedEntry<D> {
    /// Pair a record with its decoded data. The caller guarantees the record
    /// has the kind whose data `data` is.
    #[must_use]
    pub fn new(entry: EntryRecord, data: D) -> Self {
        Self { entry, data }
    }

    /// The typed data.
    #[must_use]
    pub fn data(&self) -> &D {
        &self.data
    }

    /// The complete record.
    #[must_use]
    pub fn entry(&self) -> &EntryRecord {
        &self.entry
    }

    /// The complete record, dropping the typed data.
    #[must_use]
    pub fn into_entry(self) -> EntryRecord {
        self.entry
    }
}

impl<D> Deref for TypedEntry<D> {
    type Target = EntryRecord;

    fn deref(&self) -> &EntryRecord {
        &self.entry
    }
}

/// Entry content of a typed kind; the token supplies `kind`.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct TypedEntryDraft<D> {
    /// Messages contributed to model context.
    pub model: Option<Vec<Message>>,
    /// The typed data; [`NoData`] for kinds without data.
    pub data: D,
    /// `"self"` starts active context at the newly assigned entry ID.
    pub head: Option<EntryHead>,
    /// Context-only overrides of earlier visible entries.
    pub edits: Option<Vec<ContextEdit>>,
}
