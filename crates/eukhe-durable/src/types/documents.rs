//! Document semantics, records, addresses, and content (`types.ts`, spec §3, §10).

use std::fmt;
use std::sync::Arc;

use eukhe_chord::delta::Op;
use eukhe_chord::json::{JsonObject, JsonValue};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::ids::{ConversationId, DocumentId, Seq, TaskId};
use super::json_serde::{forbidden, into_object, object, required, ObjectRef};

/// How much history a conversation document retains.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum DocumentHistory {
    /// Retain only current state.
    Latest,
    /// Retain history needed for as-of reads.
    Rewindable,
}

/// How a conversation fork initializes a conversation document.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum DocumentFork {
    /// From the source state at the fork's cutoff (rewindable documents only).
    AsOf,
    /// From the source's current state.
    Current,
    /// From the definition's initial value.
    Initial,
}

/// Fork behavior a latest-only conversation document may declare.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LatestFork {
    /// From the source's current state.
    Current,
    /// From the definition's initial value.
    Initial,
}

/// Fork behavior a rewindable conversation document may declare.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RewindableFork {
    /// From the source state at the fork's cutoff.
    AsOf,
    /// From the source's current state.
    Current,
    /// From the definition's initial value.
    Initial,
}

impl From<LatestFork> for DocumentFork {
    fn from(fork: LatestFork) -> Self {
        match fork {
            LatestFork::Current => Self::Current,
            LatestFork::Initial => Self::Initial,
        }
    }
}

impl From<RewindableFork> for DocumentFork {
    fn from(fork: RewindableFork) -> Self {
        match fork {
            RewindableFork::AsOf => Self::AsOf,
            RewindableFork::Current => Self::Current,
            RewindableFork::Initial => Self::Initial,
        }
    }
}

/// History and fork behavior of a conversation document (TS
/// `LatestConversationSemantics | RewindableConversationSemantics`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConversationSemantics {
    /// Retains only current state.
    Latest(LatestFork),
    /// History remains addressable for as-of reads.
    Rewindable(RewindableFork),
}

impl ConversationSemantics {
    /// The retained history.
    #[must_use]
    pub fn history(self) -> DocumentHistory {
        match self {
            Self::Latest(_) => DocumentHistory::Latest,
            Self::Rewindable(_) => DocumentHistory::Rewindable,
        }
    }

    /// The fork behavior.
    #[must_use]
    pub fn fork(self) -> DocumentFork {
        match self {
            Self::Latest(fork) => fork.into(),
            Self::Rewindable(fork) => fork.into(),
        }
    }

    /// The semantics with `history` and `fork`; `None` for `latest` with `asOf`.
    #[must_use]
    pub fn from_parts(history: DocumentHistory, fork: DocumentFork) -> Option<Self> {
        Some(match (history, fork) {
            (DocumentHistory::Latest, DocumentFork::AsOf) => return None,
            (DocumentHistory::Latest, DocumentFork::Current) => Self::Latest(LatestFork::Current),
            (DocumentHistory::Latest, DocumentFork::Initial) => Self::Latest(LatestFork::Initial),
            (DocumentHistory::Rewindable, DocumentFork::AsOf) => {
                Self::Rewindable(RewindableFork::AsOf)
            }
            (DocumentHistory::Rewindable, DocumentFork::Current) => {
                Self::Rewindable(RewindableFork::Current)
            }
            (DocumentHistory::Rewindable, DocumentFork::Initial) => {
                Self::Rewindable(RewindableFork::Initial)
            }
        })
    }
}

/// Ownership and lifetime of a document; only conversation documents declare
/// history and fork behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DocumentSemantics {
    /// Current-only, owned by the Session.
    Session,
    /// Owned by a conversation.
    Conversation(ConversationSemantics),
    /// Current-only, owned by a task and retired when it becomes terminal.
    Task,
}

impl DocumentSemantics {
    /// The scope kind name: `"session"`, `"conversation"`, or `"task"`.
    #[must_use]
    pub fn scope_name(self) -> &'static str {
        match self {
            Self::Session => "session",
            Self::Conversation(_) => "conversation",
            Self::Task => "task",
        }
    }
}

/// Stored replay state supplied to a document's checkpoint predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CheckpointInfo {
    /// Deltas already stored after the newest base, excluding the change being evaluated.
    pub deltas_since_base: u64,
}

/// The exact scope of a document (TS `DocumentRecord["scope"]`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "camelCase",
    rename_all_fields = "camelCase"
)]
pub enum DocumentScope {
    /// The Session.
    Session,
    /// One conversation.
    Conversation {
        /// The owning conversation.
        conversation_id: ConversationId,
    },
    /// One task.
    Task {
        /// The owning task.
        task_id: TaskId,
    },
}

impl DocumentScope {
    /// The scope kind name: `"session"`, `"conversation"`, or `"task"`.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Session => "session",
            Self::Conversation { .. } => "conversation",
            Self::Task { .. } => "task",
        }
    }
}

/// Scope plus, for conversation documents, the persisted history and fork
/// policy of a document record.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DocumentRecordScope {
    /// `scope: { kind: "session" }`.
    Session,
    /// `scope: { kind: "conversation", conversationId }` with `history` and `fork`.
    Conversation {
        /// The owning conversation.
        conversation_id: ConversationId,
        /// The persisted history and fork policy.
        semantics: ConversationSemantics,
    },
    /// `scope: { kind: "task", taskId }`.
    Task {
        /// The owning task.
        task_id: TaskId,
    },
}

impl DocumentRecordScope {
    /// The scope without lifetime semantics.
    #[must_use]
    pub fn scope(self) -> DocumentScope {
        match self {
            Self::Session => DocumentScope::Session,
            Self::Conversation {
                conversation_id, ..
            } => DocumentScope::Conversation { conversation_id },
            Self::Task { task_id } => DocumentScope::Task { task_id },
        }
    }

    /// The persisted semantics.
    #[must_use]
    pub fn semantics(self) -> DocumentSemantics {
        match self {
            Self::Session => DocumentSemantics::Session,
            Self::Conversation { semantics, .. } => DocumentSemantics::Conversation(semantics),
            Self::Task { .. } => DocumentSemantics::Task,
        }
    }

    /// The persisted history of a conversation document.
    #[must_use]
    pub fn history(self) -> Option<DocumentHistory> {
        match self {
            Self::Conversation { semantics, .. } => Some(semantics.history()),
            Self::Session | Self::Task { .. } => None,
        }
    }

    /// The persisted fork policy of a conversation document.
    #[must_use]
    pub fn fork(self) -> Option<DocumentFork> {
        match self {
            Self::Conversation { semantics, .. } => Some(semantics.fork()),
            Self::Session | Self::Task { .. } => None,
        }
    }
}

/// Fields supplied when storage creates and stamps a new [`DocumentRecord`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DocumentCreate {
    /// Unique incarnation ID; never reused when the same logical document is recreated.
    pub id: DocumentId,
    /// Stable document definition kind.
    pub kind: String,
    /// Family member key; absent for singleton documents.
    pub key: Option<String>,
    /// Scope and conversation lifetime semantics.
    pub scope: DocumentRecordScope,
}

/// Persisted lifecycle record for one create-to-retire document incarnation.
/// Membership is the half-open interval `createdAt <= at < retiredAt`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DocumentRecord {
    /// Unique incarnation ID; never reused when the same logical document is recreated.
    pub id: DocumentId,
    /// Stable document definition kind.
    pub kind: String,
    /// Family member key; absent for singleton documents.
    pub key: Option<String>,
    /// Scope and conversation lifetime semantics.
    pub scope: DocumentRecordScope,
    /// Commit that created the incarnation, stamped by storage.
    pub created_at: Seq,
    /// Commit that retired the incarnation; absent while it is current.
    pub retired_at: Option<Seq>,
}

impl DocumentRecord {
    /// Stamp a create value with the creating commit (`{ ...create, createdAt }`).
    #[must_use]
    pub fn from_create(create: DocumentCreate, created_at: Seq) -> Self {
        Self {
            id: create.id,
            kind: create.kind,
            key: create.key,
            scope: create.scope,
            created_at,
            retired_at: None,
        }
    }

    /// The create value of this record, without lifetime fields.
    #[must_use]
    pub fn to_create(&self) -> DocumentCreate {
        DocumentCreate {
            id: self.id,
            kind: self.kind.clone(),
            key: self.key.clone(),
            scope: self.scope,
        }
    }
}

/// Identity and scope shared by [`DocumentCreate`] and [`DocumentRecord`]
/// (TS functions accepting `DocumentCreate | DocumentRecord`).
pub trait DocumentIdentity {
    /// The incarnation ID.
    fn id(&self) -> DocumentId;
    /// The definition kind.
    fn kind(&self) -> &str;
    /// The family key, if any.
    fn key(&self) -> Option<&str>;
    /// The scope and lifetime semantics.
    fn record_scope(&self) -> DocumentRecordScope;
}

impl DocumentIdentity for DocumentCreate {
    fn id(&self) -> DocumentId {
        self.id
    }

    fn kind(&self) -> &str {
        &self.kind
    }

    fn key(&self) -> Option<&str> {
        self.key.as_deref()
    }

    fn record_scope(&self) -> DocumentRecordScope {
        self.scope
    }
}

impl DocumentIdentity for DocumentRecord {
    fn id(&self) -> DocumentId {
        self.id
    }

    fn kind(&self) -> &str {
        &self.kind
    }

    fn key(&self) -> Option<&str> {
        self.key.as_deref()
    }

    fn record_scope(&self) -> DocumentRecordScope {
        self.scope
    }
}

fn serialize_document<S: Serializer>(
    serializer: S,
    name: &'static str,
    identity: &impl DocumentIdentity,
    lifetime: Option<(Seq, Option<Seq>)>,
) -> Result<S::Ok, S::Error> {
    // `{ id, kind, key?, scope, history?, fork? }`, then storage's `createdAt` and `retiredAt?`.
    let scope = identity.record_scope();
    let mut out = serializer.serialize_struct(name, 8)?;
    out.serialize_field("id", &identity.id())?;
    out.serialize_field("kind", identity.kind())?;
    if let Some(key) = identity.key() {
        out.serialize_field("key", key)?;
    }
    out.serialize_field("scope", &scope.scope())?;
    if let DocumentRecordScope::Conversation { semantics, .. } = scope {
        out.serialize_field("history", &semantics.history())?;
        out.serialize_field("fork", &semantics.fork())?;
    }
    if let Some((created_at, retired_at)) = lifetime {
        out.serialize_field("createdAt", &created_at)?;
        if let Some(retired_at) = retired_at {
            out.serialize_field("retiredAt", &retired_at)?;
        }
    }
    out.end()
}

impl Serialize for DocumentCreate {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serialize_document(serializer, "DocumentCreate", self, None)
    }
}

impl Serialize for DocumentRecord {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serialize_document(
            serializer,
            "DocumentRecord",
            self,
            Some((self.created_at, self.retired_at)),
        )
    }
}

/// Flat JSON shape of every document record union member.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct DocumentWire {
    id: DocumentId,
    kind: String,
    #[serde(default)]
    key: Option<String>,
    scope: DocumentScope,
    #[serde(default)]
    history: Option<DocumentHistory>,
    #[serde(default)]
    fork: Option<DocumentFork>,
    #[serde(default)]
    created_at: Option<Seq>,
    #[serde(default)]
    retired_at: Option<Seq>,
}

impl DocumentWire {
    fn record_scope<E: serde::de::Error>(&self) -> Result<DocumentRecordScope, E> {
        match self.scope {
            DocumentScope::Session => {
                forbidden(self.history.as_ref(), "history", "a session document")?;
                forbidden(self.fork.as_ref(), "fork", "a session document")?;
                Ok(DocumentRecordScope::Session)
            }
            DocumentScope::Task { task_id } => {
                forbidden(self.history.as_ref(), "history", "a task document")?;
                forbidden(self.fork.as_ref(), "fork", "a task document")?;
                Ok(DocumentRecordScope::Task { task_id })
            }
            DocumentScope::Conversation { conversation_id } => {
                let history = required(self.history, "history", "a conversation document")?;
                let fork = required(self.fork, "fork", "a conversation document")?;
                let semantics = ConversationSemantics::from_parts(history, fork)
                    .ok_or_else(|| E::custom("a latest conversation document cannot fork asOf"))?;
                Ok(DocumentRecordScope::Conversation {
                    conversation_id,
                    semantics,
                })
            }
        }
    }
}

impl<'de> Deserialize<'de> for DocumentCreate {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire = DocumentWire::deserialize(deserializer)?;
        forbidden(
            wire.created_at.as_ref(),
            "createdAt",
            "a document create value",
        )?;
        forbidden(
            wire.retired_at.as_ref(),
            "retiredAt",
            "a document create value",
        )?;
        let scope = wire.record_scope()?;
        Ok(Self {
            id: wire.id,
            kind: wire.kind,
            key: wire.key,
            scope,
        })
    }
}

impl<'de> Deserialize<'de> for DocumentRecord {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let wire = DocumentWire::deserialize(deserializer)?;
        let scope = wire.record_scope()?;
        let created_at = required(wire.created_at, "createdAt", "a document record")?;
        Ok(Self {
            id: wire.id,
            kind: wire.kind,
            key: wire.key,
            scope,
            created_at,
            retired_at: wire.retired_at,
        })
    }
}

/// Current state or one historical commit sequence used for document
/// membership and content reads (TS `Seq | "current"`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DocumentPoint {
    /// `"current"`.
    Current,
    /// The state as of one commit sequence.
    At(Seq),
}

impl Serialize for DocumentPoint {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Current => serializer.serialize_str("current"),
            Self::At(seq) => seq.serialize(serializer),
        }
    }
}

impl<'de> Deserialize<'de> for DocumentPoint {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match JsonValue::deserialize(deserializer)? {
            JsonValue::String(text) if &*text == "current" => Ok(Self::Current),
            JsonValue::Number(number) => number
                .as_u64()
                .map(|value| Self::At(Seq::from_number(value)))
                .ok_or_else(|| {
                    serde::de::Error::custom(format!("invalid document point {number}"))
                }),
            other => Err(serde::de::Error::custom(format!(
                "invalid document point {other}"
            ))),
        }
    }
}

impl fmt::Display for DocumentPoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Current => f.write_str("current"),
            Self::At(seq) => fmt::Display::fmt(seq, f),
        }
    }
}

/// Exact logical identity of a singleton or one keyed family member.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DocumentAddress {
    /// The definition kind.
    pub kind: String,
    /// The exact scope.
    pub scope: DocumentScope,
    /// Absent selects the singleton; present selects one family member.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub key: Option<String>,
}

/// Complete base value of a document at one definition version; serializes
/// as the content `{ version, kind: "base", value }`, the only content a
/// `document.create` write carries.
#[derive(Debug, Clone, PartialEq)]
pub struct DocumentBase {
    /// Definition version of `value`.
    pub version: u64,
    /// The complete value.
    pub value: Arc<JsonObject>,
}

/// Chord operation batch applied to the previous revision at one definition version.
#[derive(Debug, Clone, PartialEq)]
pub struct DocumentDelta {
    /// Definition version of the result; equals the previous revision's version.
    pub version: u64,
    /// The operations, shared with the commit publication.
    pub ops: Arc<[Op]>,
}

/// Complete checkpoint or Chord operation batch selected by the owning Session.
#[derive(Debug, Clone, PartialEq)]
pub enum DocumentContent {
    /// `{ version, kind: "base", value }`.
    Base(DocumentBase),
    /// `{ version, kind: "delta", ops }`.
    Delta(DocumentDelta),
}

impl DocumentContent {
    /// The definition version.
    #[must_use]
    pub fn version(&self) -> u64 {
        match self {
            Self::Base(base) => base.version,
            Self::Delta(delta) => delta.version,
        }
    }
}

impl Serialize for DocumentBase {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut out = serializer.serialize_struct("DocumentContent", 3)?;
        out.serialize_field("version", &self.version)?;
        out.serialize_field("kind", "base")?;
        out.serialize_field("value", &ObjectRef(&self.value))?;
        out.end()
    }
}

impl Serialize for DocumentContent {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Base(base) => base.serialize(serializer),
            Self::Delta(delta) => {
                let mut out = serializer.serialize_struct("DocumentContent", 3)?;
                out.serialize_field("version", &delta.version)?;
                out.serialize_field("kind", "delta")?;
                out.serialize_field("ops", &*delta.ops)?;
                out.end()
            }
        }
    }
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
enum ContentKind {
    Base,
    Delta,
}

#[derive(Deserialize)]
struct ContentWire {
    version: u64,
    kind: ContentKind,
    #[serde(default)]
    value: Option<JsonValue>,
    #[serde(default)]
    ops: Option<Vec<Op>>,
}

impl ContentWire {
    fn content<E: serde::de::Error>(self) -> Result<DocumentContent, E> {
        match self.kind {
            ContentKind::Base => {
                forbidden(self.ops.as_ref(), "ops", "a document base")?;
                let value = into_object(required(self.value, "value", "a document base")?)?;
                Ok(DocumentContent::Base(DocumentBase {
                    version: self.version,
                    value,
                }))
            }
            ContentKind::Delta => {
                forbidden(self.value.as_ref(), "value", "a document delta")?;
                let ops = required(self.ops, "ops", "a document delta")?;
                Ok(DocumentContent::Delta(DocumentDelta {
                    version: self.version,
                    ops: Arc::from(ops),
                }))
            }
        }
    }
}

impl<'de> Deserialize<'de> for DocumentContent {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        ContentWire::deserialize(deserializer)?.content()
    }
}

impl<'de> Deserialize<'de> for DocumentBase {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        match ContentWire::deserialize(deserializer)?.content()? {
            DocumentContent::Base(base) => Ok(base),
            DocumentContent::Delta(_) => Err(serde::de::Error::custom(
                "document creation always starts from a complete base",
            )),
        }
    }
}

/// Exact persisted source selected for a definition-free document copy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DocumentCopySource {
    /// The source incarnation.
    pub id: DocumentId,
    /// The source point.
    pub at: DocumentPoint,
}

/// Detached materialized value and stored definition version at a selected point.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StoredDocument {
    /// The incarnation's record.
    pub record: DocumentRecord,
    /// Stored definition version of `value`.
    pub version: u64,
    /// The materialized value.
    #[serde(with = "object")]
    pub value: Arc<JsonObject>,
    /// Deltas replayed after the selected base to materialize `value`.
    pub deltas_since_base: u64,
}
