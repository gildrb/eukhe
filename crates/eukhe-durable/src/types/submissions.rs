//! Submission records (`types.ts`, spec §2, §6).

use eukhe_chord::json::JsonValue;
use serde::ser::SerializeStruct;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::ids::{ConversationId, EntryId, SubmissionId};
use super::json_serde::{forbidden, present, required};

/// Whether a submission is user input or a passive entry write.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum SubmissionType {
    /// User input that may start a run.
    Input,
    /// A passive entry write.
    Write,
}

/// Lifecycle status of a submission (TS `SubmissionRecord["status"]`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum SubmissionStatus {
    /// Admitted but not yet represented in the transcript.
    Queued,
    /// Added to the transcript and owned by an active run (inputs only).
    Placed,
    /// Answered input or appended write.
    Done,
    /// Terminal without an answer.
    Unanswered,
}

/// Lifecycle of an admitted user input.
#[derive(Debug, Clone, PartialEq)]
pub enum InputSubmission {
    /// Admitted but not yet represented in the transcript.
    Queued,
    /// Added to the transcript and owned by an active run.
    Placed {
        /// The user entry.
        entry: EntryId,
    },
    /// Successfully answered user input.
    Done {
        /// The user entry.
        entry: EntryId,
        /// The answer entry.
        answer: EntryId,
    },
    /// Terminal input that can no longer receive an answer.
    Unanswered {
        /// The user entry, when the input was placed.
        entry: Option<EntryId>,
        /// Why no answer came.
        reason: String,
        /// Optional diagnostic data.
        detail: Option<JsonValue>,
    },
}

/// Lifecycle of an admitted passive entry write.
#[derive(Debug, Clone, PartialEq)]
pub enum WriteSubmission {
    /// Admitted but not yet appended to the transcript.
    Queued,
    /// Successfully appended passive entry.
    Done {
        /// The appended entry.
        entry: EntryId,
    },
    /// Terminal passive write that could not be placed.
    Unanswered {
        /// Why it was not placed.
        reason: String,
        /// Optional diagnostic data.
        detail: Option<JsonValue>,
    },
}

/// The type and status-dependent fields of a submission.
#[derive(Debug, Clone, PartialEq)]
pub enum SubmissionState {
    /// `type: "input"`.
    Input(InputSubmission),
    /// `type: "write"`.
    Write(WriteSubmission),
}

impl SubmissionState {
    /// The submission type.
    #[must_use]
    pub fn submission_type(&self) -> SubmissionType {
        match self {
            Self::Input(_) => SubmissionType::Input,
            Self::Write(_) => SubmissionType::Write,
        }
    }

    /// The lifecycle status.
    #[must_use]
    pub fn status(&self) -> SubmissionStatus {
        match self {
            Self::Input(InputSubmission::Queued) | Self::Write(WriteSubmission::Queued) => {
                SubmissionStatus::Queued
            }
            Self::Input(InputSubmission::Placed { .. }) => SubmissionStatus::Placed,
            Self::Input(InputSubmission::Done { .. })
            | Self::Write(WriteSubmission::Done { .. }) => SubmissionStatus::Done,
            Self::Input(InputSubmission::Unanswered { .. })
            | Self::Write(WriteSubmission::Unanswered { .. }) => SubmissionStatus::Unanswered,
        }
    }

    /// The transcript entry the submission is represented by, if any.
    #[must_use]
    pub fn entry(&self) -> Option<EntryId> {
        match self {
            Self::Input(
                InputSubmission::Placed { entry } | InputSubmission::Done { entry, .. },
            )
            | Self::Write(WriteSubmission::Done { entry }) => Some(*entry),
            Self::Input(InputSubmission::Unanswered { entry, .. }) => *entry,
            Self::Input(InputSubmission::Queued)
            | Self::Write(WriteSubmission::Queued | WriteSubmission::Unanswered { .. }) => None,
        }
    }

    /// The answer entry of a done input.
    #[must_use]
    pub fn answer(&self) -> Option<EntryId> {
        match self {
            Self::Input(InputSubmission::Done { answer, .. }) => Some(*answer),
            Self::Input(_) | Self::Write(_) => None,
        }
    }

    /// The reason of an unanswered submission.
    #[must_use]
    pub fn reason(&self) -> Option<&str> {
        match self {
            Self::Input(InputSubmission::Unanswered { reason, .. })
            | Self::Write(WriteSubmission::Unanswered { reason, .. }) => Some(reason),
            Self::Input(_) | Self::Write(_) => None,
        }
    }

    /// The detail of an unanswered submission.
    #[must_use]
    pub fn detail(&self) -> Option<&JsonValue> {
        match self {
            Self::Input(InputSubmission::Unanswered { detail, .. })
            | Self::Write(WriteSubmission::Unanswered { detail, .. }) => detail.as_ref(),
            Self::Input(_) | Self::Write(_) => None,
        }
    }

    /// Whether the submission is settled (`done` or `unanswered`).
    #[must_use]
    pub fn is_settled(&self) -> bool {
        matches!(
            self.status(),
            SubmissionStatus::Done | SubmissionStatus::Unanswered
        )
    }
}

/// Durable lifecycle of one admitted user input or passive entry write.
///
/// Fields serialize in the order the TS Session writes them:
/// `{ ...create, id }` and later settlement fields appended.
#[derive(Debug, Clone, PartialEq)]
pub struct SubmissionRecord {
    /// The submission's ID.
    pub id: SubmissionId,
    /// The conversation it was admitted to.
    pub conversation_id: ConversationId,
    /// Host-provided deduplication key, scoped to the conversation.
    pub request_id: Option<String>,
    /// Type and status-dependent fields.
    pub state: SubmissionState,
}

impl SubmissionRecord {
    /// The record a create value becomes once the Session assigns `id`.
    #[must_use]
    pub fn from_create(create: SubmissionCreate, id: SubmissionId) -> Self {
        Self {
            id,
            conversation_id: create.conversation_id,
            request_id: create.request_id,
            state: create.state,
        }
    }
}

/// Submission fields supplied before the Session assigns an ID.
#[derive(Debug, Clone, PartialEq)]
pub struct SubmissionCreate {
    /// The conversation to admit to.
    pub conversation_id: ConversationId,
    /// Host-provided deduplication key, scoped to the conversation.
    pub request_id: Option<String>,
    /// Type and status-dependent fields.
    pub state: SubmissionState,
}

/// Terminal status staged for a submission; identity, type, and entry come
/// from its current record.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "camelCase")]
pub enum SubmissionSettlement {
    /// Answered by `answer`.
    Done {
        /// The answer entry.
        answer: EntryId,
    },
    /// Settled without an answer.
    Unanswered {
        /// Why no answer came.
        reason: String,
        /// Optional diagnostic data.
        #[serde(
            default,
            skip_serializing_if = "Option::is_none",
            deserialize_with = "present"
        )]
        detail: Option<JsonValue>,
    },
}

fn serialize_submission<S: Serializer>(
    serializer: S,
    name: &'static str,
    id: Option<SubmissionId>,
    conversation_id: ConversationId,
    request_id: Option<&String>,
    state: &SubmissionState,
) -> Result<S::Ok, S::Error> {
    let entry = state.entry();
    let reason = state.reason();
    let detail = state.detail();
    let answer = state.answer();
    // `{ conversationId, requestId?, type, status, entry?, reason?, detail?, id }`, then a settled `answer`.
    let mut out = serializer.serialize_struct(name, 9)?;
    out.serialize_field("conversationId", &conversation_id)?;
    if let Some(request_id) = request_id {
        out.serialize_field("requestId", request_id)?;
    }
    out.serialize_field("type", &state.submission_type())?;
    out.serialize_field("status", &state.status())?;
    if let Some(entry) = entry {
        out.serialize_field("entry", &entry)?;
    }
    if let Some(reason) = reason {
        out.serialize_field("reason", reason)?;
    }
    if let Some(detail) = detail {
        out.serialize_field("detail", detail)?;
    }
    if let Some(id) = id {
        out.serialize_field("id", &id)?;
    }
    if let Some(answer) = answer {
        out.serialize_field("answer", &answer)?;
    }
    out.end()
}

impl Serialize for SubmissionRecord {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serialize_submission(
            serializer,
            "SubmissionRecord",
            Some(self.id),
            self.conversation_id,
            self.request_id.as_ref(),
            &self.state,
        )
    }
}

impl Serialize for SubmissionCreate {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serialize_submission(
            serializer,
            "SubmissionCreate",
            None,
            self.conversation_id,
            self.request_id.as_ref(),
            &self.state,
        )
    }
}

/// Flat JSON shape of every submission union member.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct SubmissionWire {
    #[serde(default)]
    id: Option<SubmissionId>,
    conversation_id: ConversationId,
    #[serde(default)]
    request_id: Option<String>,
    #[serde(rename = "type")]
    submission_type: SubmissionType,
    status: SubmissionStatus,
    #[serde(default)]
    entry: Option<EntryId>,
    #[serde(default)]
    answer: Option<EntryId>,
    #[serde(default)]
    reason: Option<String>,
    #[serde(default, deserialize_with = "present")]
    detail: Option<JsonValue>,
}

impl SubmissionWire {
    /// The union member these fields select, rejecting fields it forbids.
    fn state<E: serde::de::Error>(self) -> Result<SubmissionState, E> {
        let Self {
            submission_type,
            status,
            entry,
            answer,
            reason,
            detail,
            ..
        } = self;
        let member = match (submission_type, status) {
            (SubmissionType::Input, SubmissionStatus::Queued) => "a queued input submission",
            (SubmissionType::Input, SubmissionStatus::Placed) => "a placed input submission",
            (SubmissionType::Input, SubmissionStatus::Done) => "a done input submission",
            (SubmissionType::Input, SubmissionStatus::Unanswered) => {
                "an unanswered input submission"
            }
            (SubmissionType::Write, SubmissionStatus::Queued) => "a queued write submission",
            (SubmissionType::Write, SubmissionStatus::Placed) => "a write submission",
            (SubmissionType::Write, SubmissionStatus::Done) => "a done write submission",
            (SubmissionType::Write, SubmissionStatus::Unanswered) => {
                "an unanswered write submission"
            }
        };
        let settled_fields =
            |reason: Option<&String>, detail: Option<&JsonValue>| -> Result<(), E> {
                forbidden(reason, "reason", member)?;
                forbidden(detail, "detail", member)
            };
        Ok(match (submission_type, status) {
            (SubmissionType::Input, SubmissionStatus::Queued) => {
                forbidden(entry.as_ref(), "entry", member)?;
                forbidden(answer.as_ref(), "answer", member)?;
                settled_fields(reason.as_ref(), detail.as_ref())?;
                SubmissionState::Input(InputSubmission::Queued)
            }
            (SubmissionType::Input, SubmissionStatus::Placed) => {
                forbidden(answer.as_ref(), "answer", member)?;
                settled_fields(reason.as_ref(), detail.as_ref())?;
                SubmissionState::Input(InputSubmission::Placed {
                    entry: required(entry, "entry", member)?,
                })
            }
            (SubmissionType::Input, SubmissionStatus::Done) => {
                settled_fields(reason.as_ref(), detail.as_ref())?;
                SubmissionState::Input(InputSubmission::Done {
                    entry: required(entry, "entry", member)?,
                    answer: required(answer, "answer", member)?,
                })
            }
            (SubmissionType::Input, SubmissionStatus::Unanswered) => {
                forbidden(answer.as_ref(), "answer", member)?;
                SubmissionState::Input(InputSubmission::Unanswered {
                    entry,
                    reason: required(reason, "reason", member)?,
                    detail,
                })
            }
            (SubmissionType::Write, SubmissionStatus::Queued) => {
                forbidden(entry.as_ref(), "entry", member)?;
                forbidden(answer.as_ref(), "answer", member)?;
                settled_fields(reason.as_ref(), detail.as_ref())?;
                SubmissionState::Write(WriteSubmission::Queued)
            }
            (SubmissionType::Write, SubmissionStatus::Placed) => {
                return Err(E::custom("a write submission cannot be placed"));
            }
            (SubmissionType::Write, SubmissionStatus::Done) => {
                forbidden(answer.as_ref(), "answer", member)?;
                settled_fields(reason.as_ref(), detail.as_ref())?;
                SubmissionState::Write(WriteSubmission::Done {
                    entry: required(entry, "entry", member)?,
                })
            }
            (SubmissionType::Write, SubmissionStatus::Unanswered) => {
                forbidden(entry.as_ref(), "entry", member)?;
                forbidden(answer.as_ref(), "answer", member)?;
                SubmissionState::Write(WriteSubmission::Unanswered {
                    reason: required(reason, "reason", member)?,
                    detail,
                })
            }
        })
    }
}

impl<'de> Deserialize<'de> for SubmissionRecord {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let mut wire = SubmissionWire::deserialize(deserializer)?;
        let id = required(wire.id.take(), "id", "a submission record")?;
        let conversation_id = wire.conversation_id;
        let request_id = wire.request_id.take();
        Ok(Self {
            id,
            conversation_id,
            request_id,
            state: wire.state()?,
        })
    }
}

impl<'de> Deserialize<'de> for SubmissionCreate {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let mut wire = SubmissionWire::deserialize(deserializer)?;
        forbidden(wire.id.as_ref(), "id", "a submission create value")?;
        let conversation_id = wire.conversation_id;
        let request_id = wire.request_id.take();
        Ok(Self {
            conversation_id,
            request_id,
            state: wire.state()?,
        })
    }
}
