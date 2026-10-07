//! Typed entry kinds and the built-in entry tokens (`entries.ts`, spec §8.1).

use std::fmt;
use std::marker::PhantomData;

use eukhe_chord::json::JsonError;
use serde::{Deserialize, Serialize};

use crate::harness::types::{CompactionReason, ToolDiagnostic};
use crate::types::{EntryData, EntryDraft, EntryRecord, NoData, TypedEntry, TypedEntryDraft};

/// Typed entry kind with a narrowing guard (TS `Entry<D>`). `D` is the type
/// of `data`; [`NoData`] (TS `never`) means the kind carries no data.
pub struct Entry<D = NoData> {
    kind: &'static str,
    data: PhantomData<fn() -> D>,
}

/// An entry kind that is not a non-empty string (TS `TypeError`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("Entry kind must be a non-empty string")]
pub struct EntryKindError;

impl<D> Entry<D> {
    /// Define a typed entry kind whose [`Entry::is`] guard narrows by
    /// `EntryRecord.kind` (TS `defineEntry`).
    ///
    /// # Errors
    /// `kind` is empty.
    pub const fn define(kind: &'static str) -> Result<Self, EntryKindError> {
        if kind.is_empty() {
            return Err(EntryKindError);
        }
        Ok(Self {
            kind,
            data: PhantomData,
        })
    }

    /// A built-in kind, known to be non-empty.
    const fn builtin(kind: &'static str) -> Self {
        Self {
            kind,
            data: PhantomData,
        }
    }

    /// The entry kind.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        self.kind
    }

    /// Whether `entry` is present and has this kind.
    #[must_use]
    pub fn is(&self, entry: Option<&EntryRecord>) -> bool {
        entry.is_some_and(|entry| entry.kind == self.kind)
    }
}

impl<D: EntryData> Entry<D> {
    /// Narrow `entry` to this kind, decoding its data; `None` when it has
    /// another kind.
    ///
    /// # Errors
    /// The entry has this kind but its data does not decode as `D`.
    pub fn narrow(&self, entry: EntryRecord) -> Result<Option<TypedEntry<D>>, JsonError> {
        if entry.kind != self.kind {
            return Ok(None);
        }
        let data = D::decode(entry.data.as_ref())?;
        Ok(Some(TypedEntry::new(entry, data)))
    }

    /// The untyped draft of `draft`; the token supplies `kind`.
    ///
    /// # Errors
    /// The data is not strict JSON.
    pub fn draft(&self, draft: &TypedEntryDraft<D>) -> Result<EntryDraft, JsonError> {
        Ok(EntryDraft {
            kind: self.kind.to_owned(),
            model: draft.model.clone(),
            data: draft.data.encode()?,
            head: draft.head,
            edits: draft.edits.clone(),
        })
    }
}

/// Define a typed entry kind (TS `defineEntry<D>(kind)`).
///
/// # Errors
/// `kind` is empty.
pub const fn define_entry<D>(kind: &'static str) -> Result<Entry<D>, EntryKindError> {
    Entry::define(kind)
}

impl<D> Clone for Entry<D> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<D> Copy for Entry<D> {}

impl<D> fmt::Debug for Entry<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Entry").field("kind", &self.kind).finish()
    }
}

/// Data of a [`TOOL_RESULT_ENTRY`]: the structured diagnostics, possibly none.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ToolResultData {
    /// The diagnostics rendered at the end of the result content.
    pub diagnostics: Vec<ToolDiagnostic>,
}

/// Data of a [`COMPACTION_ENTRY`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactionData {
    /// Why the compaction ran.
    pub reason: CompactionReason,
}

/// User input: `model` is `[UserMessage]`. Written by submissions.
pub static USER_ENTRY: Entry = Entry::builtin("pi.user");

/// Provider result with any stop reason: `model` is `[AssistantMessage]`.
/// Written by generation.
pub static ASSISTANT_ENTRY: Entry = Entry::builtin("pi.assistant");

/// Positional prompt and tool change: `model` is `[SystemMessage]` with empty `content`.
pub static SYSTEM_ENTRY: Entry = Entry::builtin("pi.system");

/// Tool result: `model` is `[ToolResultMessage]`, whose content ends with the
/// rendered diagnostics block; `data` holds the structured diagnostics,
/// possibly none. Written by tool tasks, and by generation for calls it did
/// not offer.
pub static TOOL_RESULT_ENTRY: Entry<ToolResultData> = Entry::builtin("pi.tool-result");

/// Start of a new context: always `head: "self"`, with `model` absent for a
/// plain reset or `[UserMessage]` carrying the handoff text. Written by
/// `Conversation.reset()` and the `handoff` tool control.
pub static RESET_ENTRY: Entry = Entry::builtin("pi.reset");

/// Compaction summary: `model` is `[UserMessage]` with the wrapped summary,
/// `head` the first kept entry. Written by compaction tasks, directly or
/// through a write submission.
pub static COMPACTION_ENTRY: Entry<CompactionData> = Entry::builtin("pi.compaction");

#[cfg(test)]
mod tests {
    //! Typed entry cases of `test/session-definitions.test.ts`; the
    //! `@ts-expect-error` draft cases are `compile_fail` doctests in
    //! `types::compile_checks`.

    use eukhe_chord::json::{to_json, JsonValue};
    use serde::{Deserialize, Serialize};

    use super::*;
    use crate::harness::types::ToolDiagnosticSeverity;
    use crate::types::{ConversationId, EntryHead, EntryId};

    #[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
    struct Note {
        text: String,
    }

    static NOTE: Entry<Note> = match define_entry("t.note") {
        Ok(token) => token,
        Err(_) => panic!("invalid entry kind"),
    };
    static MARKER: Entry = match Entry::define("t.marker") {
        Ok(token) => token,
        Err(_) => panic!("invalid entry kind"),
    };

    fn record(kind: &str, data: Option<JsonValue>) -> EntryRecord {
        EntryRecord {
            model: None,
            data,
            edits: None,
            kind: kind.to_owned(),
            id: EntryId::from_number(3),
            conversation_id: ConversationId::from_number(1),
            head: None,
            by_task_id: None,
        }
    }

    #[test]
    fn rejects_empty_entry_kinds() {
        assert_eq!(
            define_entry::<NoData>("").unwrap_err().to_string(),
            "Entry kind must be a non-empty string"
        );
    }

    #[test]
    fn types_typed_entries() {
        let note = NOTE
            .narrow(record(
                "t.note",
                Some(JsonValue::parse(r#"{"text":"x"}"#).unwrap()),
            ))
            .unwrap()
            .unwrap();
        assert_eq!(note.data().text, "x");
        assert_eq!(note.kind, "t.note");
        assert!(NOTE.narrow(record("t.marker", None)).unwrap().is_none());
        assert!(NOTE.narrow(record("t.note", None)).is_err());
        let marker = MARKER.narrow(record("t.marker", None)).unwrap().unwrap();
        assert_eq!(*marker.data(), NoData);

        assert!(NOTE.is(Some(&record("t.note", None))));
        assert!(!NOTE.is(Some(&record("t.raw", None))));
        assert!(!NOTE.is(None));

        let draft = NOTE
            .draft(&TypedEntryDraft {
                model: None,
                data: Note {
                    text: "x".to_owned(),
                },
                head: None,
                edits: None,
            })
            .unwrap();
        assert_eq!(
            to_json(&draft).unwrap().to_string(),
            r#"{"kind":"t.note","data":{"text":"x"}}"#
        );
        let draft = MARKER
            .draft(&TypedEntryDraft {
                head: Some(EntryHead::SelfEntry),
                ..TypedEntryDraft::default()
            })
            .unwrap();
        assert_eq!(
            to_json(&draft).unwrap().to_string(),
            r#"{"kind":"t.marker","head":"self"}"#
        );
    }

    #[test]
    fn defines_built_in_entries() {
        let kinds = [
            USER_ENTRY.kind(),
            ASSISTANT_ENTRY.kind(),
            SYSTEM_ENTRY.kind(),
            TOOL_RESULT_ENTRY.kind(),
            RESET_ENTRY.kind(),
            COMPACTION_ENTRY.kind(),
        ];
        assert_eq!(
            kinds,
            [
                "pi.user",
                "pi.assistant",
                "pi.system",
                "pi.tool-result",
                "pi.reset",
                "pi.compaction"
            ]
        );
        let data = r#"{"diagnostics":[{"severity":"warn","code":"truncated","message":"truncated"},{"severity":"info","message":"ok"}]}"#;
        let result = TOOL_RESULT_ENTRY
            .narrow(record(
                "pi.tool-result",
                Some(JsonValue::parse(data).unwrap()),
            ))
            .unwrap()
            .unwrap();
        assert_eq!(
            result.data().diagnostics[0].severity,
            ToolDiagnosticSeverity::Warn
        );
        assert_eq!(to_json(result.data()).unwrap().to_string(), data);
        let compaction = COMPACTION_ENTRY.narrow(record(
            "pi.compaction",
            Some(JsonValue::parse(r#"{"reason":"overflow"}"#).unwrap()),
        ));
        assert_eq!(
            compaction.unwrap().unwrap().data().reason,
            CompactionReason::Overflow
        );
    }
}
