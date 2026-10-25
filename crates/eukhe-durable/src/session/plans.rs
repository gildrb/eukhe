//! Batch assembly data of one transaction: staged submission changes and the
//! write and publication plan of every staged document incarnation.

use std::sync::Arc;

use crate::types::{
    ConversationId, DocumentBase, DocumentContent, DocumentCreate, DocumentDelta, DocumentId,
    DocumentRecord, DocumentRecordScope, EntryId, InputSubmission, StorageWrite, SubmissionRecord,
    SubmissionSettlement, SubmissionState, WriteSubmission,
};
use eukhe_bend::rules::submission::{self, Change, Out, Sub, Why};
use eukhe_chord::delta::{Prepared, Tracker};

use super::error::{SessionError, SessionResult};
use super::observation::Ops;
use super::transaction::{object_value, Definition, DocumentEntry, DocumentTarget, LoadedDocument};

/// A staged submission change: a settlement, or the placement of a queued
/// submission at its entry.
#[derive(Clone, Debug)]
pub(super) enum SubmissionChange {
    Settle(SubmissionSettlement),
    Placed(EntryId),
}

/// Complete record after applying one change. The compiled core decides
/// (`eukhe_bend::rules::submission`, `laws/submission.bend`): placement
/// turns a queued input `placed` and a queued write `done`; only a placed
/// input can be answered; a settled record stays. `None` means unchanged.
pub(super) fn apply_submission_change(
    current: &SubmissionRecord,
    change: &SubmissionChange,
) -> SessionResult<Option<SubmissionRecord>> {
    let asked = match change {
        SubmissionChange::Placed(entry) => Change::Place { entry: entry.get() },
        SubmissionChange::Settle(SubmissionSettlement::Done { answer }) => Change::Answer {
            answer: answer.get(),
        },
        SubmissionChange::Settle(SubmissionSettlement::Unanswered { .. }) => Change::Unanswered,
    };
    let out = submission::step(lifecycle(&current.state), asked)
        .map_err(|error| SessionError::error(error.to_string()))?;
    let next = match out {
        Out::Stays => return Ok(None),
        Out::Refused(Why::NotQueued) => {
            return Err(SessionError::error(format!(
                "Submission {} is not queued",
                current.id
            )));
        }
        Out::Refused(Why::NotPlacedInput) => {
            return Err(SessionError::error(format!(
                "Submission {} is not a placed input",
                current.id
            )));
        }
        Out::Moves(next) => next,
    };
    // Queued and placed records carry no answer, reason, or detail: an
    // unanswered record takes them from its settlement.
    let settlement = match change {
        SubmissionChange::Settle(SubmissionSettlement::Unanswered { reason, detail }) => {
            Some((reason, detail))
        }
        SubmissionChange::Placed(_)
        | SubmissionChange::Settle(SubmissionSettlement::Done { .. }) => None,
    };
    let state = match (next, settlement) {
        (Sub::InputQueued, _) => SubmissionState::Input(InputSubmission::Queued),
        (Sub::InputPlaced { entry }, _) => SubmissionState::Input(InputSubmission::Placed {
            entry: EntryId::from_number(entry),
        }),
        (Sub::InputAnswered { entry, answer }, _) => {
            SubmissionState::Input(InputSubmission::Done {
                entry: EntryId::from_number(entry),
                answer: EntryId::from_number(answer),
            })
        }
        (Sub::InputUnanswered { entry }, Some((reason, detail))) => {
            SubmissionState::Input(InputSubmission::Unanswered {
                entry: entry.map(EntryId::from_number),
                reason: reason.clone(),
                detail: detail.clone(),
            })
        }
        (Sub::WriteQueued, _) => SubmissionState::Write(WriteSubmission::Queued),
        (Sub::WriteDone { entry }, _) => SubmissionState::Write(WriteSubmission::Done {
            entry: EntryId::from_number(entry),
        }),
        (Sub::WriteUnanswered, Some((reason, detail))) => {
            SubmissionState::Write(WriteSubmission::Unanswered {
                reason: reason.clone(),
                detail: detail.clone(),
            })
        }
        (Sub::InputUnanswered { .. } | Sub::WriteUnanswered, None) => {
            return Err(SessionError::error(format!(
                "Submission {}: the core settled it unanswered without an unanswered settlement",
                current.id
            )));
        }
    };
    Ok(Some(SubmissionRecord {
        state,
        ..current.clone()
    }))
}

/// The lifecycle of a submission state, as the core reads it.
fn lifecycle(state: &SubmissionState) -> Sub {
    match state {
        SubmissionState::Input(InputSubmission::Queued) => Sub::InputQueued,
        SubmissionState::Input(InputSubmission::Placed { entry }) => {
            Sub::InputPlaced { entry: entry.get() }
        }
        SubmissionState::Input(InputSubmission::Done { entry, answer }) => Sub::InputAnswered {
            entry: entry.get(),
            answer: answer.get(),
        },
        SubmissionState::Input(InputSubmission::Unanswered { entry, .. }) => Sub::InputUnanswered {
            entry: entry.map(EntryId::get),
        },
        SubmissionState::Write(WriteSubmission::Queued) => Sub::WriteQueued,
        SubmissionState::Write(WriteSubmission::Done { entry }) => {
            Sub::WriteDone { entry: entry.get() }
        }
        SubmissionState::Write(WriteSubmission::Unanswered { .. }) => Sub::WriteUnanswered,
    }
}

/// The record a plan writes: committed, or created by this commit.
#[derive(Clone)]
pub(super) enum PlanRecord {
    Committed(DocumentRecord),
    New(DocumentCreate),
}

impl PlanRecord {
    pub(super) fn id(&self) -> DocumentId {
        match self {
            Self::Committed(record) => record.id,
            Self::New(record) => record.id,
        }
    }

    pub(super) fn scope(&self) -> DocumentRecordScope {
        match self {
            Self::Committed(record) => record.scope,
            Self::New(record) => record.scope,
        }
    }
}

/// Prepared change of a tracked incarnation.
pub(super) struct PlanChange {
    pub(super) tracker: Tracker,
    pub(super) prepared: Prepared,
    /// Exact prepared operations shared by the stored delta and the publication.
    pub(super) ops: Ops,
    pub(super) version: u64,
    /// The cached incarnation this change updates; absent when it creates one.
    pub(super) loaded: Option<Arc<LoadedDocument>>,
    pub(super) definition: Option<Definition>,
}

/// What one staged incarnation writes and publishes, decided once before
/// Storage admission so adoption only applies it.
pub(super) struct DocumentPlan {
    pub(super) address_id: String,
    pub(super) record: PlanRecord,
    pub(super) retire: bool,
    /// Creation, copy, or change content; absent when only retirement is written.
    pub(super) content: Option<StorageWrite>,
    /// Prepared change of a tracked incarnation; absent for fork copies and
    /// retirement-only entries.
    pub(super) change: Option<PlanChange>,
    /// Resolved before Storage admission so adoption performs no reads.
    pub(super) conversation_id: Option<ConversationId>,
}

/// Plan of one staged document: its record, content write, and prepared
/// change. Retirement is decided later.
pub(super) fn plan_document(document: &DocumentEntry) -> Option<DocumentPlan> {
    let target = document.target.as_ref()?;
    let address_id = document.address_id.clone();
    let retire = document.retire_on_commit;
    Some(match target {
        DocumentTarget::Created {
            record,
            version,
            tracker,
        } => {
            let prepared = document
                .prepared
                .clone()
                .expect("created documents are prepared");
            let content = DocumentBase {
                version: *version,
                value: object_value(prepared.value()),
            };
            DocumentPlan {
                address_id,
                record: PlanRecord::New(record.clone()),
                retire,
                content: Some(StorageWrite::DocumentCreate {
                    record: record.clone(),
                    content,
                }),
                change: Some(PlanChange {
                    tracker: tracker.clone(),
                    ops: Arc::from(prepared.ops()),
                    prepared,
                    version: *version,
                    loaded: None,
                    definition: None,
                }),
                conversation_id: None,
            }
        }
        DocumentTarget::ForkCopy { record, source } => DocumentPlan {
            address_id,
            record: PlanRecord::New(record.clone()),
            retire,
            content: Some(StorageWrite::DocumentCopy {
                record: record.clone(),
                source: *source,
            }),
            change: None,
            conversation_id: None,
        },
        DocumentTarget::RetireOnly(record) => DocumentPlan {
            address_id,
            record: PlanRecord::Committed(record.clone()),
            retire,
            content: None,
            change: None,
            conversation_id: None,
        },
        DocumentTarget::Loaded(loaded) => plan_loaded(document, loaded, address_id, retire),
    })
}

/// Plan of a loaded incarnation: a version change stores a base even without
/// operations; otherwise only a change stores a delta.
fn plan_loaded(
    document: &DocumentEntry,
    loaded: &Arc<LoadedDocument>,
    address_id: String,
    retire: bool,
) -> DocumentPlan {
    let definition = document
        .definition
        .clone()
        .expect("loaded documents carry their definition");
    let prepared = document
        .prepared
        .clone()
        .expect("loaded documents are prepared");
    let version = definition.version();
    let id = loaded.record.id;
    let ops: Ops = Arc::from(prepared.ops());
    // A version change stores a base even without operations;
    // otherwise only a change stores a delta.
    let content = if loaded.stored_version() < version {
        Some(StorageWrite::DocumentChange {
            id,
            content: DocumentContent::Base(DocumentBase {
                version,
                value: object_value(prepared.value()),
            }),
        })
    } else if ops.is_empty() {
        None
    } else {
        Some(StorageWrite::DocumentChange {
            id,
            content: DocumentContent::Delta(DocumentDelta {
                version,
                ops: Arc::clone(&ops),
            }),
        })
    };
    DocumentPlan {
        address_id,
        record: PlanRecord::Committed(loaded.record.clone()),
        retire,
        content,
        change: Some(PlanChange {
            tracker: loaded.tracker.clone(),
            prepared,
            ops,
            version,
            loaded: Some(Arc::clone(loaded)),
            definition: Some(definition),
        }),
        conversation_id: None,
    }
}

/// Whether adoption publishes the plan: every creation, copy, and retirement,
/// and a loaded incarnation that writes content, which includes a
/// migration-only base so observers of the older shape receive the new value.
pub(super) fn publishes(plan: &DocumentPlan) -> bool {
    plan.retire
        || plan
            .change
            .as_ref()
            .is_none_or(|change| change.loaded.is_none())
        || plan.content.is_some()
}
