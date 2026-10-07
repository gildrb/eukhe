//! Batch assembly data of one transaction: staged submission changes and the
//! write and publication plan of every staged document incarnation.

use std::sync::Arc;

use crate::types::{
    ConversationId, DocumentBase, DocumentContent, DocumentCreate, DocumentDelta, DocumentId,
    DocumentRecord, DocumentRecordScope, EntryId, InputSubmission, StorageWrite, SubmissionRecord,
    SubmissionSettlement, SubmissionState, WriteSubmission,
};
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

/// Complete record after applying one change. Placement turns a queued input
/// `placed` and a queued write `done`; only a placed input can be answered. A
/// settled record stays. `None` means unchanged.
pub(super) fn apply_submission_change(
    current: &SubmissionRecord,
    change: &SubmissionChange,
) -> SessionResult<Option<SubmissionRecord>> {
    if current.state.is_settled() {
        return Ok(None);
    }
    let state = match (change, &current.state) {
        (SubmissionChange::Placed(entry), SubmissionState::Input(InputSubmission::Queued)) => {
            SubmissionState::Input(InputSubmission::Placed { entry: *entry })
        }
        (SubmissionChange::Placed(entry), SubmissionState::Write(WriteSubmission::Queued)) => {
            SubmissionState::Write(WriteSubmission::Done { entry: *entry })
        }
        (SubmissionChange::Placed(_), _) => {
            return Err(SessionError::error(format!(
                "Submission {} is not queued",
                current.id
            )));
        }
        (
            SubmissionChange::Settle(SubmissionSettlement::Done { answer }),
            SubmissionState::Input(InputSubmission::Placed { entry }),
        ) => SubmissionState::Input(InputSubmission::Done {
            entry: *entry,
            answer: *answer,
        }),
        (SubmissionChange::Settle(SubmissionSettlement::Done { .. }), _) => {
            return Err(SessionError::error(format!(
                "Submission {} is not a placed input",
                current.id
            )));
        }
        // Queued and placed records carry no answer, reason, or detail; an
        // unanswered input keeps its entry.
        (
            SubmissionChange::Settle(SubmissionSettlement::Unanswered { reason, detail }),
            SubmissionState::Input(_),
        ) => SubmissionState::Input(InputSubmission::Unanswered {
            entry: current.state.entry(),
            reason: reason.clone(),
            detail: detail.clone(),
        }),
        (
            SubmissionChange::Settle(SubmissionSettlement::Unanswered { reason, detail }),
            SubmissionState::Write(_),
        ) => SubmissionState::Write(WriteSubmission::Unanswered {
            reason: reason.clone(),
            detail: detail.clone(),
        }),
    };
    Ok(Some(SubmissionRecord {
        state,
        ..current.clone()
    }))
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
