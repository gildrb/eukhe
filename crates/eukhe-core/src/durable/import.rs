//! Import of an old `<id>.jsonl` session into a new durable storage.
//!
//! The active branch (root to the file's default leaf) becomes the root
//! conversation: user/assistant/tool-result messages as the built-in
//! entries, compactions as `pi.compaction` heads, custom rows as eukhe entry
//! kinds (`crate::durable::entries`); the model, thinking level, and cwd
//! become the root's `pi.agent`, the branch's goal state the goal doc, and
//! the file's name, archived state, Anthropic warning marker, and RLM
//! lineage the session metadata ([`super::session_meta`]). Everything lands
//! in one commit inside a staging directory that is made durable and
//! renamed into place ([`super::staging`]), so `storage_dir` either holds
//! the whole import or does not exist. The storage's files keep the legacy
//! file's mtime, so the session keeps its recency. The legacy file is only
//! read.

mod plan;
#[cfg(test)]
mod tests;

use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::SystemTime;

use eukhe_ai::models::{create_models, CreateModelsOptions};
use eukhe_chord::context::{without_abort_signal, Context};
use eukhe_chord::json::{to_json, JsonError, JsonValue};
use eukhe_durable::entries::ASSISTANT_ENTRY;
use eukhe_durable::errors::StorageError;
use eukhe_durable::harness::json::assign_json;
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{AgentChange, FieldChange, HarnessOptions, ModelRef};
use eukhe_durable::harness::usage::{record_usage, UsageBucket};
use eukhe_durable::harness::{Harness, RootOptions};
use eukhe_durable::session::{SessionError, SessionResult, Tx};
use eukhe_durable::storage::jsonl::{open_native_jsonl_storage, JsonlStorageOptions};
use eukhe_durable::types::{ConversationId, EntryHead, EntryId};
use eukhe_types::pi_ai::{Message, ModelThinkingLevel};
use futures::FutureExt;

use self::plan::{plan_import, ImportPlan, PlannedHead};
use super::staging::{publish, staging_dir, StagingKind};
use crate::durable::goals::import_legacy_goal;
use crate::durable::session_meta::SESSION_META_DOC;

/// The durable storage's commit log; a directory without it is no session.
const MAIN_FILE: &str = "main.jsonl";

/// What [`import_legacy_session`] wrote.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportReport {
    /// The legacy header's session id.
    pub session_id: String,
    /// The legacy header's cwd, now the root agent's `cwd`.
    pub cwd: String,
    /// The latest `model_change` on the branch.
    pub model: Option<ModelRef>,
    /// The latest `thinking_level_change` on the branch.
    pub thinking_level: Option<ModelThinkingLevel>,
    /// The legacy entry id the imported branch ends at.
    pub leaf_id: Option<String>,
    /// Durable entries appended to the root conversation.
    pub entries: usize,
    /// Branch rows with no durable entry (labels, session info and state,
    /// git state, service tiers, child-usage rows, unknown rows); session
    /// info and state land in the session metadata instead.
    pub skipped_rows: usize,
}

/// Why an import failed. Nothing is left at `storage_dir` then, unless only
/// the final sync of its parent directory failed.
#[derive(Debug, thiserror::Error)]
pub enum ImportError {
    #[error("{action} {}: {source}", path.display())]
    Io {
        action: &'static str,
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("legacy session has no session header")]
    MissingHeader,
    #[error("durable storage {} already exists", path.display())]
    AlreadyExists { path: PathBuf },
    #[error("storage directory {} has no parent directory or is not UTF-8", path.display())]
    StorageDir { path: PathBuf },
    #[error("unknown thinking level {level:?} in legacy session")]
    ThinkingLevel { level: String },
    #[error("legacy entry {entry_id:?} does not convert: {source}")]
    Convert {
        entry_id: String,
        #[source]
        source: serde_json::Error,
    },
    #[error(transparent)]
    Json(#[from] JsonError),
    #[error(transparent)]
    Storage(#[from] StorageError),
    #[error(transparent)]
    Session(#[from] SessionError),
}

/// Make the durable storage `dir` exist when only its legacy session file
/// (the `<dir>.jsonl` sibling) does: the import every reader and opener
/// of a session goes through, so a legacy file is only ever read here.
/// `Some` with what this call imported; `None` when there was nothing to
/// import (`dir` exists, or no legacy sibling), also when a concurrent
/// import of the same file published the storage first.
///
/// # Errors
///
/// The legacy file does not import (see [`import_legacy_session`]).
pub async fn ensure_storage(dir: &Path, cx: &Context) -> Result<Option<ImportReport>, ImportError> {
    let (Some(parent), Some(name)) = (dir.parent(), dir.file_name()) else {
        return Ok(None);
    };
    let mut legacy = name.to_owned();
    legacy.push(".jsonl");
    let legacy = parent.join(legacy);
    if tokio::fs::try_exists(dir).await.unwrap_or(true) || !is_file(&legacy).await {
        return Ok(None);
    }
    match import_legacy_session(&legacy, dir, cx).await {
        Ok(report) => {
            tracing::info!(
                legacy = %legacy.display(),
                entries = report.entries,
                skipped_rows = report.skipped_rows,
                "imported legacy session"
            );
            Ok(Some(report))
        }
        Err(_) if is_file(&dir.join(MAIN_FILE)).await => Ok(None),
        Err(error) => Err(error),
    }
}

async fn is_file(path: &Path) -> bool {
    tokio::fs::metadata(path)
        .await
        .is_ok_and(|metadata| metadata.is_file())
}

/// Import the active branch of the legacy session file `legacy` into a new
/// durable JSONL storage at `storage_dir` (see the module docs).
///
/// # Errors
///
/// `storage_dir` exists; the legacy file cannot be read, has no header, or
/// holds rows that do not convert; or writing the storage fails. On error
/// nothing is left at `storage_dir`, unless only the final sync of its
/// parent directory failed (the storage is complete then).
pub async fn import_legacy_session(
    legacy: &Path,
    storage_dir: &Path,
    cx: &Context,
) -> Result<ImportReport, ImportError> {
    let bytes = tokio::fs::read(legacy)
        .await
        .map_err(io("read legacy session", legacy))?;
    let modified = tokio::fs::metadata(legacy)
        .await
        .and_then(|metadata| metadata.modified())
        .map_err(io("inspect legacy session", legacy))?;
    let content = legacy_text(&bytes).map_err(|error| ImportError::Io {
        action: "decode legacy session",
        path: legacy.to_owned(),
        source: std::io::Error::new(std::io::ErrorKind::InvalidData, error),
    })?;
    let plan = plan_import(content)?;
    let exists = tokio::fs::try_exists(storage_dir)
        .await
        .map_err(io("inspect", storage_dir))?;
    if exists {
        return Err(ImportError::AlreadyExists {
            path: storage_dir.to_owned(),
        });
    }
    let (parent, staging) =
        staging_dir(storage_dir, StagingKind::Import).ok_or_else(|| ImportError::StorageDir {
            path: storage_dir.to_owned(),
        })?;
    tokio::fs::create_dir_all(&parent)
        .await
        .map_err(io("create", &parent))?;
    tokio::fs::create_dir(&staging)
        .await
        .map_err(io("create staging directory", &staging))?;
    let report = report(&plan);
    let written = async {
        write_storage(&staging, plan, cx).await?;
        stamp_mtime(&staging, modified).await?;
        publish(&staging, storage_dir, &parent)
            .await
            .map_err(|error| ImportError::Io {
                action: error.action,
                path: error.path,
                source: error.source,
            })
    }
    .await;
    if let Err(error) = written {
        // A failed final sync already moved the staging directory into place.
        if tokio::fs::try_exists(&staging).await.unwrap_or(true) {
            if let Err(cleanup) = tokio::fs::remove_dir_all(&staging).await {
                tracing::warn!(
                    staging = %staging.display(),
                    error = %cleanup,
                    "failed to remove the staging directory of a failed session import"
                );
            }
        }
        return Err(error);
    }
    Ok(report)
}

/// Give every file of the storage in `dir` the legacy file's mtime, so the
/// imported session lists where the legacy one did (recency is the newest
/// mtime of the storage's files).
async fn stamp_mtime(dir: &Path, modified: SystemTime) -> Result<(), ImportError> {
    let mut entries = tokio::fs::read_dir(dir)
        .await
        .map_err(io("list staging directory", dir))?;
    while let Some(entry) = entries
        .next_entry()
        .await
        .map_err(io("list staging directory", dir))?
    {
        let path = entry.path();
        let file_type = entry.file_type().await.map_err(io("inspect", &path))?;
        if !file_type.is_file() {
            continue;
        }
        let file = tokio::fs::File::open(&path)
            .await
            .map_err(io("open", &path))?
            .into_std()
            .await;
        file.set_modified(modified)
            .map_err(io("set the mtime of", &path))?;
    }
    Ok(())
}

fn io<'a>(action: &'static str, path: &'a Path) -> impl FnOnce(std::io::Error) -> ImportError + 'a {
    move |source| ImportError::Io {
        action,
        path: path.to_owned(),
        source,
    }
}

/// The legacy file as text. A crash mid-append can leave an unterminated
/// last line cut inside a multi-byte character; that torn tail is an
/// uncommitted row (the parser skips it as malformed JSON anyway), so it
/// is dropped instead of failing the whole import. Invalid UTF-8 inside a
/// complete line is still an error.
fn legacy_text(bytes: &[u8]) -> Result<&str, std::str::Utf8Error> {
    let error = match std::str::from_utf8(bytes) {
        Ok(text) => return Ok(text),
        Err(error) => error,
    };
    let complete = bytes
        .iter()
        .rposition(|&byte| byte == b'\n')
        .map_or(0, |index| index + 1);
    if error.valid_up_to() < complete {
        return Err(error);
    }
    std::str::from_utf8(&bytes[..complete])
}

fn report(plan: &ImportPlan) -> ImportReport {
    ImportReport {
        session_id: plan.session_id.clone(),
        cwd: plan.cwd.clone(),
        model: plan.model.clone(),
        thinking_level: plan.thinking_level,
        leaf_id: plan.leaf_id.clone(),
        entries: plan.entries.len(),
        skipped_rows: plan.skipped_rows,
    }
}

/// Create the storage in `directory`: the root conversation, its agent, and
/// every planned entry in the creating commit.
async fn write_storage(
    directory: &Path,
    plan: ImportPlan,
    cx: &Context,
) -> Result<(), ImportError> {
    let directory = directory.to_str().ok_or_else(|| ImportError::StorageDir {
        path: directory.to_owned(),
    })?;
    let storage =
        open_native_jsonl_storage(directory, cx, JsonlStorageOptions { fsync: true }).await?;
    let harness = Harness::open(Arc::new(storage), harness_options(), cx).await?;
    let agent = AgentChange {
        model: plan
            .model
            .clone()
            .map_or(FieldChange::Keep, FieldChange::Set),
        thinking_level: plan
            .thinking_level
            .map_or(FieldChange::Keep, FieldChange::Set),
        cwd: FieldChange::Set(plan.cwd.clone()),
        ..AgentChange::default()
    };
    let created = harness
        .root(
            RootOptions {
                agent: Some(agent),
                init: Some(Box::new(move |tx, id| append_plan(tx, id, plan).boxed())),
            },
            cx,
        )
        .await;
    // Close even when the commit failed; the commit error wins.
    let closed = harness.close(&without_abort_signal(cx)).await;
    created?;
    closed?;
    Ok(())
}

/// The Harness options of the import: nothing runs, so no models and only
/// the built-in tasks.
fn harness_options() -> HarnessOptions {
    HarnessOptions::new(
        create_models(CreateModelsOptions::default()),
        Arc::new(create_registry()),
    )
}

/// Append every planned entry, seed the goal state from the branch, and
/// write the session metadata. Each imported assistant answer adds its
/// usage to `pi.usage`, as the commit that recorded a live response does:
/// the session's spend survives the import.
async fn append_plan(
    tx: Tx,
    conversation_id: ConversationId,
    plan: ImportPlan,
) -> SessionResult<()> {
    let mut appended: Vec<EntryId> = Vec::with_capacity(plan.entries.len());
    for planned in plan.entries {
        let mut draft = planned.draft;
        draft.head = match planned.head {
            PlannedHead::None => None,
            PlannedHead::SelfEntry => Some(EntryHead::SelfEntry),
            PlannedHead::Planned(index) => Some(EntryHead::Entry(appended[index])),
        };
        let answer = draft
            .model
            .as_deref()
            .and_then(<[Message]>::first)
            .and_then(Message::as_assistant)
            .filter(|_| draft.kind == ASSISTANT_ENTRY.kind())
            .map(|message| {
                (
                    format!("{}/{}", message.provider, message.model),
                    message.usage,
                )
            });
        appended.push(tx.append_entry(conversation_id, draft).await?.id);
        if let Some((key, usage)) = answer {
            record_usage(&tx, conversation_id, UsageBucket::Models, &key, &usage).await?;
        }
    }
    import_legacy_goal(&tx, conversation_id, &plan.branch).await?;
    if let JsonValue::Object(fields) = to_json(&plan.meta)? {
        if !fields.is_empty() {
            let draft = tx.doc(&SESSION_META_DOC, ()).await?;
            for (key, value) in fields.iter() {
                assign_json(&draft, key, value)?;
            }
        }
    }
    Ok(())
}
