//! Import of an old `<id>.jsonl` session into a new durable storage.
//!
//! The active branch (root to the file's default leaf) becomes the root
//! conversation: user/assistant/tool-result messages as the built-in
//! entries, compactions as `pi.compaction` heads, custom rows as eukhe entry
//! kinds (`crate::durable::entries`); the model, thinking level, and cwd
//! become the root's `pi.agent`, the branch's goal state the goal doc.
//! Everything lands in one commit inside a
//! staging directory that is renamed into place, so `storage_dir` either
//! holds the whole import or does not exist. The legacy file is only read.

mod plan;
#[cfg(test)]
mod tests;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_chord::context::{without_abort_signal, Context};
use eukhe_chord::json::JsonError;
use eukhe_durable::errors::StorageError;
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{AgentChange, FieldChange, HarnessOptions, ModelRef};
use eukhe_durable::harness::{Harness, RootOptions};
use eukhe_durable::session::{SessionError, SessionResult, Tx};
use eukhe_durable::storage::jsonl::{open_native_jsonl_storage, JsonlStorageOptions};
use eukhe_durable::types::{ConversationId, EntryHead, EntryId};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_types::pi_ai::ModelThinkingLevel;
use futures::FutureExt;

use self::plan::{plan_import, ImportPlan, PlannedHead};
use crate::durable::goals::import_legacy_goal;

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
    /// Branch rows with no durable counterpart (labels, session info and
    /// state, git state, service tiers, child-usage rows, unknown rows).
    pub skipped_rows: usize,
}

/// Why an import failed. Nothing is left at `storage_dir` then.
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

/// Import the active branch of the legacy session file `legacy` into a new
/// durable JSONL storage at `storage_dir` (see the module docs).
///
/// # Errors
///
/// `storage_dir` exists; the legacy file cannot be read, has no header, or
/// holds rows that do not convert; or writing the storage fails. On error
/// nothing is left at `storage_dir`.
pub async fn import_legacy_session(
    legacy: &Path,
    storage_dir: &Path,
    cx: &Context,
) -> Result<ImportReport, ImportError> {
    let content = tokio::fs::read_to_string(legacy)
        .await
        .map_err(io("read legacy session", legacy))?;
    let plan = plan_import(&content)?;
    let exists = tokio::fs::try_exists(storage_dir)
        .await
        .map_err(io("inspect", storage_dir))?;
    if exists {
        return Err(ImportError::AlreadyExists {
            path: storage_dir.to_owned(),
        });
    }
    let (parent, staging) = staging_dir(storage_dir)?;
    tokio::fs::create_dir_all(&parent)
        .await
        .map_err(io("create", &parent))?;
    tokio::fs::create_dir(&staging)
        .await
        .map_err(io("create staging directory", &staging))?;
    let report = report(&plan);
    let written = match write_storage(&staging, plan, cx).await {
        Ok(()) => tokio::fs::rename(&staging, storage_dir)
            .await
            .map_err(io("move import into", storage_dir)),
        Err(error) => Err(error),
    };
    if let Err(error) = written {
        if let Err(cleanup) = tokio::fs::remove_dir_all(&staging).await {
            tracing::warn!(
                staging = %staging.display(),
                error = %cleanup,
                "failed to remove the staging directory of a failed session import"
            );
        }
        return Err(error);
    }
    sync_dir(&parent).await?;
    Ok(report)
}

fn io<'a>(action: &'static str, path: &'a Path) -> impl FnOnce(std::io::Error) -> ImportError + 'a {
    move |source| ImportError::Io {
        action,
        path: path.to_owned(),
        source,
    }
}

/// The parent of `storage_dir` and a unique staging directory beside it
/// (same filesystem, so the final rename is atomic).
fn staging_dir(storage_dir: &Path) -> Result<(PathBuf, PathBuf), ImportError> {
    let invalid = || ImportError::StorageDir {
        path: storage_dir.to_owned(),
    };
    let name = storage_dir
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(invalid)?;
    let parent = match storage_dir.parent() {
        Some(parent) if parent.as_os_str().is_empty() => PathBuf::from("."),
        Some(parent) => parent.to_owned(),
        None => return Err(invalid()),
    };
    let staging = parent.join(format!(".{name}.import-{}", uuid::Uuid::new_v4().simple()));
    if staging.to_str().is_none() {
        return Err(invalid());
    }
    Ok((parent, staging))
}

/// Flush the directory entry of the renamed storage.
async fn sync_dir(dir: &Path) -> Result<(), ImportError> {
    let dir = dir.to_owned();
    let synced = tokio::task::spawn_blocking({
        let dir = dir.clone();
        move || std::fs::File::open(&dir).and_then(|file| file.sync_all())
    })
    .await
    .map_err(|join| ImportError::Io {
        action: "sync",
        path: dir.clone(),
        source: std::io::Error::other(join),
    })?;
    synced.map_err(io("sync", &dir))
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

/// Append every planned entry, then seed the goal state from the branch.
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
        appended.push(tx.append_entry(conversation_id, draft).await?.id);
    }
    import_legacy_goal(&tx, conversation_id, &plan.branch).await
}
