//! Forking a session into a new storage: the source (a durable storage, or a
//! legacy file imported on the way) is copied into a staging directory
//! beside `new_dir`, its main conversation is forked there and recorded as
//! the copy's main conversation, and the staging directory is made durable
//! and renamed into place ([`super::staging`]), so `new_dir` holds the whole
//! fork or does not exist. The source is only read.

#[cfg(test)]
mod tests;

use std::path::{Path, PathBuf};
use std::sync::Arc;

use eukhe_ai::models::{create_models, CreateModelsOptions};
use eukhe_chord::context::{without_abort_signal, Context};
use eukhe_chord::json::JsonValue;
use eukhe_durable::errors::StorageError;
use eukhe_durable::harness::agent::AGENT_DOC;
use eukhe_durable::harness::json::assign_json;
use eukhe_durable::harness::registry::create_registry;
use eukhe_durable::harness::types::{
    AgentChange, ConversationCreateOptions, FieldChange, HarnessOptions,
};
use eukhe_durable::harness::{Conversation, ConversationEntryQuery, Harness};
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::storage::jsonl::{open_native_jsonl_storage, JsonlStorageOptions};
use eukhe_durable::types::{ConversationId, ConversationOwnership, EntryId};
use futures::FutureExt;

use super::discovery::SessionLocation;
use super::import::{import_legacy_session, ImportError};
use super::main_conversation::{main_conversation, set_main_conversation};
use super::staging::{publish, staging_dir, StagingKind};
use crate::session::manager::read_session_header;

/// The durable storage's commit log, copied last (see [`copy_storage`]).
const MAIN_FILE: &str = "main.jsonl";

/// Copies of a source that keeps publishing commits [`copy_storage`] takes
/// before it gives up.
const COPY_ATTEMPTS: usize = 8;

/// Where the fork starts in the source's main conversation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForkPoint {
    /// At its latest visible entry; an empty conversation forks as
    /// [`ForkPoint::Start`].
    Latest,
    /// At this visible entry (the fork's last inherited entry).
    Entry(EntryId),
    /// Before its first entry: a new empty conversation carrying a copy of
    /// its `pi.agent` (model, thinking level, cwd, ...).
    Start,
}

/// The new session [`fork_session`] wrote.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForkedSession {
    /// The new storage directory.
    pub dir: PathBuf,
    /// The fork: the new storage's main conversation.
    pub main: ConversationId,
}

/// Why a fork failed. Nothing is left at `new_dir` then, unless only the
/// final sync of its parent directory failed.
#[derive(Debug, thiserror::Error)]
pub enum ForkError {
    #[error("Cannot fork: source session not found: {}", path.display())]
    MissingSource { path: PathBuf },
    #[error("Cannot fork: source session file is not a regular file: {}", path.display())]
    NotRegularFile { path: PathBuf },
    #[error("Cannot fork: source session file is empty or invalid: {}", path.display())]
    InvalidSource { path: PathBuf },
    #[error("fork target {} already exists", path.display())]
    TargetExists { path: PathBuf },
    #[error("fork target {} has no parent directory or is not UTF-8", path.display())]
    TargetDir { path: PathBuf },
    #[error("{action} {}: {source}", path.display())]
    Io {
        action: &'static str,
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error(
        "Cannot fork: source session {} kept committing through {attempts} copy attempts",
        path.display()
    )]
    SourceBusy { path: PathBuf, attempts: usize },
    #[error("failed to import legacy session {}: {source}", path.display())]
    Import {
        path: PathBuf,
        #[source]
        source: ImportError,
    },
    #[error(transparent)]
    Storage(#[from] StorageError),
    #[error(transparent)]
    Session(#[from] SessionError),
}

/// Copy `source` (a durable storage, or a legacy file imported) into
/// `new_dir`, fork its main conversation at `at`, and record the fork as the
/// copy's main conversation (`eukhe.session`). `cwd` (when given) becomes the
/// fork's `pi.agent` cwd in the same commit.
///
/// A durable source being written by another process is copied as one
/// consistent snapshot of its commits (see [`copy_storage`]).
///
/// # Errors
///
/// The source is missing or invalid, `new_dir` exists, or copying, the
/// import, or the fork commit fails. On error nothing is left at `new_dir`,
/// unless only the final sync of its parent directory failed (the fork is
/// complete then).
pub async fn fork_session(
    source: &SessionLocation,
    at: ForkPoint,
    cwd: Option<&Path>,
    new_dir: &Path,
    cx: &Context,
) -> Result<ForkedSession, ForkError> {
    fork_into(source, None, at, cwd, new_dir, cx).await
}

/// [`fork_session`] of the source's conversation `conversation` instead of
/// its main one (`at` is a point of that conversation); the fork still
/// becomes the copy's main conversation.
///
/// # Errors
///
/// As [`fork_session`]; also when `conversation` does not exist.
pub async fn fork_session_conversation(
    source: &SessionLocation,
    conversation: ConversationId,
    at: ForkPoint,
    cwd: Option<&Path>,
    new_dir: &Path,
    cx: &Context,
) -> Result<ForkedSession, ForkError> {
    fork_into(source, Some(conversation), at, cwd, new_dir, cx).await
}

/// The shared body of the session forks: fork `conversation` (`None`: the
/// main one) of a copy of `source` into `new_dir`.
async fn fork_into(
    source: &SessionLocation,
    conversation: Option<ConversationId>,
    at: ForkPoint,
    cwd: Option<&Path>,
    new_dir: &Path,
    cx: &Context,
) -> Result<ForkedSession, ForkError> {
    let exists = tokio::fs::try_exists(new_dir)
        .await
        .map_err(io("inspect", new_dir))?;
    if exists {
        return Err(ForkError::TargetExists {
            path: new_dir.to_owned(),
        });
    }
    let (parent, staging) =
        staging_dir(new_dir, StagingKind::Fork).ok_or_else(|| ForkError::TargetDir {
            path: new_dir.to_owned(),
        })?;
    tokio::fs::create_dir_all(&parent)
        .await
        .map_err(io("create", &parent))?;
    let forked = async {
        populate(source, &staging, cx).await?;
        let main = fork_storage(&staging, conversation, at, cwd, cx).await?;
        publish(&staging, new_dir, &parent)
            .await
            .map_err(|error| ForkError::Io {
                action: error.action,
                path: error.path,
                source: error.source,
            })?;
        Ok(main)
    }
    .await;
    match forked {
        Ok(main) => Ok(ForkedSession {
            dir: new_dir.to_owned(),
            main,
        }),
        Err(error) => {
            if tokio::fs::try_exists(&staging).await.unwrap_or(true) {
                if let Err(cleanup) = tokio::fs::remove_dir_all(&staging).await {
                    tracing::warn!(
                        staging = %staging.display(),
                        error = %cleanup,
                        "failed to remove the staging directory of a failed fork"
                    );
                }
            }
            Err(error)
        }
    }
}

/// Fork `main` at `at` inside `harness` and make the fork the main
/// conversation in its creating commit (call `EukheSession::reload_main`
/// afterwards). `cwd` (when given) becomes the fork's `pi.agent` cwd.
///
/// # Errors
///
/// Reading `main`'s entries or agent, or the creating commit, fails.
pub async fn fork_main_conversation(
    harness: &Harness,
    main: &Conversation,
    at: ForkPoint,
    cwd: Option<&Path>,
    cx: &Context,
) -> SessionResult<Conversation> {
    let cwd = cwd.map(|cwd| cwd.to_string_lossy().into_owned());
    let entry = match at {
        ForkPoint::Entry(entry) => Some(entry),
        ForkPoint::Latest => main
            .entries(ConversationEntryQuery::default(), 1, None, cx)
            .await?
            .items
            .first()
            .map(|entry| entry.id),
        ForkPoint::Start => None,
    };
    if let Some(entry) = entry {
        let mut options = ConversationCreateOptions::new(ConversationOwnership::Ownerless);
        options.agent = cwd.map(|cwd| AgentChange {
            cwd: FieldChange::Set(cwd),
            ..AgentChange::default()
        });
        options.init = Some(Box::new(|tx, id| {
            async move { set_main_conversation(&tx, id).await }.boxed()
        }));
        return main.fork(entry, options, cx).await;
    }
    let agent = harness.snapshot(&AGENT_DOC, main.id(), cx).await?;
    let mut options = ConversationCreateOptions::new(ConversationOwnership::Ownerless);
    options.init = Some(Box::new(move |tx, id| {
        async move {
            let draft = tx.doc(&AGENT_DOC, id).await?;
            if let Some(agent) = agent {
                for (key, value) in agent.iter() {
                    assign_json(&draft, key, value)?;
                }
            }
            if let Some(cwd) = cwd {
                assign_json(&draft, "cwd", &JsonValue::from(cwd))?;
            }
            set_main_conversation(&tx, id).await
        }
        .boxed()
    }));
    harness.create_conversation(options, cx).await
}

/// Fill the missing `staging` with the source's storage.
async fn populate(source: &SessionLocation, staging: &Path, cx: &Context) -> Result<(), ForkError> {
    let storage_dir = source.storage_dir();
    if is_storage(&storage_dir).await {
        return copy_storage(&storage_dir, staging).await;
    }
    let file = match source {
        SessionLocation::Durable(dir) => {
            return Err(ForkError::MissingSource { path: dir.clone() });
        }
        SessionLocation::Legacy(file) => file,
    };
    match tokio::fs::metadata(file).await {
        Ok(metadata) if metadata.is_file() => {}
        Ok(_) => return Err(ForkError::NotRegularFile { path: file.clone() }),
        Err(_) => return Err(ForkError::InvalidSource { path: file.clone() }),
    }
    let header = {
        let path = file.clone();
        tokio::task::spawn_blocking(move || read_session_header(&path))
            .await
            .map_err(|join| ForkError::Io {
                action: "read",
                path: file.clone(),
                source: std::io::Error::other(join),
            })?
    };
    if header.is_none() {
        return Err(ForkError::InvalidSource { path: file.clone() });
    }
    match import_legacy_session(file, staging, cx).await {
        Ok(_) => Ok(()),
        Err(ImportError::MissingHeader) => Err(ForkError::InvalidSource { path: file.clone() }),
        Err(source) => Err(ForkError::Import {
            path: file.clone(),
            source,
        }),
    }
}

async fn is_storage(dir: &Path) -> bool {
    tokio::fs::metadata(dir.join(MAIN_FILE))
        .await
        .is_ok_and(|metadata| metadata.is_file())
}

/// Copy the storage `source` into the missing `target` as one consistent
/// snapshot, also while another process commits to it.
///
/// The invariant is the JSONL storage's commit order: a commit appends its
/// sidecar records, then its `main.jsonl` marker, and only after that marker
/// reclaims (rewrites or removes) the sidecars it made unneeded; `main.jsonl`
/// itself only grows. So every other file is copied first and `main.jsonl`
/// last, and the copy stands when `main.jsonl` had the copied length before
/// anything was copied: no commit was published meanwhile, so the sidecar
/// records every copied marker needs were appended before the copy began,
/// every reclamation the copy saw was authorized by a copied marker, and the
/// records of later commits are unconfirmed tails the copy drops when it
/// opens. A commit published mid-copy can tear the copy (its marker needs a
/// record appended after its sidecar was copied), so that copy is discarded
/// and taken again, at most [`COPY_ATTEMPTS`] times.
async fn copy_storage(source: &Path, target: &Path) -> Result<(), ForkError> {
    for _ in 0..COPY_ATTEMPTS {
        let published = copy_without_main(source, target).await?;
        match finish_copy(source, target, published).await? {
            Snapshot::Consistent => return Ok(()),
            Snapshot::Torn => tokio::fs::remove_dir_all(target)
                .await
                .map_err(io("remove torn copy", target))?,
        }
    }
    Err(ForkError::SourceBusy {
        path: source.to_owned(),
        attempts: COPY_ATTEMPTS,
    })
}

/// Whether a copy of a storage holds one snapshot of its commits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Snapshot {
    /// No commit was published while the copy was taken.
    Consistent,
    /// A commit was published meanwhile; the copy may lack its records.
    Torn,
}

/// The first step of a [`copy_storage`] attempt: create `target` and copy
/// every entry of `source` but `main.jsonl` into it. Returns the length
/// `main.jsonl` had before.
async fn copy_without_main(source: &Path, target: &Path) -> Result<u64, ForkError> {
    tokio::fs::create_dir(target)
        .await
        .map_err(io("create staging directory", target))?;
    let main = source.join(MAIN_FILE);
    let published = tokio::fs::metadata(&main)
        .await
        .map_err(io("inspect", &main))?
        .len();
    copy_dir_contents(source, target, Some(MAIN_FILE)).await?;
    Ok(published)
}

/// The last step of a [`copy_storage`] attempt: copy `main.jsonl`, whose
/// length was `published` before [`copy_without_main`], and judge the copy.
async fn finish_copy(source: &Path, target: &Path, published: u64) -> Result<Snapshot, ForkError> {
    let main = source.join(MAIN_FILE);
    let copied = tokio::fs::copy(&main, target.join(MAIN_FILE))
        .await
        .map_err(io("copy", &main))?;
    Ok(if copied == published {
        Snapshot::Consistent
    } else {
        Snapshot::Torn
    })
}

/// Copy the entries of `source` into the existing `target`, recursively,
/// except the top-level `skip`.
async fn copy_dir_contents(
    source: &Path,
    target: &Path,
    skip: Option<&str>,
) -> Result<(), ForkError> {
    let mut pending = vec![(source.to_owned(), target.to_owned(), skip)];
    while let Some((from, to, skip)) = pending.pop() {
        let mut entries = tokio::fs::read_dir(&from)
            .await
            .map_err(io("read directory", &from))?;
        while let Some(entry) = entries
            .next_entry()
            .await
            .map_err(io("read directory", &from))?
        {
            let name = entry.file_name();
            if skip.is_some_and(|skip| name == skip) {
                continue;
            }
            let path = entry.path();
            let destination = to.join(&name);
            let file_type = entry.file_type().await.map_err(io("inspect", &path))?;
            if file_type.is_dir() {
                tokio::fs::create_dir(&destination)
                    .await
                    .map_err(io("create", &destination))?;
                pending.push((path, destination, None));
            } else {
                tokio::fs::copy(&path, &destination)
                    .await
                    .map_err(io("copy", &path))?;
            }
        }
    }
    Ok(())
}

/// Open the copied storage in `dir` (nothing is resumed), fork
/// `conversation` (`None`: its main conversation), and close it.
async fn fork_storage(
    dir: &Path,
    conversation: Option<ConversationId>,
    at: ForkPoint,
    cwd: Option<&Path>,
    cx: &Context,
) -> Result<ConversationId, ForkError> {
    let directory = dir.to_str().ok_or_else(|| ForkError::TargetDir {
        path: dir.to_owned(),
    })?;
    let storage =
        open_native_jsonl_storage(directory, cx, JsonlStorageOptions { fsync: true }).await?;
    let harness = Harness::open(Arc::new(storage), harness_options(), cx).await?;
    let forked = async {
        let source = match conversation {
            Some(id) => harness
                .conversation(id, cx)
                .await?
                .ok_or_else(|| SessionError::error(format!("Conversation {id} does not exist")))?,
            None => main_conversation(&harness, cx).await?,
        };
        fork_main_conversation(&harness, &source, at, cwd, cx).await
    }
    .await;
    // Close even when the fork failed; the fork error wins.
    let closed = harness.close(&without_abort_signal(cx)).await;
    let fork = forked?;
    closed?;
    Ok(fork.id())
}

/// The Harness options of the fork: nothing runs, so no models and only the
/// built-in tasks (forks copy documents without their definitions).
fn harness_options() -> HarnessOptions {
    HarnessOptions::new(
        create_models(CreateModelsOptions::default()),
        Arc::new(create_registry()),
    )
}

fn io<'a>(action: &'static str, path: &'a Path) -> impl FnOnce(std::io::Error) -> ForkError + 'a {
    move |source| ForkError::Io {
        action,
        path: path.to_owned(),
        source,
    }
}
