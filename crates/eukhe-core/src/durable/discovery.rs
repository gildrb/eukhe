//! Session listing and `--resume` resolution over a sessions directory that
//! holds durable storages (`<sessions_dir>/<id>/`) and legacy `<id>.jsonl`
//! files not imported yet (a legacy file whose `<id>/` directory exists is
//! the durable session). A durable session's cwd is its main conversation's
//! `pi.agent` cwd, read through a view that never writes (the session may be
//! open in another process); its recency is the newest file mtime in its
//! directory. Selector tiers and messages are those of
//! [`crate::session::discovery::resolve_session_path`].

mod read_only;
#[cfg(test)]
pub(super) mod tests;

use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::SystemTime;

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, JsonValue};
use eukhe_durable::documents::DocToken;
use eukhe_durable::errors::StorageError;
use eukhe_durable::harness::agent::AGENT_DOC;
use eukhe_durable::harness::types::AgentState;
use eukhe_durable::session::{Session, SessionError, SessionResult};
use eukhe_durable::types::{
    ConversationId, EntryQuery, EntryRecord, Storage, ROOT_CONVERSATION_ID,
};
use futures::StreamExt;

use super::main_conversation::{SessionState, SESSION_DOC};
use crate::session::discovery::{
    looks_like_session_path, match_saved_session, session_cwd_matches, SavedSessionMatch,
    SessionSelectorError,
};
use crate::session::manager::read_session_header;

/// The durable storage's commit log; a directory without it is no session.
const MAIN_FILE: &str = "main.jsonl";
const LEGACY_EXTENSION: &str = "jsonl";
/// Storages read at once while listing.
const LISTING_CONCURRENCY: usize = 8;

/// One listed session: a durable storage dir, or a legacy file not imported
/// yet.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SessionLocation {
    /// `<sessions_dir>/<id>/`.
    Durable(PathBuf),
    /// `<sessions_dir>/<id>.jsonl`.
    Legacy(PathBuf),
}

impl SessionLocation {
    /// The location a session path names: a directory or a non-`.jsonl`
    /// path is a durable storage (an existing one or one to create), a
    /// `.jsonl` file a legacy session.
    #[must_use]
    pub fn from_path(path: PathBuf) -> Self {
        let legacy = path
            .extension()
            .is_some_and(|extension| extension.eq_ignore_ascii_case(LEGACY_EXTENSION));
        if legacy && !path.is_dir() {
            Self::Legacy(path)
        } else {
            Self::Durable(path)
        }
    }

    /// The durable directory or legacy file.
    #[must_use]
    pub fn path(&self) -> &Path {
        match self {
            Self::Durable(path) | Self::Legacy(path) => path,
        }
    }

    /// The storage directory this location opens as: the durable directory,
    /// or the legacy file's `<stem>/` sibling (where `open_session` imports
    /// it).
    #[must_use]
    pub fn storage_dir(&self) -> PathBuf {
        match self {
            Self::Durable(dir) => dir.clone(),
            Self::Legacy(file) => file.with_extension(""),
        }
    }
}

/// One saved session of a sessions directory.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SessionListing {
    pub id: String,
    pub location: SessionLocation,
    pub cwd: String,
    pub modified: SystemTime,
}

impl SessionListing {
    /// The durable directory the session opens as: its storage, or
    /// `<sessions_dir>/<id>/` for a legacy file (imported on open).
    #[must_use]
    pub fn storage_dir(&self, sessions_dir: &Path) -> PathBuf {
        match &self.location {
            SessionLocation::Durable(dir) => dir.clone(),
            SessionLocation::Legacy(_) => sessions_dir.join(&self.id),
        }
    }
}

/// Where a selector resolved to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolvedListing {
    /// The selector was path-like and is used as-is.
    Path(SessionLocation),
    /// A saved session whose cwd matches the current one.
    Local(SessionListing),
    /// A saved session belonging to a different project.
    Global(SessionListing),
}

/// Every session of `sessions_dir`, newest first: durable storages and the
/// legacy files whose storage directory does not exist. Sessions without a
/// readable cwd are skipped, as the legacy scan skips header-less files.
pub async fn list_sessions(sessions_dir: &Path, cx: &Context) -> Vec<SessionListing> {
    let Ok(mut entries) = tokio::fs::read_dir(sessions_dir).await else {
        return Vec::new();
    };
    let mut durable = Vec::new();
    let mut legacy = Vec::new();
    while let Ok(Some(entry)) = entries.next_entry().await {
        let Ok(file_type) = entry.file_type().await else {
            continue;
        };
        let path = entry.path();
        if file_type.is_dir() {
            let hidden = entry.file_name().to_string_lossy().starts_with('.');
            if !hidden && is_file(&path.join(MAIN_FILE)).await {
                durable.push(path);
            }
        } else if file_type.is_file()
            && path
                .extension()
                .is_some_and(|extension| extension == LEGACY_EXTENSION)
        {
            legacy.push(path);
        }
    }

    let mut listings: Vec<SessionListing> = futures::stream::iter(durable)
        .map(|dir| durable_listing(dir, cx))
        .buffer_unordered(LISTING_CONCURRENCY)
        .filter_map(futures::future::ready)
        .collect()
        .await;
    for file in legacy {
        if let Some(listing) = legacy_listing(sessions_dir, file).await {
            listings.push(listing);
        }
    }
    listings.sort_by(|left, right| {
        right
            .modified
            .cmp(&left.modified)
            .then_with(|| left.id.cmp(&right.id))
    });
    listings
}

/// The newest session of `sessions_dir` whose cwd is `cwd`.
pub async fn most_recent_session_for_cwd(
    sessions_dir: &Path,
    cwd: &Path,
    cx: &Context,
) -> Option<SessionListing> {
    list_sessions(sessions_dir, cx)
        .await
        .into_iter()
        .find(|listing| session_cwd_matches(&listing.cwd, cwd))
}

/// Resolve a `--resume` selector: a path-like selector names a location
/// as-is ([`SessionLocation::from_path`]); otherwise exact, then partial id
/// matches, each local (same cwd) first, then global.
///
/// # Errors
///
/// [`SessionSelectorError::Ambiguous`] when a match tier holds several
/// sessions, [`SessionSelectorError::NotFound`] when none matches.
pub async fn resolve_session(
    selector: &str,
    cwd: &Path,
    sessions_dir: &Path,
    cx: &Context,
) -> Result<ResolvedListing, SessionSelectorError> {
    if looks_like_session_path(selector) {
        return Ok(ResolvedListing::Path(SessionLocation::from_path(
            PathBuf::from(selector),
        )));
    }
    let listings = list_sessions(sessions_dir, cx).await;
    let matched = match_saved_session(
        selector,
        &listings,
        |listing| listing.id.as_str(),
        |listing| session_cwd_matches(&listing.cwd, cwd),
    )?;
    Ok(match matched {
        SavedSessionMatch::Local(listing) => ResolvedListing::Local(listing.clone()),
        SavedSessionMatch::Global(listing) => ResolvedListing::Global(listing.clone()),
    })
}

/// The session's cwd: the main conversation's `pi.agent` cwd of a durable
/// storage (also of a legacy file already imported), else the legacy
/// header's cwd. `None` when it cannot be read.
pub async fn read_session_cwd(location: &SessionLocation, cx: &Context) -> Option<String> {
    match location {
        SessionLocation::Durable(dir) => read_durable_cwd(dir, cx).await,
        SessionLocation::Legacy(file) => {
            let storage_dir = location.storage_dir();
            if tokio::fs::try_exists(&storage_dir).await.unwrap_or(false) {
                read_durable_cwd(&storage_dir, cx).await
            } else {
                read_legacy_cwd(file.clone()).await
            }
        }
    }
}

async fn is_file(path: &Path) -> bool {
    tokio::fs::metadata(path)
        .await
        .is_ok_and(|metadata| metadata.is_file())
}

async fn durable_listing(dir: PathBuf, cx: &Context) -> Option<SessionListing> {
    let id = dir.file_name()?.to_str()?.to_owned();
    let cwd = read_durable_cwd(&dir, cx).await?;
    if cwd.is_empty() {
        return None;
    }
    let modified = newest_mtime(&dir).await?;
    Some(SessionListing {
        id,
        location: SessionLocation::Durable(dir),
        cwd,
        modified,
    })
}

async fn legacy_listing(sessions_dir: &Path, file: PathBuf) -> Option<SessionListing> {
    let header = {
        let file = file.clone();
        tokio::task::spawn_blocking(move || read_session_header(&file))
            .await
            .ok()??
    };
    if header.cwd.is_empty()
        || tokio::fs::try_exists(sessions_dir.join(&header.id))
            .await
            .unwrap_or(true)
    {
        return None;
    }
    let modified = tokio::fs::metadata(&file).await.ok()?.modified().ok()?;
    Some(SessionListing {
        id: header.id,
        location: SessionLocation::Legacy(file),
        cwd: header.cwd,
        modified,
    })
}

async fn read_legacy_cwd(file: PathBuf) -> Option<String> {
    tokio::task::spawn_blocking(move || read_session_header(&file))
        .await
        .ok()?
        .map(|header| header.cwd)
}

/// The newest mtime among the files of `dir`.
async fn newest_mtime(dir: &Path) -> Option<SystemTime> {
    let mut entries = tokio::fs::read_dir(dir).await.ok()?;
    let mut newest: Option<SystemTime> = None;
    while let Ok(Some(entry)) = entries.next_entry().await {
        let Ok(metadata) = entry.metadata().await else {
            continue;
        };
        if !metadata.is_file() {
            continue;
        }
        if let Ok(modified) = metadata.modified() {
            newest = Some(newest.map_or(modified, |newest| newest.max(modified)));
        }
    }
    newest
}

/// The main conversation of a session, as [`read_main_transcript`] reads
/// it.
#[derive(Debug, Clone, PartialEq)]
pub struct MainTranscript {
    pub main: ConversationId,
    /// The main conversation's `pi.agent` (default when absent).
    pub agent: AgentState,
    /// The main conversation's fork-aware history, oldest first.
    pub entries: Vec<EntryRecord>,
}

/// Why [`read_main_transcript`] failed.
#[derive(Debug, thiserror::Error)]
pub enum DiscoveryError {
    #[error("no durable session storage at {}", path.display())]
    NotDurable { path: PathBuf },
    #[error("session storage path {} is not UTF-8", path.display())]
    NotUtf8 { path: PathBuf },
    #[error(transparent)]
    Storage(#[from] StorageError),
    #[error(transparent)]
    Session(#[from] SessionError),
}

/// Entries read per storage scan.
const ENTRY_PAGE_SIZE: usize = 256;

/// The main conversation, its agent, and its history, read through a view
/// that never writes (the session may be open in another process). A legacy
/// location reads its imported storage.
///
/// # Errors
///
/// The location has no durable storage (a legacy file not imported yet),
/// or reading the storage fails.
pub async fn read_main_transcript(
    location: &SessionLocation,
    cx: &Context,
) -> Result<MainTranscript, DiscoveryError> {
    let dir = location.storage_dir();
    let (session, storage) = open_view(&dir, cx).await?;
    let read = async {
        let (main, agent) = main_agent(&session, cx).await?;
        let query = EntryQuery::new(main);
        let mut entries = Vec::new();
        let mut cursor = None;
        loop {
            let page = storage
                .scan_entries(&query, ENTRY_PAGE_SIZE, cursor.as_ref(), cx)
                .await?;
            entries.extend(page.items);
            match page.next {
                Some(next) => cursor = Some(next),
                None => break,
            }
        }
        entries.reverse();
        Ok::<_, DiscoveryError>(MainTranscript {
            main,
            agent: agent.unwrap_or_default(),
            entries,
        })
    }
    .await;
    close_view(&session, &dir, cx).await;
    read
}

/// One document of a session's storage, decoded, read through a view that
/// never writes (the session may be open in another process). A legacy
/// location reads its imported storage. `None` when the document is
/// absent.
///
/// # Errors
///
/// The location has no durable storage (a legacy file not imported yet),
/// or reading or decoding the document fails.
pub async fn read_session_document<D: DocToken>(
    location: &SessionLocation,
    token: &D,
    locator: D::Locator<'_>,
    cx: &Context,
) -> Result<Option<D::Value>, DiscoveryError> {
    let dir = location.storage_dir();
    let (session, _) = open_view(&dir, cx).await?;
    let read = match session.snapshot(token, locator, cx).await {
        Ok(Some(value)) => from_json(&JsonValue::Object(value))
            .map(Some)
            .map_err(|error| DiscoveryError::Session(SessionError::other(error))),
        Ok(None) => Ok(None),
        Err(error) => Err(DiscoveryError::Session(error)),
    };
    close_view(&session, &dir, cx).await;
    read
}

async fn read_durable_cwd(dir: &Path, cx: &Context) -> Option<String> {
    let (session, _) = match open_view(dir, cx).await {
        Ok(view) => view,
        Err(error) => {
            tracing::debug!(dir = %dir.display(), error = %error, "unreadable session storage");
            return None;
        }
    };
    let agent = main_agent(&session, cx).await;
    close_view(&session, dir, cx).await;
    match agent {
        Ok((_, agent)) => agent?.cwd,
        Err(error) => {
            tracing::debug!(dir = %dir.display(), error = %error, "unreadable session cwd");
            None
        }
    }
}

/// A read-only Session over the storage in `dir`, and the storage.
async fn open_view(
    dir: &Path,
    cx: &Context,
) -> Result<(Session, Arc<dyn Storage>), DiscoveryError> {
    if !is_file(&dir.join(MAIN_FILE)).await {
        return Err(DiscoveryError::NotDurable {
            path: dir.to_owned(),
        });
    }
    let directory = dir.to_str().ok_or_else(|| DiscoveryError::NotUtf8 {
        path: dir.to_owned(),
    })?;
    let storage: Arc<dyn Storage> = Arc::new(read_only::open_read_only(directory, cx).await?);
    Ok((Session::new(Arc::clone(&storage)), storage))
}

async fn close_view(session: &Session, dir: &Path, cx: &Context) {
    if let Err(error) = session.close(cx).await {
        tracing::debug!(dir = %dir.display(), error = %error, "closing a session storage view");
    }
}

/// The main conversation (`eukhe.session.main`, else the root) and its
/// `pi.agent`.
async fn main_agent(
    session: &Session,
    cx: &Context,
) -> SessionResult<(ConversationId, Option<AgentState>)> {
    let main = match session.snapshot(&SESSION_DOC, (), cx).await? {
        Some(value) => {
            let state: SessionState =
                from_json(&JsonValue::Object(value)).map_err(SessionError::other)?;
            state.main.unwrap_or(ROOT_CONVERSATION_ID)
        }
        None => ROOT_CONVERSATION_ID,
    };
    let agent = match session.snapshot(&AGENT_DOC, main, cx).await? {
        Some(value) => Some(from_json(&JsonValue::Object(value)).map_err(SessionError::other)?),
        None => None,
    };
    Ok((main, agent))
}
