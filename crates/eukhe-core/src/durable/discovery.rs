//! Session listing and `--resume` resolution over a sessions directory that
//! holds durable storages (`<sessions_dir>/<id>/`) and legacy `<stem>.jsonl`
//! files not imported yet (a legacy file whose `<stem>/` directory exists is
//! that directory's session; the id of a legacy row is its stem, the name
//! of the storage it imports into). A durable session's cwd is its main conversation's
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
use super::staging::rule::{self, Form, Obs, Pick, Seen};
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

/// Every session of `sessions_dir`, newest first (then by id): durable
/// storages and the legacy files whose storage directory does not exist.
/// Sessions without a readable cwd are skipped, as the legacy scan skips
/// header-less files. The rule (which entry is a session, under which id,
/// and the order) runs as compiled Bend (`bend/listing.bend`,
/// [`rule::scan`], [`rule::rows`]); this reads the facts it needs.
pub async fn list_sessions(sessions_dir: &Path, cx: &Context) -> Vec<SessionListing> {
    let Ok(mut entries) = tokio::fs::read_dir(sessions_dir).await else {
        return Vec::new();
    };
    let mut listed: Vec<(PathBuf, Option<String>, Form)> = Vec::new();
    while let Ok(Some(entry)) = entries.next_entry().await {
        let Ok(file_type) = entry.file_type().await else {
            continue;
        };
        let path = entry.path();
        let form = if file_type.is_dir() {
            Form::Dir {
                main: is_file(&path.join(MAIN_FILE)).await,
            }
        } else if file_type.is_file() {
            Form::File
        } else {
            Form::Other
        };
        listed.push((path, entry.file_name().into_string().ok(), form));
    }
    let seens: Vec<Seen<'_>> = listed
        .iter()
        .map(|(_, name, form)| Seen {
            name: name.as_deref(),
            form: *form,
        })
        .collect();
    let picks = rule::scan(&seens);
    let candidates: Vec<(PathBuf, Pick)> = listed
        .iter()
        .zip(&picks)
        .map(|((path, _, _), pick)| (path.clone(), pick.clone()))
        .collect();
    let facts: Vec<(Option<String>, Vec<SystemTime>)> = futures::stream::iter(candidates)
        .map(|(path, pick)| candidate_facts(path, pick, cx))
        .buffered(LISTING_CONCURRENCY)
        .collect()
        .await;
    let obs: Vec<Obs<'_>> = seens
        .iter()
        .zip(&facts)
        .map(|(seen, (cwd, times))| Obs {
            seen: *seen,
            cwd: cwd.as_deref(),
            times: times.clone(),
        })
        .collect();
    // A row is a listed candidate at its place (laws/listing.bend,
    // `rows_are_entries`): its entry and its cwd are there.
    rule::rows(&obs)
        .into_iter()
        .filter_map(|row| {
            let (path, _, _) = listed.get(row.at)?;
            let cwd = facts.get(row.at)?.0.clone()?;
            let (id, location) = match row.pick {
                Pick::Store(id) => (id, SessionLocation::Durable(path.clone())),
                Pick::Legacy(id) => (id, SessionLocation::Legacy(path.clone())),
                Pick::Skip => return None,
            };
            Some(SessionListing {
                id,
                location,
                cwd,
                modified: row.time,
            })
        })
        .collect()
}

/// What the listing reads of a session candidate: its cwd (`None`: it does
/// not read) and the modification times of its files (a storage: every
/// file in it; a legacy file: the file). Nothing of an entry the scan skips.
async fn candidate_facts(
    path: PathBuf,
    pick: Pick,
    cx: &Context,
) -> (Option<String>, Vec<SystemTime>) {
    match pick {
        Pick::Skip => (None, Vec::new()),
        Pick::Store(_) => (read_durable_cwd(&path, cx).await, file_times(&path).await),
        Pick::Legacy(_) => {
            let modified = tokio::fs::metadata(&path)
                .await
                .ok()
                .and_then(|metadata| metadata.modified().ok());
            (read_legacy_cwd(path).await, modified.into_iter().collect())
        }
    }
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

async fn read_legacy_cwd(file: PathBuf) -> Option<String> {
    tokio::task::spawn_blocking(move || read_session_header(&file))
        .await
        .ok()?
        .map(|header| header.cwd)
}

/// The modification times of the files of `dir`.
async fn file_times(dir: &Path) -> Vec<SystemTime> {
    let Ok(mut entries) = tokio::fs::read_dir(dir).await else {
        return Vec::new();
    };
    let mut times = Vec::new();
    while let Ok(Some(entry)) = entries.next_entry().await {
        let Ok(metadata) = entry.metadata().await else {
            continue;
        };
        if !metadata.is_file() {
            continue;
        }
        if let Ok(modified) = metadata.modified() {
            times.push(modified);
        }
    }
    times
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
