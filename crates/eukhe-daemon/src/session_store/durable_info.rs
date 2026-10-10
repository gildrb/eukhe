//! The list metadata of a durable session storage (`<sessions_dir>/<id>/`):
//! the [`SessionInfo`] the legacy fold derives from a `.jsonl` file, read
//! from the storage's main conversation and its `eukhe.daemon.session`
//! document through read-only views (the session may be live in another
//! process). Every commit appends a marker to the storage's `main.jsonl`,
//! so a row is cached per storage on that file's generation.
//!
//! The storage readers are async; the sync catalog surface
//! ([`super::read_session_info`], the roster scan) runs them on a reader
//! thread with its own current-thread runtime, which is legal from any
//! caller (plain threads, blocking-pool threads, and async tasks alike).

use std::collections::HashMap;
use std::future::Future;
use std::path::{Path, PathBuf};
use std::sync::{LazyLock, Mutex, PoisonError};
use std::time::SystemTime;

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_core::durable::{read_main_transcript, read_session_document, SessionLocation};
use eukhe_durable::entries::{ASSISTANT_ENTRY, TOOL_RESULT_ENTRY, USER_ENTRY};
use eukhe_types::pi_ai::Message;

use super::info::{
    append_capped_search_text, SessionInfo, SessionInfoGeneration,
    SESSION_LIST_SEARCH_TEXT_MAX_CHARS, SESSION_SCAN_MAX_CACHED_STATES,
};
use crate::session_usage::SessionUsageSummary;
use crate::worker::durable_host::meta::SESSION_META_DOC;

/// The durable storage's commit log; a directory without it is no session.
const MAIN_FILE: &str = "main.jsonl";

/// Whether `dir` holds a durable session storage.
#[must_use]
pub(crate) fn is_durable_storage(dir: &Path) -> bool {
    dir.join(MAIN_FILE).is_file()
}

/// The durable storage a session path names: the directory itself, or the
/// imported `<stem>/` sibling of a legacy `<stem>.jsonl` path. `None` when
/// no storage exists there (a legacy file not imported yet, or nothing).
#[must_use]
pub(crate) fn durable_storage_of(path: &Path) -> Option<PathBuf> {
    let dir = SessionLocation::from_path(path.to_path_buf()).storage_dir();
    is_durable_storage(&dir).then_some(dir)
}

/// The newest mtime among the files of a storage directory (its recency:
/// the commit log and the sidecars a commit writes).
#[must_use]
pub(crate) fn storage_modified(dir: &Path) -> Option<SystemTime> {
    std::fs::read_dir(dir)
        .ok()?
        .flatten()
        .filter_map(|entry| entry.metadata().ok())
        .filter(std::fs::Metadata::is_file)
        .filter_map(|metadata| metadata.modified().ok())
        .max()
}

/// Run one storage operation to completion on a helper thread with its own
/// current-thread runtime (legal from plain threads, blocking-pool threads,
/// and async tasks alike). Errs when the runtime cannot start.
pub(crate) fn block_on_storage<T: Send>(
    operation: impl Future<Output = T> + Send,
) -> std::io::Result<T> {
    std::thread::scope(|scope| {
        scope
            .spawn(|| {
                tokio::runtime::Builder::new_current_thread()
                    .enable_all()
                    .build()
                    .map(|runtime| runtime.block_on(operation))
            })
            .join()
    })
    .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
}

/// [`read_durable_session_info`] from sync code.
#[must_use]
pub(crate) fn read_durable_session_info_blocking(dir: &Path) -> Option<SessionInfo> {
    block_on_storage(read_durable_session_info(dir, &BACKGROUND_CONTEXT))
        .map_err(|error| {
            eprintln!("eukhe-daemon: starting a session storage reader failed: {error}");
        })
        .ok()
        .flatten()
}

/// One cached row: the commit-log generation it was read at.
struct CachedInfo {
    generation: SessionInfoGeneration,
    info: SessionInfo,
    /// Insertion ordinal: the bound evicts the oldest row.
    ordinal: u64,
}

#[derive(Default)]
struct DurableInfoCache {
    rows: HashMap<PathBuf, CachedInfo>,
    next_ordinal: u64,
}

impl DurableInfoCache {
    fn get(&self, dir: &Path, generation: &SessionInfoGeneration) -> Option<SessionInfo> {
        self.rows
            .get(dir)
            .filter(|cached| cached.generation == *generation)
            .map(|cached| cached.info.clone())
    }

    fn store(&mut self, dir: PathBuf, generation: SessionInfoGeneration, info: SessionInfo) {
        let ordinal = self.next_ordinal;
        self.next_ordinal += 1;
        self.rows.insert(
            dir,
            CachedInfo {
                generation,
                info,
                ordinal,
            },
        );
        if self.rows.len() > SESSION_SCAN_MAX_CACHED_STATES {
            let oldest = self
                .rows
                .iter()
                .min_by_key(|(_, cached)| cached.ordinal)
                .map(|(dir, _)| dir.clone());
            if let Some(oldest) = oldest {
                self.rows.remove(&oldest);
            }
        }
    }
}

/// The per-storage rows, keyed by storage directory.
static DURABLE_INFO_CACHE: LazyLock<Mutex<DurableInfoCache>> =
    LazyLock::new(|| Mutex::new(DurableInfoCache::default()));

fn durable_info_cache() -> std::sync::MutexGuard<'static, DurableInfoCache> {
    DURABLE_INFO_CACHE
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
}

/// The list metadata of the durable storage in `dir`: the main
/// conversation's cwd, model, thinking level, and messages, the session
/// name, and the archived state (`archived` after a `kill`, else
/// `active`). `None` when `dir` holds no readable storage. A durable
/// storage records no RLM role, so the row is depth 0 without a parent.
pub(crate) async fn read_durable_session_info(dir: &Path, cx: &Context) -> Option<SessionInfo> {
    let generation =
        SessionInfoGeneration::from_metadata(&tokio::fs::metadata(dir.join(MAIN_FILE)).await.ok()?);
    if let Some(info) = durable_info_cache().get(dir, &generation) {
        return Some(info);
    }
    let location = SessionLocation::Durable(dir.to_path_buf());
    let transcript = match read_main_transcript(&location, cx).await {
        Ok(transcript) => transcript,
        Err(error) => {
            eprintln!(
                "eukhe-daemon: reading the session storage {} failed: {error}",
                dir.display()
            );
            return None;
        }
    };
    let meta = match read_session_document(&location, &SESSION_META_DOC, (), cx).await {
        Ok(meta) => meta.unwrap_or_default(),
        Err(error) => {
            eprintln!(
                "eukhe-daemon: reading the session metadata of {} failed: {error}",
                dir.display()
            );
            return None;
        }
    };
    let mut fold = TranscriptFold::default();
    for entry in &transcript.entries {
        let kind = entry.kind.as_str();
        if kind != USER_ENTRY.kind()
            && kind != ASSISTANT_ENTRY.kind()
            && kind != TOOL_RESULT_ENTRY.kind()
        {
            continue;
        }
        if let Some(message) = entry.model.as_deref().and_then(<[Message]>::first) {
            fold.message(message);
        }
    }
    let modified_ms = fold.last_activity_ms.or_else(|| {
        storage_modified(dir)
            .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
            .map(|duration| u64::try_from(duration.as_millis()).unwrap_or(u64::MAX))
    });
    let modified = modified_ms
        .map(crate::util::iso_from_unix_ms)
        .unwrap_or_default();
    let usage = fold.usage();
    let model = transcript
        .agent
        .model
        .map(|model| (model.provider, model.model_id))
        .or(fold.model);
    let info = SessionInfo {
        path: dir.to_path_buf(),
        id: dir
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default(),
        cwd: transcript.agent.cwd.unwrap_or_default(),
        name: meta
            .name
            .as_deref()
            .map(str::trim)
            .filter(|name| !name.is_empty())
            .map(str::to_string),
        state: Some(if meta.archived { "archived" } else { "active" }.to_string()),
        model,
        thinking_level: transcript
            .agent
            .thinking_level
            .map(|level| level.as_str().to_string()),
        parent_session_path: None,
        rlm_depth: 0,
        created: fold
            .first_activity_ms
            .or(modified_ms)
            .map(crate::util::iso_from_unix_ms)
            .unwrap_or_default(),
        modified,
        message_count: fold.message_count,
        first_message: if fold.first_message.is_empty() {
            "(no messages)".to_string()
        } else {
            fold.first_message
        },
        all_messages_text: fold.all_messages_text,
        usage,
        deleted_descendant_usage: None,
    };
    durable_info_cache().store(dir.to_path_buf(), generation, info.clone());
    Some(info)
}

/// The listing fold over the main conversation's model messages (the
/// legacy fold's `message` arm).
#[derive(Default)]
struct TranscriptFold {
    message_count: usize,
    first_message: String,
    all_messages_text: String,
    search_text_chars: usize,
    first_activity_ms: Option<u64>,
    last_activity_ms: Option<u64>,
    model: Option<(String, String)>,
    input_tokens: u64,
    output_tokens: u64,
    cost: f64,
}

impl TranscriptFold {
    fn message(&mut self, message: &Message) {
        self.message_count += 1;
        let timestamp = match message {
            Message::User(user) => user.timestamp,
            Message::Assistant(assistant) => {
                self.model = Some((assistant.provider.clone(), assistant.model.clone()));
                let usage = &assistant.usage;
                self.input_tokens = self
                    .input_tokens
                    .saturating_add(usage.input)
                    .saturating_add(usage.cache_read)
                    .saturating_add(usage.cache_write);
                self.output_tokens = self.output_tokens.saturating_add(usage.output);
                self.cost += usage.cost.total;
                assistant.timestamp
            }
            Message::System(_) | Message::ToolResult(_) => return,
        };
        if timestamp > 0 {
            self.first_activity_ms = Some(
                self.first_activity_ms
                    .map_or(timestamp, |first| first.min(timestamp)),
            );
            self.last_activity_ms = Some(
                self.last_activity_ms
                    .map_or(timestamp, |last| last.max(timestamp)),
            );
        }
        let text = serde_json::to_value(message)
            .map(|value| crate::types::content_to_text(&value["content"]))
            .unwrap_or_default();
        if matches!(message, Message::User(_)) && self.first_message.is_empty() {
            self.first_message.clone_from(&text);
        }
        if self.search_text_chars < SESSION_LIST_SEARCH_TEXT_MAX_CHARS {
            self.search_text_chars = append_capped_search_text(
                &mut self.all_messages_text,
                &text,
                self.search_text_chars,
            );
        }
    }

    /// TS `sessionUsageSummaryFrom` over the assistant usage: `None` when
    /// the session recorded no billable work.
    fn usage(&self) -> Option<SessionUsageSummary> {
        (self.input_tokens > 0 || self.output_tokens > 0 || self.cost != 0.0).then_some(
            SessionUsageSummary {
                input_tokens: self.input_tokens,
                output_tokens: self.output_tokens,
                cost: self.cost,
            },
        )
    }
}
