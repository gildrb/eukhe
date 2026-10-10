//! Durable session storages for the CLI e2e tests: the sessions a run left
//! under `<sessions>/<id>/` and the main conversation's transcript, read
//! through `eukhe_core::durable::read_main_transcript` (the read-only
//! storage path the session listing uses).

#![allow(dead_code)] // each including test binary uses its own subset

use std::path::{Path, PathBuf};

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::{read_main_transcript, SessionLocation};

/// The durable session storages in `sessions_dir` (directories holding a
/// `main.jsonl`), sorted by path.
pub fn session_dirs(sessions_dir: &Path) -> Vec<PathBuf> {
    let mut dirs: Vec<PathBuf> = std::fs::read_dir(sessions_dir)
        .map(|entries| {
            entries
                .flatten()
                .map(|entry| entry.path())
                .filter(|path| path.join("main.jsonl").is_file())
                .collect()
        })
        .unwrap_or_default();
    dirs.sort();
    dirs
}

/// One stored session's main conversation: its agent (`pi.agent`) and its
/// entries oldest-first, as JSON.
pub struct Transcript {
    pub agent: serde_json::Value,
    pub entries: Vec<serde_json::Value>,
}

impl Transcript {
    /// The text of every model message, in order (user prompts, assistant
    /// answers, custom rows that reach the model).
    pub fn message_texts(&self) -> Vec<String> {
        self.entries
            .iter()
            .filter_map(|entry| entry["model"].as_array())
            .flatten()
            .filter_map(|message| match &message["content"] {
                serde_json::Value::String(text) => Some(text.clone()),
                serde_json::Value::Array(blocks) => blocks
                    .iter()
                    .find_map(|block| block["text"].as_str().map(str::to_owned)),
                _ => None,
            })
            .collect()
    }

    /// The text of every user and assistant message, in order (the chat
    /// rows, without the custom rows such as the harness digest).
    pub fn chat_texts(&self) -> Vec<String> {
        self.entries
            .iter()
            .filter_map(|entry| entry["model"].as_array())
            .flatten()
            .filter(|message| message["role"] == "user" || message["role"] == "assistant")
            .filter_map(|message| match &message["content"] {
                serde_json::Value::String(text) => Some(text.clone()),
                serde_json::Value::Array(blocks) => blocks
                    .iter()
                    .find_map(|block| block["text"].as_str().map(str::to_owned)),
                _ => None,
            })
            .collect()
    }

    /// The entries of `kind` (`pi.user`, `pi.assistant`, `eukhe.custom`, ...).
    pub fn of_kind(&self, kind: &str) -> Vec<&serde_json::Value> {
        self.entries
            .iter()
            .filter(|entry| entry["kind"] == kind)
            .collect()
    }

    /// The `eukhe.custom` rows of `custom_type` (their `data`).
    pub fn custom_rows(&self, custom_type: &str) -> Vec<&serde_json::Value> {
        self.of_kind("eukhe.custom")
            .into_iter()
            .map(|entry| &entry["data"])
            .filter(|data| data["customType"] == custom_type)
            .collect()
    }
}

/// Read the main transcript of the durable storage `dir`.
///
/// # Panics
///
/// When the storage cannot be read.
pub fn read_transcript(dir: &Path) -> Transcript {
    load_transcript(dir).unwrap_or_else(|error| panic!("read {}: {error}", dir.display()))
}

/// The main transcript of the durable storage `dir`, `None` while it cannot
/// be read (not created yet), for a poll that waits on a live session.
pub fn try_read_transcript(dir: &Path) -> Option<Transcript> {
    load_transcript(dir).ok()
}

/// The durable storage a legacy session file imports into on its first
/// open (`<sessions>/<stem>/`).
pub fn legacy_storage(file: &Path) -> PathBuf {
    SessionLocation::Legacy(file.to_path_buf()).storage_dir()
}

/// Whether one of the durable storage `dir`'s JSONL files carries `needle`
/// (a document value the transcript read does not surface, such as the
/// `eukhe.daemon.session` name).
pub fn storage_contains(dir: &Path, needle: &str) -> bool {
    std::fs::read_dir(dir).is_ok_and(|mut entries| {
        entries.any(|entry| {
            entry.is_ok_and(|entry| {
                let path = entry.path();
                path.extension()
                    .is_some_and(|extension| extension == "jsonl")
                    && std::fs::read_to_string(&path).is_ok_and(|content| content.contains(needle))
            })
        })
    })
}

/// The read runs its own runtime on a scoped thread, so async tests (whose
/// runtime already drives the calling thread) can read too.
fn load_transcript(dir: &Path) -> Result<Transcript, String> {
    let transcript = std::thread::scope(|scope| {
        scope
            .spawn(|| {
                tokio::runtime::Builder::new_current_thread()
                    .enable_all()
                    .build()
                    .expect("runtime")
                    .block_on(read_main_transcript(
                        &SessionLocation::Durable(dir.to_path_buf()),
                        &BACKGROUND_CONTEXT,
                    ))
            })
            .join()
            .expect("the transcript read thread")
    })
    .map_err(|error| error.to_string())?;
    Ok(Transcript {
        agent: serde_json::to_value(&transcript.agent).expect("agent JSON"),
        entries: transcript
            .entries
            .iter()
            .map(|entry| serde_json::to_value(entry).expect("entry JSON"))
            .collect(),
    })
}
