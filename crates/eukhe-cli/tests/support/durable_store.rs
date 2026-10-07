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
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("runtime");
    let transcript = runtime
        .block_on(read_main_transcript(
            &SessionLocation::Durable(dir.to_path_buf()),
            &BACKGROUND_CONTEXT,
        ))
        .unwrap_or_else(|error| panic!("read {}: {error}", dir.display()));
    Transcript {
        agent: serde_json::to_value(&transcript.agent).expect("agent JSON"),
        entries: transcript
            .entries
            .iter()
            .map(|entry| serde_json::to_value(entry).expect("entry JSON"))
            .collect(),
    }
}
