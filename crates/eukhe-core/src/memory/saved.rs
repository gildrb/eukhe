//! The chat's saved state beside its logs: `view.json`, the live view as
//! `[l, i]` pairs (§1, §3.2: a cache of the fold of the logs, saved on
//! every change), and `prompt.json`, the
//! turns' system prompt and tools that compactions reuse (§4). Each file is
//! replaced atomically: written to a temporary file, fsynced, renamed over
//! the old one, and the directory fsynced.

use std::fs::{self, File};
use std::io::{self, Write};
use std::path::Path;

use eukhe_types::pi_ai::Tool;

use super::view::Part;

/// The saved view.
pub(crate) const VIEW_FILE: &str = "view.json";
/// The saved compaction prompt.
pub(crate) const PROMPT_FILE: &str = "prompt.json";

/// What every compaction sends before its view: the turns' system prompt
/// and tools, verbatim, so a compaction reads them from the turns' cache
/// entry (§4). The tools are declared, never called.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CompactionPrompt {
    pub system: String,
    pub tools: Vec<Tool>,
}

impl CompactionPrompt {
    /// The prompt before any turn has reported its own: the memory layer
    /// alone (§5's prompt), without tools.
    #[must_use]
    pub fn memory_layer() -> CompactionPrompt {
        CompactionPrompt {
            system: super::memory_system_layer(),
            tools: Vec::new(),
        }
    }
}

/// The saved view's parts, `None` when the chat has never saved one.
///
/// # Errors
///
/// Returns an error when the file exists but cannot be read or parsed.
pub(crate) fn load_view(dir: &Path) -> io::Result<Option<Vec<Part>>> {
    let Some(bytes) = read_optional(&dir.join(VIEW_FILE))? else {
        return Ok(None);
    };
    let pairs: Vec<(u32, u64)> = serde_json::from_slice(&bytes)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    Ok(Some(
        pairs.into_iter().map(|(l, i)| Part { l, i }).collect(),
    ))
}

/// Replace the saved view.
///
/// # Errors
///
/// Returns an error when the file cannot be written, synced or renamed.
pub(crate) fn save_view(dir: &Path, parts: &[Part]) -> io::Result<()> {
    let pairs: Vec<(u32, u64)> = parts.iter().map(|part| (part.l, part.i)).collect();
    let bytes = serde_json::to_vec(&pairs).map_err(io::Error::other)?;
    write_atomic(dir, VIEW_FILE, &bytes)
}

/// The saved compaction prompt, `None` before any turn reported one.
///
/// # Errors
///
/// Returns an error when the file exists but cannot be read or parsed.
pub(crate) fn load_prompt(dir: &Path) -> io::Result<Option<CompactionPrompt>> {
    let Some(bytes) = read_optional(&dir.join(PROMPT_FILE))? else {
        return Ok(None);
    };
    serde_json::from_slice(&bytes)
        .map(Some)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
}

/// Replace the saved compaction prompt.
///
/// # Errors
///
/// Returns an error when the file cannot be written, synced or renamed.
pub(crate) fn save_prompt(dir: &Path, prompt: &CompactionPrompt) -> io::Result<()> {
    let bytes = serde_json::to_vec(prompt).map_err(io::Error::other)?;
    write_atomic(dir, PROMPT_FILE, &bytes)
}

fn read_optional(path: &Path) -> io::Result<Option<Vec<u8>>> {
    match fs::read(path) {
        Ok(bytes) => Ok(Some(bytes)),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(error),
    }
}

/// Temp file + fsync + rename + directory fsync: a crash leaves the old
/// file or the new one, never half of either.
fn write_atomic(dir: &Path, name: &str, bytes: &[u8]) -> io::Result<()> {
    let temp = dir.join(format!(".{name}.tmp"));
    let mut file = File::create(&temp)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    drop(file);
    fs::rename(&temp, dir.join(name))?;
    File::open(dir)?.sync_all()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The loaded view is the saved one, and an unsaved chat has none.
    #[test]
    fn a_saved_view_loads_back_unchanged() {
        let dir = tempfile::tempdir().unwrap();
        let parts = vec![
            Part { l: 3, i: 0 },
            Part { l: 1, i: 4 },
            Part { l: 0, i: 10 },
        ];
        let before = load_view(dir.path()).unwrap();
        save_view(dir.path(), &parts).unwrap();
        assert_eq!(
            (
                before,
                load_view(dir.path()).unwrap(),
                fs::read_to_string(dir.path().join(VIEW_FILE)).unwrap(),
                dir.path().join(format!(".{VIEW_FILE}.tmp")).exists()
            ),
            (None, Some(parts), "[[3,0],[1,4],[0,10]]".to_string(), false)
        );
    }

    #[test]
    fn a_saved_prompt_loads_back_unchanged() {
        let dir = tempfile::tempdir().unwrap();
        let prompt = CompactionPrompt {
            system: "You are Eukhe.".to_string(),
            tools: vec![serde_json::from_value(serde_json::json!({
                "name": "zoom",
                "description": "Open a line.",
                "parameters": {"type": "object", "properties": {}}
            }))
            .unwrap()],
        };
        save_prompt(dir.path(), &prompt).unwrap();
        assert_eq!(load_prompt(dir.path()).unwrap(), Some(prompt));
    }
}
