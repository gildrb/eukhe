//! The legacy-file load (read-only): parse a session file's entries and
//! keep them only when the first row is a valid session header. A torn
//! tail line is skipped by the parser; the file itself is never rewritten.

use super::{parse_session_entries, FileEntry, Path};

/// Load entries from a session file; empty when the file is missing,
/// unreadable, or does not lead with a session header.
#[must_use]
pub fn load_entries_from_file(file_path: &Path) -> Vec<FileEntry> {
    let Ok(content) = std::fs::read_to_string(file_path) else {
        return Vec::new();
    };
    let entries = parse_session_entries(&content);
    match entries.first() {
        Some(FileEntry::Header { .. }) => entries,
        _ => Vec::new(),
    }
}
