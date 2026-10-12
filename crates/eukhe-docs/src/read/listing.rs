//! Directory reads: one level, directories first, then files with sizes.

use std::fmt::Write as _;
use std::path::Path;

/// One directory entry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DirEntry {
    pub name: String,
    pub is_dir: bool,
    /// File size in bytes; `None` for directories.
    pub size: Option<u64>,
}

pub(super) fn list(directory: &Path) -> std::io::Result<Vec<DirEntry>> {
    let mut entries = Vec::new();
    for entry in std::fs::read_dir(directory)? {
        let entry = entry?;
        let metadata = entry.metadata()?;
        entries.push(DirEntry {
            name: entry.file_name().to_string_lossy().into_owned(),
            is_dir: metadata.is_dir(),
            size: (!metadata.is_dir()).then_some(metadata.len()),
        });
    }
    entries.sort_by(|a, b| b.is_dir.cmp(&a.is_dir).then_with(|| a.name.cmp(&b.name)));
    Ok(entries)
}

pub(super) fn render(entries: &[DirEntry]) -> String {
    if entries.is_empty() {
        return "(empty directory)".to_owned();
    }
    let mut out = String::new();
    for entry in entries {
        if !out.is_empty() {
            out.push('\n');
        }
        match entry.size {
            Some(size) => {
                let _infallible = write!(out, "{} ({})", entry.name, super::format_bytes(size));
            }
            None => {
                let _infallible = write!(out, "{}/", entry.name);
            }
        }
    }
    out
}
