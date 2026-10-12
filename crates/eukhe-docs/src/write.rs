//! Locked, atomic writes. Every writer of a path takes an OS lock on
//! `<lock dir>/<xxh64 of the canonical path>.lock` (shared by every session
//! and process of one eukhe home), then replaces the file through a
//! same-directory temporary file: write, fsync, rename, fsync the
//! directory. The mode of a replaced file is kept.

use std::fs::{File, OpenOptions, Permissions};
use std::io::Write as _;
use std::os::unix::fs::PermissionsExt as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use twox_hash::XxHash64;

use crate::store::EditStore;
use crate::text::{detect_line_ending, normalize_to_lf, restore_line_endings, strip_bom};

/// An exclusive lock on one canonical path; released on drop.
#[derive(Debug)]
pub(crate) struct PathLock {
    _file: File,
}

/// Block until this process holds the lock of `canonical`.
pub(crate) fn lock(lock_dir: &Path, canonical: &Path) -> std::io::Result<PathLock> {
    std::fs::create_dir_all(lock_dir)?;
    let key = XxHash64::oneshot(0, canonical.as_os_str().as_encoded_bytes());
    let file = OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(lock_dir.join(format!("{key:016x}.lock")))?;
    file.lock()?;
    Ok(PathLock { _file: file })
}

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Replace `target` with `bytes` atomically; `permissions` applies to the
/// new file (the replaced file's, or the creation mode).
pub(crate) fn replace_atomic(
    target: &Path,
    bytes: &[u8],
    permissions: Option<Permissions>,
) -> std::io::Result<()> {
    let directory = target.parent().unwrap_or(Path::new("."));
    let name = target
        .file_name()
        .map_or_else(String::new, |name| name.to_string_lossy().into_owned());
    let temp = directory.join(format!(
        ".{name}.eukhe-tmp-{}-{}",
        std::process::id(),
        TEMP_COUNTER.fetch_add(1, Ordering::Relaxed)
    ));
    let written = write_synced(&temp, bytes, permissions)
        .and_then(|()| std::fs::rename(&temp, target))
        .and_then(|()| File::open(directory)?.sync_all());
    if written.is_err() {
        // The temporary file may not exist; the write error is the one to report.
        let _cleanup = std::fs::remove_file(&temp);
    }
    written
}

fn write_synced(
    path: &Path,
    bytes: &[u8],
    permissions: Option<Permissions>,
) -> std::io::Result<()> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
    file.write_all(bytes)?;
    if let Some(permissions) = permissions {
        file.set_permissions(permissions)?;
    }
    file.sync_all()
}

/// Why a write failed.
#[derive(Debug, thiserror::Error)]
pub enum WriteError {
    #[error("Cannot write {display}: it is a directory.")]
    IsDirectory { display: String },
    #[error("Cannot write {display}: {source}")]
    Io {
        display: String,
        #[source]
        source: std::io::Error,
    },
}

/// Whether a write created or replaced its target.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WriteDisposition {
    Created,
    Overwrote,
}

/// A committed whole-file write.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct WriteOutcome {
    pub path: String,
    pub absolute: PathBuf,
    pub disposition: WriteDisposition,
    /// Bytes persisted.
    pub bytes: usize,
    /// The new file tag; `None` when the file is too large to snapshot.
    pub tag: Option<String>,
    /// A created file starting with `#!` got execute bits.
    pub made_executable: bool,
    /// `[path#TAG]` and the confirmation line.
    pub rendered: String,
}

/// Create or overwrite `absolute` with `content` under its path lock.
///
/// A replaced file keeps its BOM, line endings, and mode; a created file
/// gets `content` as given and execute bits when it starts with `#!`. The
/// written text is recorded in `store` with every line seen.
pub(crate) fn write_file(
    store: &EditStore,
    lock_dir: &Path,
    absolute: &Path,
    display: &str,
    content: &str,
) -> Result<WriteOutcome, WriteError> {
    let io = |source| WriteError::Io {
        display: display.to_owned(),
        source,
    };
    let canonical = crate::path::canonical_key(absolute);
    let _lock = lock(lock_dir, &canonical).map_err(io)?;
    let existing = match std::fs::metadata(&canonical) {
        Ok(metadata) if metadata.is_dir() => {
            return Err(WriteError::IsDirectory {
                display: display.to_owned(),
            })
        }
        Ok(metadata) => Some((
            std::fs::read(&canonical).map_err(io)?,
            metadata.permissions(),
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => return Err(io(error)),
    };
    let (persisted, permissions, disposition, made_executable) =
        if let Some((bytes, permissions)) = existing {
            let previous = String::from_utf8_lossy(&bytes);
            let (bom, body) = strip_bom(&previous);
            let persisted = format!(
                "{bom}{}",
                restore_line_endings(&normalize_to_lf(content), detect_line_ending(body))
            );
            (
                persisted,
                Some(permissions),
                WriteDisposition::Overwrote,
                false,
            )
        } else {
            if let Some(parent) = canonical.parent() {
                std::fs::create_dir_all(parent).map_err(io)?;
            }
            let executable = content.starts_with("#!");
            // A script is created rwxr-xr-x.
            let permissions = executable.then(|| Permissions::from_mode(0o755));
            (
                content.to_owned(),
                permissions,
                WriteDisposition::Created,
                executable,
            )
        };
    replace_atomic(&canonical, persisted.as_bytes(), permissions).map_err(io)?;
    let text = normalize_to_lf(strip_bom(&persisted).1).into_owned();
    let tag = (persisted.len() as u64 <= crate::store::MAX_SNAPSHOT_FILE_BYTES).then(|| {
        let line_count = text.split('\n').count() - usize::from(text.ends_with('\n'));
        let seen: Vec<u32> = (1..=u32::try_from(line_count).unwrap_or(u32::MAX)).collect();
        store.reset_noop(&canonical);
        store.record(&canonical, &text, Some(&seen))
    });
    let confirmation = format!("Successfully wrote {} bytes to {display}", persisted.len());
    let rendered = match &tag {
        Some(tag) => format!("[{display}#{tag}]\n{confirmation}"),
        None => confirmation,
    };
    Ok(WriteOutcome {
        path: display.to_owned(),
        absolute: absolute.to_path_buf(),
        disposition,
        bytes: persisted.len(),
        tag,
        made_executable,
        rendered,
    })
}

#[cfg(test)]
mod tests;
