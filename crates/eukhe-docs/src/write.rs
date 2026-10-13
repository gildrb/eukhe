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

use crate::error::EditError;
use crate::hashline::{EditWriter, WriteOp, WriteRequest as EditWriteRequest, WriteResponse};
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
    #[error("Cannot write {display}: it changed on disk since it was read. Nothing was written; re-read it and retry.")]
    Changed { display: String },
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

/// What a write expects to replace.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Base<'a> {
    /// Whatever is there, or nothing.
    Any,
    /// Exactly these bytes; anything else (or no file) is
    /// [`WriteError::Changed`].
    Bytes(&'a [u8]),
}

/// The file's permissions when its current bytes are `expected`; `None`
/// when they differ.
fn permissions_if_unchanged(
    canonical: &Path,
    expected: &[u8],
) -> std::io::Result<Option<Permissions>> {
    let current = std::fs::read(canonical)?;
    if current != expected {
        return Ok(None);
    }
    Ok(Some(std::fs::metadata(canonical)?.permissions()))
}

/// Create or overwrite `absolute` with `content` under its path lock, when
/// its current bytes are `base`.
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
    base: Base<'_>,
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
    let changed = || WriteError::Changed {
        display: display.to_owned(),
    };
    match (base, &existing) {
        (Base::Any, _) => {}
        (Base::Bytes(_), None) => return Err(changed()),
        (Base::Bytes(expected), Some((bytes, _))) => {
            if bytes.as_slice() != expected {
                return Err(changed());
            }
        }
    }
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

/// The [`EditWriter`] of a session: every hashline write takes the path
/// lock, compares the file's current bytes with the bytes the edit was
/// applied to, and replaces the file atomically (mode kept).
pub(crate) struct LockedWriter<'a> {
    pub(crate) lock_dir: &'a Path,
}

impl LockedWriter<'_> {
    fn lock_all(&self, paths: &[&Path]) -> Result<Vec<PathLock>, EditError> {
        let mut keys: Vec<&Path> = paths.to_vec();
        // One global order keeps two movers from deadlocking.
        keys.sort_unstable();
        keys.dedup();
        keys.into_iter()
            .map(|key| lock(self.lock_dir, key).map_err(|source| io_error(key, source)))
            .collect()
    }
}

fn io_error(path: &Path, source: std::io::Error) -> EditError {
    EditError::Io {
        path: path.to_path_buf(),
        source,
    }
}

/// Fail unless `canonical` still holds `before_raw`; return its permissions.
fn compare(canonical: &Path, display: &str, before_raw: &str) -> Result<Permissions, EditError> {
    permissions_if_unchanged(canonical, before_raw.as_bytes())
        .map_err(|source| io_error(canonical, source))?
        .ok_or_else(|| {
            EditError::apply(format!(
                "Edit rejected for {display}: the file changed on disk while the edit was being \
                 applied. Nothing was written. Re-read the file and retry."
            ))
        })
}

impl EditWriter for LockedWriter<'_> {
    fn write(&self, request: &EditWriteRequest<'_>) -> Result<WriteResponse, EditError> {
        let source = crate::path::canonical_key(request.absolute);
        match request.op {
            WriteOp::Create { content } => {
                let _locks = self.lock_all(&[&source])?;
                if let Some(parent) = source.parent() {
                    std::fs::create_dir_all(parent).map_err(|error| io_error(parent, error))?;
                }
                replace_atomic(&source, content.as_bytes(), None)
                    .map_err(|error| io_error(&source, error))?;
                Ok(WriteResponse {
                    written: content.to_owned(),
                })
            }
            WriteOp::Update {
                before_raw,
                content,
            } => {
                let _locks = self.lock_all(&[&source])?;
                let permissions = compare(&source, request.display, before_raw)?;
                replace_atomic(&source, content.as_bytes(), Some(permissions))
                    .map_err(|error| io_error(&source, error))?;
                Ok(WriteResponse {
                    written: content.to_owned(),
                })
            }
            WriteOp::Delete { before_raw } => {
                let _locks = self.lock_all(&[&source])?;
                compare(&source, request.display, before_raw)?;
                std::fs::remove_file(&source).map_err(|error| io_error(&source, error))?;
                Ok(WriteResponse {
                    written: String::new(),
                })
            }
            WriteOp::Move {
                before_raw,
                destination,
                content,
            } => {
                let target = crate::path::canonical_key(destination);
                let _locks = self.lock_all(&[&source, &target])?;
                let permissions = compare(&source, request.display, before_raw)?;
                if let Some(parent) = target.parent() {
                    std::fs::create_dir_all(parent).map_err(|error| io_error(parent, error))?;
                }
                replace_atomic(&target, content.as_bytes(), Some(permissions))
                    .map_err(|error| io_error(&target, error))?;
                std::fs::remove_file(&source).map_err(|error| io_error(&source, error))?;
                Ok(WriteResponse {
                    written: content.to_owned(),
                })
            }
        }
    }
}

#[cfg(test)]
mod tests;
