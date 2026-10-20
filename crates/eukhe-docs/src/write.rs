//! Locked, atomic writes. Every write lands on the target's real path
//! (symlinks followed) and runs only after the host's [`AccessGate`]
//! let it. A writer then takes an OS lock on
//! `<lock dir>/<xxh64 of the real path>.lock` (shared by every session
//! and process of one eukhe home), and replaces the file through a
//! same-directory temporary file: write, fsync, rename, fsync the
//! directory. A replaced file keeps its mode; a created file gets the
//! default mode (no execute bit).

use std::fs::{File, OpenOptions, Permissions};
use std::io::Write as _;
use std::os::unix::fs::OpenOptionsExt as _;
use std::os::unix::fs::PermissionsExt as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use eukhe_types::path_policy::{real_path, resolve};
use twox_hash::XxHash64;

use crate::error::EditError;
use crate::gate::{Access, AccessGate};
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
/// new file from its creation (the replaced file's mode; `None`: the
/// default mode).
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
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    if let Some(permissions) = &permissions {
        // The mode applies at creation: no window where the bytes are
        // readable under a wider mode.
        options.mode(permissions.mode());
    }
    let mut file = options.open(path)?;
    file.write_all(bytes)?;
    if let Some(permissions) = permissions {
        // The umask may have narrowed the creation mode.
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
    #[error("Did not write {display}: {reason}")]
    Refused { display: String, reason: String },
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
/// its current bytes are `base`, after `gate` let the write of its real
/// path.
///
/// A replaced file keeps its BOM, line endings, and mode; a created file
/// gets `content` as given and the default mode (no execute bit). The
/// written text is recorded in `store` with every line seen.
pub(crate) fn write_file(
    store: &EditStore,
    lock_dir: &Path,
    gate: &dyn AccessGate,
    absolute: &Path,
    display: &str,
    content: &str,
    base: Base<'_>,
) -> Result<WriteOutcome, WriteError> {
    let io = |source| WriteError::Io {
        display: display.to_owned(),
        source,
    };
    let refused = |reason| WriteError::Refused {
        display: display.to_owned(),
        reason,
    };
    let resolved = resolve(absolute);
    gate.check(Access::Write, &resolved, display)
        .map_err(refused)?;
    let canonical = resolved.into_path();
    let _lock = lock(lock_dir, &canonical).map_err(io)?;
    if real_path(absolute) != canonical {
        return Err(refused(MOVED.to_owned()));
    }
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
    let (persisted, permissions, disposition) = if let Some((bytes, permissions)) = existing {
        let previous = String::from_utf8_lossy(&bytes);
        let (bom, body) = strip_bom(&previous);
        let persisted = format!(
            "{bom}{}",
            restore_line_endings(&normalize_to_lf(content), detect_line_ending(body))
        );
        (persisted, Some(permissions), WriteDisposition::Overwrote)
    } else {
        if let Some(parent) = canonical.parent() {
            std::fs::create_dir_all(parent).map_err(io)?;
        }
        (content.to_owned(), None, WriteDisposition::Created)
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
        rendered,
    })
}

/// Why a write stops when the real path changed between the gate and the
/// lock (a link was made or moved meanwhile).
const MOVED: &str = "its real path changed while the write waited (a symlink was made or moved). Nothing was written; retry.";

/// The [`EditWriter`] of a session: every hashline write lets `gate` check
/// each real path it changes, takes the path lock, compares the file's
/// current bytes with the bytes the edit was applied to, and replaces the
/// file atomically (mode kept).
pub(crate) struct LockedWriter<'a> {
    pub(crate) lock_dir: &'a Path,
    pub(crate) gate: &'a dyn AccessGate,
}

impl LockedWriter<'_> {
    /// Let the gate check the write of `absolute` (shown as `display`);
    /// its real path.
    fn allow(&self, absolute: &Path, display: &str) -> Result<PathBuf, EditError> {
        let real = resolve(absolute);
        self.gate
            .check(Access::Write, &real, display)
            .map_err(|reason| EditError::Refused(format!("Did not write {display}: {reason}")))?;
        Ok(real.into_path())
    }

    /// Lock every path of `pairs` (each the written path and its real
    /// path at the gate), then fail if a real path changed meanwhile.
    fn lock_all(&self, pairs: &[(&Path, &Path, &str)]) -> Result<Vec<PathLock>, EditError> {
        let mut keys: Vec<&Path> = pairs.iter().map(|(_, real, _)| *real).collect();
        // One global order keeps two movers from deadlocking.
        keys.sort_unstable();
        keys.dedup();
        let locks = keys
            .into_iter()
            .map(|key| lock(self.lock_dir, key).map_err(|source| io_error(key, source)))
            .collect::<Result<Vec<_>, _>>()?;
        match pairs
            .iter()
            .find(|(absolute, real, _)| real_path(absolute) != *real)
        {
            Some((_, _, display)) => Err(EditError::Refused(format!(
                "Did not write {display}: {MOVED}"
            ))),
            None => Ok(locks),
        }
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
        let source = self.allow(request.absolute, request.display)?;
        let this = (request.absolute, source.as_path(), request.display);
        match request.op {
            WriteOp::Create { content } => {
                let _locks = self.lock_all(&[this])?;
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
                let _locks = self.lock_all(&[this])?;
                let permissions = compare(&source, request.display, before_raw)?;
                replace_atomic(&source, content.as_bytes(), Some(permissions))
                    .map_err(|error| io_error(&source, error))?;
                Ok(WriteResponse {
                    written: content.to_owned(),
                })
            }
            WriteOp::Delete { before_raw } => {
                let _locks = self.lock_all(&[this])?;
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
                let shown = destination.display().to_string();
                let target = self.allow(destination, &shown)?;
                let _locks = self.lock_all(&[this, (destination, target.as_path(), &shown)])?;
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
