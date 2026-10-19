//! Staging directories of session imports and forks. A new storage is built
//! in a hidden directory beside its final place, `.<name>.import-<uuid>` or
//! `.<name>.fork-<uuid>` (same filesystem, so the final rename is atomic),
//! made durable, and renamed into place ([`publish`]): the final directory
//! holds the whole storage or does not exist, and the rename never
//! replaces an entry at the final place. While it builds, the process
//! holds an exclusive lock on the staging lock file `<staging>.lock`
//! ([`lock_staging`]). A process that dies mid-build leaves its staging
//! directory (and maybe its lock file) behind, as an interrupted
//! saved-session delete leaves its tombstone ([`TOMBSTONE_LABEL`]);
//! [`sweep_stale_staging_dirs`] removes them. The model is
//! `bend/staging.bend`.

#[cfg(test)]
mod bridge;
#[cfg(test)]
mod tests;

use std::fs::{File, TryLockError};
use std::io;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use crate::platform::fs::{rename_no_replace, sync_directory};

/// How long a staging directory, a tombstone or a lock file stays untouched
/// before the sweep takes it for a crash leftover, when no live process
/// holds its lock. The lock is the evidence that a build runs; the age
/// covers the moment between the creation of a lock file and its lock, and
/// the leftovers of a build that held no lock. A staging directory lives
/// for one import or fork: seconds, minutes for the largest sessions. A day
/// is orders of magnitude above that, and the cost of the margin is only
/// disk space a leftover holds until a later sweep. Tombstones share the
/// bound for simplicity, though a rename keeps modification times: the
/// fresh tombstone of an old session already counts as stale, and a sweep
/// may remove it under a running delete (concurrent `remove_dir_all`s
/// tolerate each other; the later one may find nothing left).
const STALE_AFTER: Duration = Duration::from_hours(24);

/// The infix of a saved-session tombstone, `.<id>.deleted-<uuid>`: a storage
/// the daemon's saved-session delete renamed aside before removing it.
const TOMBSTONE_LABEL: &str = "deleted";

/// Hex digits of the simple-format uuid ending a staging directory name.
const STAGING_ID_LEN: usize = 32;

/// The suffix of the lock file beside a staging directory.
const LOCK_SUFFIX: &str = ".lock";

/// The commit log of a durable storage: a directory with it is a storage,
/// and the sweep does not look inside it.
const MAIN_FILE: &str = "main.jsonl";

/// What a staging directory builds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StagingKind {
    /// A legacy session imported into a new storage.
    Import,
    /// A session copied and forked into a new storage.
    Fork,
}

impl StagingKind {
    const ALL: [Self; 2] = [Self::Import, Self::Fork];

    /// The infix of the staging directory name: `.<name>.<label>-<uuid>`.
    fn label(self) -> &'static str {
        match self {
            Self::Import => "import",
            Self::Fork => "fork",
        }
    }
}

/// The parent of `target` and a fresh staging directory beside it; `None`
/// when `target` has no name or parent, or a path is not UTF-8.
pub(crate) fn staging_dir(target: &Path, kind: StagingKind) -> Option<(PathBuf, PathBuf)> {
    let name = target.file_name()?.to_str()?;
    let parent = match target.parent()? {
        parent if parent.as_os_str().is_empty() => PathBuf::from("."),
        parent => parent.to_owned(),
    };
    let staging = parent.join(format!(
        ".{name}.{}-{}",
        kind.label(),
        uuid::Uuid::new_v4().simple()
    ));
    staging.to_str()?;
    Some((parent, staging))
}

/// The lock file of the staging directory `staging`.
fn lock_path(staging: &Path) -> PathBuf {
    let mut name = staging.as_os_str().to_owned();
    name.push(LOCK_SUFFIX);
    PathBuf::from(name)
}

/// The held lock of a staging directory: while it lives, no sweep takes
/// the directory. Drop removes the lock file and then releases the lock.
#[derive(Debug)]
pub(crate) struct StagingLock {
    path: PathBuf,
    _file: File,
}

impl Drop for StagingLock {
    fn drop(&mut self) {
        if let Err(error) = std::fs::remove_file(&self.path) {
            if error.kind() != io::ErrorKind::NotFound {
                tracing::warn!(
                    lock = %self.path.display(),
                    %error,
                    "failed to remove a staging lock file"
                );
            }
        }
    }
}

/// Create the lock file of the staging directory `staging` (before the
/// directory) and hold its exclusive lock. Hold the guard until the
/// staging directory is published or removed. A sweep that inspects the
/// fresh lock file holds it only for a moment: the wait is short.
///
/// # Errors
///
/// The lock file exists already or cannot be created or locked.
pub(crate) fn lock_staging(staging: &Path) -> io::Result<StagingLock> {
    let path = lock_path(staging);
    let file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)?;
    file.lock()?;
    Ok(StagingLock { path, _file: file })
}

/// The failed step of [`publish`].
#[derive(Debug)]
pub(crate) enum PublishError {
    /// An entry is at the target already: nothing moved.
    TargetExists,
    /// A step failed.
    Step {
        action: &'static str,
        path: PathBuf,
        source: io::Error,
    },
}

/// Make the storage built in `staging` durable and move it to `target`: fsync
/// every file and directory under `staging`, rename it to `target` (both in
/// `parent`) unless an entry is there, and fsync `parent` so the rename
/// survives a power loss too.
///
/// # Errors
///
/// [`PublishError::TargetExists`] when an entry is at `target` (it stays as
/// it was), else the step that failed. Before the rename nothing is at
/// `target`; only the final sync of `parent` fails with the storage already
/// in place.
pub(crate) async fn publish(
    staging: &Path,
    target: &Path,
    parent: &Path,
) -> Result<(), PublishError> {
    let (staging, target, parent) = (staging.to_owned(), target.to_owned(), parent.to_owned());
    let staging_path = staging.clone();
    tokio::task::spawn_blocking(move || {
        let mut pending = vec![staging.clone()];
        while let Some(dir) = pending.pop() {
            for entry in std::fs::read_dir(&dir).map_err(step("read directory", &dir))? {
                let entry = entry.map_err(step("read directory", &dir))?;
                let path = entry.path();
                let file_type = entry.file_type().map_err(step("inspect", &path))?;
                if file_type.is_dir() {
                    pending.push(path);
                } else if file_type.is_file() {
                    File::open(&path)
                        .and_then(|file| file.sync_all())
                        .map_err(step("sync", &path))?;
                }
            }
            sync_directory(&dir).map_err(step("sync", &dir))?;
        }
        match rename_no_replace(&staging, &target) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                return Err(PublishError::TargetExists);
            }
            Err(error) => return Err(step("move staged storage into", &target)(error)),
        }
        sync_directory(&parent).map_err(step("sync", &parent))
    })
    .await
    .map_err(|join| PublishError::Step {
        action: "publish",
        path: staging_path,
        source: io::Error::other(join),
    })?
}

fn step<'a>(action: &'static str, path: &'a Path) -> impl FnOnce(io::Error) -> PublishError + 'a {
    move |source| PublishError::Step {
        action,
        path: path.to_owned(),
        source,
    }
}

/// What [`sweep_stale_staging_dirs`] did.
#[derive(Debug, Default)]
pub struct StagingSweep {
    /// The stale staging directories, tombstones and lock files removed.
    pub removed: Vec<PathBuf>,
    /// The entries that could not be inspected or removed.
    pub failed: Vec<(PathBuf, io::Error)>,
}

/// What an entry the sweep meets is.
enum Met {
    /// A staging directory or a tombstone.
    Leftover,
    /// A lock file whose staging directory is gone.
    OrphanLock,
    /// A directory to look inside.
    Descend,
    /// Anything else: kept, not entered.
    Keep,
}

/// Remove, under each of `roots` and at every depth, the import and fork
/// staging directories, the saved-session tombstones, and the staging lock
/// files without their directory, that no live process holds the lock of
/// and that nothing touched for a day: neither the entry nor any of its
/// direct entries changed since (see [`STALE_AFTER`]). The walk enters
/// every other directory, except a storage (it holds `main.jsonl`) and a
/// symlink. Everything else stays: held and younger leftovers (a build or a
/// delete may be running), symlinks, other files and names. A missing root
/// is empty. Blocking; run it off the async executor. The daemon runs it at
/// boot and periodically.
///
/// # Errors
///
/// A root exists but cannot be listed. An entry that cannot be inspected
/// or removed is reported in [`StagingSweep::failed`] and the sweep goes
/// on.
pub fn sweep_stale_staging_dirs(roots: &[&Path]) -> io::Result<StagingSweep> {
    let now = SystemTime::now();
    let mut sweep = StagingSweep::default();
    for root in roots {
        match std::fs::read_dir(root) {
            Ok(_) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
            Err(error) => return Err(error),
        }
        let mut pending = vec![root.to_path_buf()];
        while let Some(dir) = pending.pop() {
            let entries = match std::fs::read_dir(&dir) {
                Ok(entries) => entries,
                Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
                Err(error) => {
                    sweep.failed.push((dir, error));
                    continue;
                }
            };
            for entry in entries {
                let entry = match entry {
                    Ok(entry) => entry,
                    Err(error) => {
                        sweep.failed.push((dir.clone(), error));
                        continue;
                    }
                };
                let path = entry.path();
                let swept = match meet(&entry) {
                    Ok(Met::Leftover) => sweep_leftover(&path, now),
                    Ok(Met::OrphanLock) => sweep_orphan_lock(&path, now),
                    Ok(Met::Descend) => {
                        pending.push(path);
                        continue;
                    }
                    Ok(Met::Keep) => continue,
                    Err(error) => Err(error),
                };
                match swept {
                    Ok(true) => sweep.removed.push(path),
                    Ok(false) => {}
                    // Its owner published or removed it meanwhile.
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                    Err(error) => sweep.failed.push((path, error)),
                }
            }
        }
    }
    Ok(sweep)
}

/// What the entry is, by its name and its type (symlinks not followed).
fn meet(entry: &std::fs::DirEntry) -> io::Result<Met> {
    let file_type = entry.file_type()?;
    let name = entry.file_name();
    let name = name.to_str();
    if file_type.is_dir() {
        if name.is_some_and(is_swept_name) {
            return Ok(Met::Leftover);
        }
        let storage = std::fs::symlink_metadata(entry.path().join(MAIN_FILE))
            .is_ok_and(|metadata| metadata.is_file());
        return Ok(if storage { Met::Keep } else { Met::Descend });
    }
    let lock = file_type.is_file()
        && name
            .and_then(|name| name.strip_suffix(LOCK_SUFFIX))
            .is_some_and(is_swept_name);
    if lock {
        let dir = entry.path().with_extension("");
        return Ok(match std::fs::symlink_metadata(dir) {
            Ok(_) => Met::Keep,
            Err(error) if error.kind() == io::ErrorKind::NotFound => Met::OrphanLock,
            Err(error) => return Err(error),
        });
    }
    Ok(Met::Keep)
}

/// Take the lock of `lock` when it exists: `Ok(None)` when no lock file is
/// there, an error `WouldBlock` when a live process holds it.
fn take_lock(lock: &Path) -> io::Result<Option<File>> {
    let file = match std::fs::OpenOptions::new().write(true).open(lock) {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error),
    };
    match file.try_lock() {
        Ok(()) => Ok(Some(file)),
        Err(TryLockError::Error(error)) => Err(error),
        Err(TryLockError::WouldBlock) => Err(io::Error::from(io::ErrorKind::WouldBlock)),
    }
}

/// Whether `modified` is a day old; a time ahead of the clock is fresh.
fn is_stale(now: SystemTime, modified: SystemTime) -> bool {
    now.duration_since(modified)
        .is_ok_and(|age| age >= STALE_AFTER)
}

/// Remove the staging directory or tombstone `dir` when no live process
/// holds its lock and it is stale; then its lock file too.
fn sweep_leftover(dir: &Path, now: SystemTime) -> io::Result<bool> {
    let lock = lock_path(dir);
    let held = match take_lock(&lock) {
        Ok(held) => held,
        Err(error) if error.kind() == io::ErrorKind::WouldBlock => return Ok(false),
        Err(error) => return Err(error),
    };
    if !is_stale(now, last_touched(dir)?) {
        return Ok(false);
    }
    std::fs::remove_dir_all(dir)?;
    if held.is_some() {
        match std::fs::remove_file(&lock) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    Ok(true)
}

/// Remove the lock file `lock` of a gone staging directory when no live
/// process holds it and it is stale.
fn sweep_orphan_lock(lock: &Path, now: SystemTime) -> io::Result<bool> {
    let _held = match take_lock(lock) {
        Ok(held) => held,
        Err(error) if error.kind() == io::ErrorKind::WouldBlock => return Ok(false),
        Err(error) => return Err(error),
    };
    if !is_stale(now, std::fs::symlink_metadata(lock)?.modified()?) {
        return Ok(false);
    }
    std::fs::remove_file(lock)?;
    Ok(true)
}

/// Whether `name` is one [`staging_dir`] mints or a saved-session tombstone:
/// `.<name>.<label>-<uuid>`.
fn is_swept_name(name: &str) -> bool {
    let Some((target, suffix)) = name
        .strip_prefix('.')
        .and_then(|rest| rest.rsplit_once('.'))
    else {
        return false;
    };
    let Some((label, id)) = suffix.split_once('-') else {
        return false;
    };
    !target.is_empty()
        && (label == TOMBSTONE_LABEL
            || StagingKind::ALL
                .into_iter()
                .any(|kind| kind.label() == label))
        && id.len() == STAGING_ID_LEN
        && id
            .bytes()
            .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
}

/// The newest modification time of `dir` and its direct entries.
fn last_touched(dir: &Path) -> io::Result<SystemTime> {
    let mut newest = std::fs::symlink_metadata(dir)?.modified()?;
    for entry in std::fs::read_dir(dir)? {
        newest = newest.max(entry?.metadata()?.modified()?);
    }
    Ok(newest)
}
