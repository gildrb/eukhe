//! Staging directories of session imports and forks. A new storage is built
//! in a hidden directory beside its final place, `.<name>.import-<uuid>` or
//! `.<name>.fork-<uuid>` (same filesystem, so the final rename is atomic),
//! made durable, and renamed into place ([`publish`]): the final directory
//! holds the whole storage or does not exist. A process that dies mid-build
//! leaves its staging directory behind, as an interrupted saved-session
//! delete leaves its tombstone ([`TOMBSTONE_LABEL`]);
//! [`sweep_stale_staging_dirs`] removes both.

#[cfg(test)]
mod tests;

use std::io;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

use crate::platform::fs::sync_directory;

/// How long a staging directory stays untouched before the sweep takes it
/// for a crash leftover. The names carry no owner pid to probe (and a pid is
/// no reliable owner across pid reuse and pid namespaces), so age is the
/// only evidence. A staging directory lives for one import or fork: one
/// read of the source, one commit, one rename — seconds, minutes for the
/// largest sessions. A day is orders of magnitude above that, also covers a
/// build whose machine slept through it, and the cost of the margin is only
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

/// The failed step of [`publish`].
#[derive(Debug)]
pub(crate) struct PublishError {
    pub(crate) action: &'static str,
    pub(crate) path: PathBuf,
    pub(crate) source: io::Error,
}

/// Make the storage built in `staging` durable and move it to `target`: fsync
/// every file and directory under `staging`, rename it to `target` (both in
/// `parent`), and fsync `parent` so the rename survives a power loss too.
///
/// # Errors
///
/// A step fails. Before the rename nothing is at `target`; only the final
/// sync of `parent` fails with the storage already in place.
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
                    std::fs::File::open(&path)
                        .and_then(|file| file.sync_all())
                        .map_err(step("sync", &path))?;
                }
            }
            sync_directory(&dir).map_err(step("sync", &dir))?;
        }
        std::fs::rename(&staging, &target).map_err(step("move staged storage into", &target))?;
        sync_directory(&parent).map_err(step("sync", &parent))
    })
    .await
    .map_err(|join| PublishError {
        action: "publish",
        path: staging_path,
        source: io::Error::other(join),
    })?
}

fn step<'a>(action: &'static str, path: &'a Path) -> impl FnOnce(io::Error) -> PublishError + 'a {
    move |source| PublishError {
        action,
        path: path.to_owned(),
        source,
    }
}

/// What [`sweep_stale_staging_dirs`] did.
#[derive(Debug, Default)]
pub struct StagingSweep {
    /// The stale staging directories and tombstones removed.
    pub removed: Vec<PathBuf>,
    /// The staging directories and tombstones that could not be inspected
    /// or removed.
    pub failed: Vec<(PathBuf, io::Error)>,
}

/// Remove the import and fork staging directories and the saved-session
/// tombstones directly under `sessions_dir` that nothing touched for a day:
/// neither the directory nor any of its entries changed since (see
/// [`STALE_AFTER`]). Everything else stays: younger ones (a build or a delete
/// may be running), symlinks, files, and every other name. Blocking; run it
/// off the async executor.
///
/// # Errors
///
/// `sessions_dir` exists but cannot be listed. A directory that cannot be
/// inspected or removed is reported in [`StagingSweep::failed`] and the
/// sweep goes on.
pub fn sweep_stale_staging_dirs(sessions_dir: &Path) -> io::Result<StagingSweep> {
    let entries = match std::fs::read_dir(sessions_dir) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Ok(StagingSweep::default());
        }
        Err(error) => return Err(error),
    };
    let now = SystemTime::now();
    let mut sweep = StagingSweep::default();
    for entry in entries {
        let entry = entry?;
        if !entry.file_name().to_str().is_some_and(is_swept_name) {
            continue;
        }
        let dir = entry.path();
        let swept = entry.file_type().and_then(|file_type| {
            if !file_type.is_dir() {
                return Ok(false);
            }
            // A modification time ahead of the clock counts as fresh.
            let stale = now
                .duration_since(last_touched(&dir)?)
                .is_ok_and(|age| age >= STALE_AFTER);
            if stale {
                std::fs::remove_dir_all(&dir)?;
            }
            Ok(stale)
        });
        match swept {
            Ok(true) => sweep.removed.push(dir),
            Ok(false) => {}
            // Its owner published or removed it meanwhile.
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => sweep.failed.push((dir, error)),
        }
    }
    Ok(sweep)
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
