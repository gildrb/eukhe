//! Locations and result shapes for the kernel's persisted user namespace,
//! which is revived when a session resumes. The kernel is otherwise spawned
//! fresh on resume, leaving the model believing it still has access to
//! variables/imports it defined earlier.
//!
//! Snapshotting is best-effort and per-variable: each top-level name is pickled
//! with `dill` independently, so a single unpicklable object (open file,
//! socket, GPU tensor, ...) is skipped and reported rather than aborting the
//! whole snapshot.
//!
//! Ported from `core/kernel/state-snapshot.ts`.

use std::path::{Path, PathBuf};

/// Default ceiling on a snapshot payload. Over-cap variables are skipped + reported.
pub const DEFAULT_SNAPSHOT_MAX_BYTES: u64 = 256 * 1024 * 1024;
/// Default ceiling for one serialized variable.
pub const DEFAULT_SNAPSHOT_MAX_VARIABLE_BYTES: u64 = 16 * 1024 * 1024;

const KERNEL_STATE_BASENAME: &str = "kernel-state";

/// The directory under the work root holding the sessions' kernel
/// snapshot directories (and, before the work root, under each storage).
const KERNELS_DIR: &str = "kernels";

/// One name that could not be serialized, with a short reason.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SnapshotSkip {
    pub name: String,
    pub reason: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SnapshotResult {
    /// Top-level names successfully serialized into the payload.
    pub saved: Vec<String>,
    /// Names that could not be serialized, with a short reason.
    pub skipped: Vec<SnapshotSkip>,
    /// Oversized live variables removed by an explicit compaction snapshot.
    pub pruned: Option<Vec<String>>,
    /// Payload size on disk, in bytes.
    pub bytes: u64,
    pub path: PathBuf,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RestoreResult {
    /// Names successfully revived into the kernel namespace.
    pub restored: Vec<String>,
    /// Names present in the snapshot that failed to revive, with a short reason.
    pub failed: Vec<SnapshotSkip>,
    pub path: PathBuf,
}

/// Absolute path to the dill payload within a session's artifact directory.
pub fn snapshot_path_in(artifact_dir: impl AsRef<Path>) -> PathBuf {
    artifact_dir
        .as_ref()
        .join(format!("{KERNEL_STATE_BASENAME}.dill"))
}

/// Absolute path to the JSON manifest within a session's artifact directory.
pub fn manifest_path_in(artifact_dir: impl AsRef<Path>) -> PathBuf {
    artifact_dir
        .as_ref()
        .join(format!("{KERNEL_STATE_BASENAME}.json"))
}

/// The kernel snapshot directories of the session stored at
/// `storage_dir`, one per conversation: `<work root>/kernels/<storage dir
/// name>`. The kernel writes them, so they lie in the work root, out of the
/// agent dir. `None` when `agent_dir` has no work root or `storage_dir` no
/// name.
#[must_use]
pub fn session_snapshots_dir(agent_dir: &Path, storage_dir: &Path) -> Option<PathBuf> {
    let work_root = eukhe_types::platform::dirs::work_root_of(agent_dir)?;
    Some(work_root.join(KERNELS_DIR).join(storage_dir.file_name()?))
}

/// Move the snapshot directories an older Eukhe kept in the storage
/// (`<storage dir>/kernels`) to [`session_snapshots_dir`], its parents
/// created private; nothing to move when none is there. A move a crash
/// cut ends on the next call ([`crate::platform::move_dir`]).
///
/// # Errors
///
/// The move fails (the old directory stays whole).
pub fn move_storage_snapshots(agent_dir: &Path, storage_dir: &Path) -> std::io::Result<()> {
    let old = storage_dir.join(KERNELS_DIR);
    match std::fs::symlink_metadata(&old) {
        Ok(meta) if meta.is_dir() => {}
        Ok(_) => return Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
    }
    let Some(new) = session_snapshots_dir(agent_dir, storage_dir) else {
        return Ok(());
    };
    if let Some(parent) = new.parent() {
        crate::platform::perms::create_dir_all_private(parent)?;
    }
    crate::platform::move_dir(&old, &new)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn session_snapshots_lie_in_the_work_root() {
        assert_eq!(
            session_snapshots_dir(
                Path::new("/home/u/.eukhe"),
                Path::new("/home/u/.eukhe/sessions/019a")
            ),
            Some(PathBuf::from("/home/u/.eukhe-work/kernels/019a"))
        );
    }

    /// Migration: an install upgraded with snapshots in the storage
    /// (`<storage>/kernels/<conversation>`) finds them in the work root,
    /// byte for byte, the storage keeping its other files; a second call
    /// moves nothing.
    #[test]
    fn storage_snapshots_move_to_the_work_root() {
        let dir = tempfile::tempdir().unwrap();
        let agent_dir = dir.path().join("agent");
        let storage = agent_dir.join("sessions/019a");
        let old = storage.join("kernels/conv-1");
        std::fs::create_dir_all(&old).unwrap();
        std::fs::write(snapshot_path_in(&old), "dill").unwrap();
        std::fs::write(manifest_path_in(&old), "{}").unwrap();
        std::fs::write(storage.join("main.jsonl"), "{}\n").unwrap();
        move_storage_snapshots(&agent_dir, &storage).unwrap();
        move_storage_snapshots(&agent_dir, &storage).unwrap();
        let new = session_snapshots_dir(&agent_dir, &storage)
            .unwrap()
            .join("conv-1");
        let read = |path: PathBuf| std::fs::read_to_string(path).ok();
        assert_eq!(
            (
                read(snapshot_path_in(&new)),
                read(manifest_path_in(&new)),
                storage.join("kernels").exists(),
                read(storage.join("main.jsonl")),
                new.starts_with(dir.path().join("agent-work")),
            ),
            (
                Some("dill".to_owned()),
                Some("{}".to_owned()),
                false,
                Some("{}\n".to_owned()),
                true,
            )
        );
    }

    #[test]
    fn paths_match_ts_layout() {
        assert_eq!(
            snapshot_path_in("/tmp/art"),
            PathBuf::from("/tmp/art/kernel-state.dill")
        );
        assert_eq!(
            manifest_path_in("/tmp/art"),
            PathBuf::from("/tmp/art/kernel-state.json")
        );
    }
}
