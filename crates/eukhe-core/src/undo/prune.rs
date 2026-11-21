//! Remove the snapshots of sessions whose last turn is older than
//! `undo.keepDays`: a session's snapshot directory changes at every turn,
//! so its modification time is its last turn.

use std::path::Path;
use std::time::{Duration, SystemTime};

/// Remove each session's snapshot directory under `dir` last changed
/// before `now - keep_days`, but `keep`'s (the session that is running);
/// the names of the ones removed.
///
/// # Errors
///
/// `dir` cannot be read, or a directory cannot be removed. A missing `dir`
/// removes nothing.
pub fn prune_snapshots(
    dir: &Path,
    keep_days: u64,
    now: SystemTime,
    keep: &str,
) -> std::io::Result<Vec<String>> {
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => return Err(error),
    };
    let horizon = now
        .checked_sub(Duration::from_secs(keep_days.saturating_mul(24 * 60 * 60)))
        .unwrap_or(SystemTime::UNIX_EPOCH);
    let keep = format!("{keep}.git");
    let mut removed = Vec::new();
    for entry in entries {
        let entry = entry?;
        let name = entry.file_name().to_string_lossy().into_owned();
        let meta = entry.metadata()?;
        let old = meta.modified().is_ok_and(|modified| modified < horizon);
        let repository = Path::new(&name)
            .extension()
            .is_some_and(|extension| extension == "git");
        if meta.is_dir() && repository && name != keep && old {
            std::fs::remove_dir_all(entry.path())?;
            removed.push(name);
        }
    }
    removed.sort();
    Ok(removed)
}
