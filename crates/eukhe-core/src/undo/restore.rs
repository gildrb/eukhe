//! Carry out `/undo`'s fixes in the workspace: first every removal (and
//! the directories it leaves empty), then every write of a snapshot's
//! content (a symlink as a symlink, the executable bit as the snapshot
//! has it).

use std::path::Path;

use eukhe_bend::rules::undo::Fix;

use super::store::{Blob, Store};
use super::{changed, Entry, UndoError};

/// The mode git gives a symlink.
const SYMLINK_MODE: &str = "120000";
/// The mode git gives an executable file.
const EXECUTABLE_MODE: &str = "100755";

/// Apply `fixes` (one per entry) to the workspace of `store`; the paths it
/// changed, sorted.
pub(super) async fn apply(
    store: &Store,
    entries: &[Entry],
    fixes: &[Fix],
) -> Result<Vec<String>, UndoError> {
    if entries.len() != fixes.len() {
        return Err(UndoError::Answer(
            format!("{} fixes for {} paths", fixes.len(), entries.len()),
            "/undo",
        ));
    }
    let workspace = store.workspace();
    for (entry, fix) in changed(entries, fixes) {
        match fix {
            Fix::Remove => remove(workspace, &entry.path)?,
            Fix::Keep | Fix::Write => {}
        }
    }
    for (entry, fix) in changed(entries, fixes) {
        match (fix, &entry.before) {
            (Fix::Write, Some(blob)) => write(store, workspace, &entry.path, blob).await?,
            (Fix::Write, None) => {
                return Err(UndoError::Answer(
                    format!("a write of {} the snapshot does not have", entry.path),
                    "/undo",
                ));
            }
            (Fix::Keep | Fix::Remove, _) => {}
        }
    }
    let mut restored: Vec<String> = changed(entries, fixes)
        .map(|(entry, _)| entry.path.clone())
        .collect();
    restored.sort();
    Ok(restored)
}

/// Remove the file or symlink at `path`, then each parent directory it
/// leaves empty, up to the workspace.
fn remove(workspace: &Path, path: &str) -> Result<(), UndoError> {
    let full = workspace.join(path);
    match std::fs::remove_file(&full) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.into()),
    }
    let mut dir = full.parent();
    while let Some(parent) =
        dir.filter(|parent| *parent != workspace && parent.starts_with(workspace))
    {
        // A directory that is not empty stays: stop there.
        if std::fs::remove_dir(parent).is_err() {
            break;
        }
        dir = parent.parent();
    }
    Ok(())
}

/// Write the snapshot's `blob` at `path`, replacing what is there.
async fn write(store: &Store, workspace: &Path, path: &str, blob: &Blob) -> Result<(), UndoError> {
    let full = workspace.join(path);
    if let Some(parent) = full.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let content = store.blob(&blob.oid).await?;
    match std::fs::symlink_metadata(&full) {
        // A directory that still holds files (held back ones) stays: the
        // write fails rather than touch them.
        Ok(meta) if meta.is_dir() => std::fs::remove_dir(&full)?,
        Ok(_) => std::fs::remove_file(&full)?,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.into()),
    }
    if blob.mode == SYMLINK_MODE {
        let target = String::from_utf8_lossy(&content).into_owned();
        std::os::unix::fs::symlink(target, &full)?;
        return Ok(());
    }
    std::fs::write(&full, &content)?;
    let mode = if blob.mode == EXECUTABLE_MODE {
        0o755
    } else {
        0o644
    };
    std::fs::set_permissions(&full, std::os::unix::fs::PermissionsExt::from_mode(mode))?;
    Ok(())
}
