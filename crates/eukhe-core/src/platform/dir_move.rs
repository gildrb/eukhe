//! Moving a directory to another place, across file systems too: a crash at
//! any step leaves the directory whole at one of the two places, and the
//! next move of the same pair ends the one a crash cut.

use std::ffi::OsString;
use std::fs;
use std::io;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

use super::fs::{rename_no_replace, sync_directory};

/// Move the directory `from` to `to`, whose parent exists. On one file
/// system a rename; across file systems a copy into `<to>.moving`, a mark
/// `<to>.moved` (the copy is whole), the copy's rename to `to`, then the
/// removal of `from` and of the mark. Run again after a crash, it ends the
/// move the crash cut. Nothing to move when nothing is at `from` or a
/// symlink is. Moves into one parent take turns (a lock on the parent).
///
/// # Errors
///
/// `AlreadyExists` when `from` and `to` both hold a directory this move did
/// not make (nothing is removed); else the OS error.
pub fn move_dir(from: &Path, to: &Path) -> io::Result<()> {
    let parent = to.parent().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            format!("{} has no parent directory", to.display()),
        )
    })?;
    let lock = fs::File::open(parent)?;
    lock.lock()?;
    let (staging, mark) = (sibling(to, ".moving"), sibling(to, ".moved"));
    if exists(&mark)? && exists(to)? {
        return finish(from, &mark, parent);
    }
    // A copy a crash cut before its mark, or a whole one a crash cut
    // before its rename: copied again below.
    remove(&staging)?;
    remove(&mark)?;
    match fs::symlink_metadata(from) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
        Ok(meta) if !meta.is_dir() => return Ok(()),
        Ok(_) => {}
    }
    match rename_no_replace(from, to) {
        Ok(()) => {
            sync_directory(parent)?;
            return from.parent().map_or(Ok(()), sync_directory);
        }
        Err(error) if error.kind() == io::ErrorKind::CrossesDevices => {}
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                format!(
                    "{} and {} both hold a directory",
                    from.display(),
                    to.display()
                ),
            ));
        }
        Err(error) => return Err(error),
    }
    copy_tree(from, &staging)?;
    fs::File::create(&mark)?.sync_all()?;
    sync_directory(parent)?;
    rename_no_replace(&staging, to)?;
    sync_directory(parent)?;
    finish(from, &mark, parent)
}

/// The last steps of a copying move: `to` is whole, so `from` and the mark go.
fn finish(from: &Path, mark: &Path, parent: &Path) -> io::Result<()> {
    remove(from)?;
    if let Some(dir) = from.parent() {
        match sync_directory(dir) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            synced => synced?,
        }
    }
    remove(mark)?;
    sync_directory(parent)
}

/// `path` with `suffix` appended to its last component.
fn sibling(path: &Path, suffix: &str) -> PathBuf {
    let mut name = OsString::from(path.as_os_str());
    name.push(suffix);
    PathBuf::from(name)
}

/// Whether an entry is at `path` (a symlink counts, followed or not).
fn exists(path: &Path) -> io::Result<bool> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error),
    }
}

/// Remove the entry at `path` (a directory with everything under it; a
/// symlink itself, not its target); nothing there is no error.
fn remove(path: &Path) -> io::Result<()> {
    let removed = match fs::symlink_metadata(path) {
        Ok(meta) if meta.is_dir() => fs::remove_dir_all(path),
        Ok(_) => fs::remove_file(path),
        Err(error) => Err(error),
    };
    match removed {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        removed => removed,
    }
}

/// Copy the directory `from` to the new `to`: files with their bytes and
/// mode, symlinks as symlinks, directories with their mode (set once their
/// entries are in); each synced.
fn copy_tree(from: &Path, to: &Path) -> io::Result<()> {
    let mut pending = vec![(from.to_path_buf(), to.to_path_buf())];
    let mut dirs = Vec::new();
    while let Some((source, target)) = pending.pop() {
        let meta = fs::symlink_metadata(&source)?;
        let kind = meta.file_type();
        if kind.is_symlink() {
            std::os::unix::fs::symlink(fs::read_link(&source)?, &target)?;
        } else if kind.is_dir() {
            fs::create_dir(&target)?;
            for entry in fs::read_dir(&source)? {
                let name = entry?.file_name();
                pending.push((source.join(&name), target.join(&name)));
            }
            dirs.push((target, meta.permissions().mode()));
        } else {
            fs::copy(&source, &target)?;
            fs::File::open(&target)?.sync_all()?;
        }
    }
    // Deepest first: a directory's mode may forbid writing into it.
    for (dir, mode) in dirs.into_iter().rev() {
        sync_directory(&dir)?;
        fs::set_permissions(&dir, fs::Permissions::from_mode(mode))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests;
