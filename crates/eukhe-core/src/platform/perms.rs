//! File permission policy: owner-only mode bits (0o600 files, 0o700 dirs).

use std::fs::OpenOptions;
use std::path::Path;

/// Owner-only file mode.
pub const PRIVATE_FILE_MODE: u32 = 0o600;
/// Owner-only directory mode.
pub const PRIVATE_DIR_MODE: u32 = 0o700;

/// Make a file owner-readable/writable only (`chmod 0o600`). Best-effort:
/// callers decide whether a failure is fatal.
///
/// # Errors
///
/// Returns the underlying I/O error when the permission change fails.
pub fn restrict_file(path: &Path) -> std::io::Result<()> {
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(PRIVATE_FILE_MODE))
}

/// Make a directory owner-accessible only (`chmod 0o700`).
///
/// # Errors
///
/// Returns the underlying I/O error when the permission change fails.
pub fn restrict_dir(path: &Path) -> std::io::Result<()> {
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(PRIVATE_DIR_MODE))
}

/// Set the private mode on files created through these options.
pub fn set_private_mode(options: &mut OpenOptions) {
    use std::os::unix::fs::OpenOptionsExt;
    options.mode(PRIVATE_FILE_MODE);
}

/// The file's mode bits (`mode & 0o777`); None when the metadata read fails.
#[must_use]
pub fn file_mode(path: &Path) -> Option<u32> {
    use std::os::unix::fs::PermissionsExt;
    std::fs::metadata(path)
        .ok()
        .map(|m| m.permissions().mode() & 0o777)
}

/// True when the path is an executable file (any execute bit).
#[must_use]
pub fn is_executable(path: &Path) -> bool {
    use std::os::unix::fs::PermissionsExt;
    std::fs::metadata(path).is_ok_and(|m| m.permissions().mode() & 0o111 != 0)
}

/// True when the current process may read and write the file (access(2)
/// semantics: real/effective uid checks, not just the file mode).
#[must_use]
pub fn is_readable_writable(path: &Path) -> bool {
    nix::unistd::access(
        path,
        nix::unistd::AccessFlags::R_OK | nix::unistd::AccessFlags::W_OK,
    )
    .is_ok()
}

/// True when the current user may read the file, mirroring Node
/// `fs.access(path, R_OK)` error-code semantics used by the edit preview.
///
/// # Errors
///
/// Returns the metadata I/O error, or an EACCES error when the permission
/// bits deny a read for the effective user.
pub fn is_readable(path: &Path) -> Result<(), std::io::Error> {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    let metadata = std::fs::metadata(path)?;
    // Root on Linux can read files regardless of permission bits; mirror
    // access(2)'s effective-uid check via the permission bits plus euid.
    let mode = metadata.permissions().mode();
    let readable = (mode & 0o004) != 0
        || ((mode & 0o040) != 0 && metadata.uid() == nix::unistd::Uid::effective().as_raw())
        || ((mode & 0o400) != 0 && metadata.uid() == nix::unistd::Uid::effective().as_raw());
    if readable {
        Ok(())
    } else {
        Err(std::io::Error::from_raw_os_error(13))
    }
}

/// Set the private mode on an already-open file (`fchmod`): exact bits despite
/// the umask, and tightens a pre-existing loose file. Callers decide whether a
/// failure is fatal.
///
/// # Errors
///
/// Returns the underlying I/O error when the permission bits cannot be set.
pub fn restrict_open_file(file: &std::fs::File) -> std::io::Result<()> {
    use std::os::unix::fs::PermissionsExt;
    file.set_permissions(std::fs::Permissions::from_mode(PRIVATE_FILE_MODE))
}

/// Create directories recursively with the private dir mode; existing
/// directories are left untouched (mkdir semantics).
///
/// # Errors
///
/// Returns the underlying I/O error when a directory cannot be created.
pub fn create_dir_all_private(path: &Path) -> std::io::Result<()> {
    use std::os::unix::fs::DirBuilderExt;
    std::fs::DirBuilder::new()
        .mode(PRIVATE_DIR_MODE)
        .recursive(true)
        .create(path)
}
