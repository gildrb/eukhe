//! The working directory of a session. A session runs in the directory its
//! create names (or, for a reopen that names none, the one its saved
//! session recorded), and that directory must exist. Nothing falls back
//! to `/` or to the supervisor's own working directory: the tools resolve
//! paths against the cwd, so a wrong cwd widens what they reach (Bend model
//! `bend/fsmode.bend`, law `cwd_is_explicit`).

use std::path::PathBuf;

/// Why a session cannot start in a working directory.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(crate) enum CwdError {
    /// The create names no working directory (and no saved session
    /// recorded one).
    #[error("a session needs a working directory")]
    Missing,
    /// The named directory does not exist (anymore).
    #[error("working directory {} is gone", .0.display())]
    Gone(PathBuf),
    /// The named path exists but is not a directory.
    #[error("working directory {} is not a directory", .0.display())]
    NotADirectory(PathBuf),
}

/// The working directory `cwd` names, when it is an existing directory.
///
/// # Errors
///
/// [`CwdError::Missing`] for no (or an empty) cwd, [`CwdError::Gone`] when
/// nothing is at the path, [`CwdError::NotADirectory`] for a file.
pub(crate) fn session_cwd(cwd: Option<&str>) -> Result<PathBuf, CwdError> {
    let Some(cwd) = cwd.filter(|cwd| !cwd.is_empty()) else {
        return Err(CwdError::Missing);
    };
    let path = PathBuf::from(cwd);
    match std::fs::metadata(&path) {
        Ok(found) if found.is_dir() => Ok(path),
        Ok(_) => Err(CwdError::NotADirectory(path)),
        Err(_) => Err(CwdError::Gone(path)),
    }
}
