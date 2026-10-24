//! The working directory of a session. A session runs in the directory its
//! create names (or, for a reopen that names none, the one its saved
//! session recorded), and that directory must exist. Nothing falls back
//! to `/` or to the supervisor's own working directory: the tools resolve
//! paths against the cwd, so a wrong cwd widens what they reach. The
//! verdict is the compiled core's (`eukhe_bend::rules::fsmode::session_cwd`,
//! `bend/fsmode.bend`, laws `cwd_is_explicit` and `fsmode_ffi_answers`).

use std::path::PathBuf;

use eukhe_bend::rules::fsmode::{Cwd, Stat};

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
    /// The named path is too long for the check (the core's error).
    #[error("working directory not checked: {0}")]
    Unchecked(String),
}

/// The working directory `cwd` names, when it is an existing directory.
///
/// # Errors
///
/// [`CwdError::Missing`] for no (or an empty) cwd, [`CwdError::Gone`] when
/// nothing is at the path, [`CwdError::NotADirectory`] for a file,
/// [`CwdError::Unchecked`] for a path too long to send to the core.
pub(crate) fn session_cwd(cwd: Option<&str>) -> Result<PathBuf, CwdError> {
    let stat = match cwd.map(std::fs::metadata) {
        Some(Ok(found)) if found.is_dir() => Stat::Dir,
        Some(Ok(_)) => Stat::File,
        Some(Err(_)) | None => Stat::Absent,
    };
    let verdict = eukhe_bend::rules::fsmode::session_cwd(cwd, stat)
        .map_err(|error| CwdError::Unchecked(error.to_string()))?;
    let path = || PathBuf::from(cwd.unwrap_or_default());
    match verdict {
        Cwd::Opened => Ok(path()),
        Cwd::NeedsCwd => Err(CwdError::Missing),
        Cwd::Gone => Err(CwdError::Gone(path())),
        Cwd::NotDir => Err(CwdError::NotADirectory(path())),
    }
}
