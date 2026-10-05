//! The image a session worker launch runs: the supervisor's own build.
//!
//! A worker speaks the supervisor's wire build, so it must run the exact
//! binary the supervisor runs. When the file the supervisor started from is
//! replaced or removed while it lives (a rebuilt `target/debug/eukhe`, an
//! in-place upgrade), Linux reports the supervisor's executable path with a
//! ` (deleted)` suffix: spawning that path fails (`ENOENT`), and spawning
//! the bare path would run a different build. The kernel keeps the running
//! image reachable through `/proc/self/exe` (in the forked child, `self` is
//! still the supervisor's image until the exec), so the launch runs it from
//! there, with argv[0] naming the original path.

use std::ffi::OsString;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

/// The program a worker launch executes and the argv[0] it carries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WorkerImage {
    /// The path handed to the exec.
    pub(crate) program: PathBuf,
    /// The argv[0] override: set when `program` is not the product path
    /// itself, so process listings still name the product binary.
    pub(crate) arg0: Option<OsString>,
}

impl WorkerImage {
    /// A command that executes this image with its argv[0].
    pub(crate) fn command(&self) -> tokio::process::Command {
        let mut command = tokio::process::Command::new(&self.program);
        #[cfg(unix)]
        if let Some(arg0) = &self.arg0 {
            command.arg0(arg0);
        }
        #[cfg(not(unix))]
        debug_assert!(
            self.arg0.is_none(),
            "only the Linux procfs image overrides argv[0]"
        );
        command
    }
}

/// The supervisor's own image, resolved for a worker launch.
///
/// # Errors
///
/// Returns an error when the running executable cannot be resolved.
pub(crate) fn worker_image() -> Result<WorkerImage> {
    let current = std::env::current_exe().context("resolve the supervisor executable")?;
    Ok(worker_image_for(&current))
}

/// [`worker_image`] for a resolved `current_exe()` path.
fn worker_image_for(current: &Path) -> WorkerImage {
    #[cfg(target_os = "linux")]
    {
        // procfs marks an unlinked image by appending the suffix to the
        // link target; the file at the original path (if any) is no longer
        // this build.
        const DELETED_SUFFIX: &str = " (deleted)";
        if let Some(original) = current
            .to_str()
            .and_then(|path| path.strip_suffix(DELETED_SUFFIX))
        {
            return WorkerImage {
                program: PathBuf::from("/proc/self/exe"),
                arg0: Some(OsString::from(original)),
            };
        }
    }
    WorkerImage {
        program: current.to_path_buf(),
        arg0: None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_live_image_runs_from_its_own_path() {
        assert_eq!(
            worker_image_for(Path::new("/opt/eukhe/bin/eukhe")),
            WorkerImage {
                program: PathBuf::from("/opt/eukhe/bin/eukhe"),
                arg0: None,
            }
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn a_replaced_image_runs_from_proc_self_exe() {
        assert_eq!(
            worker_image_for(Path::new("/repo/target/debug/eukhe (deleted)")),
            WorkerImage {
                program: PathBuf::from("/proc/self/exe"),
                arg0: Some(OsString::from("/repo/target/debug/eukhe")),
            }
        );
    }
}
