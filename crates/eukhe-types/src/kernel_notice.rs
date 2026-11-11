//! The marker of the kernel-unavailable notification.
//!
//! A session whose Python kernel cannot start offers no `ipython` tool
//! (eukhe-core `durable::rlm::kernel_unavailable_notice`) and reports why
//! in its connection state
//! ([`crate::daemon::AgentConnectionState::kernel_unavailable`]). The
//! interactive client shows that as a notification once per install
//! state: the first attach that finds the kernel unavailable shows it,
//! later ones do not, until a top-level session opens with a usable
//! kernel and a later one finds it gone again. omp does the same on a
//! fresh install's first interactive launch
//! (`resolveFirstLaunchPythonEvalWarning`, shown through the UI's startup
//! notifications). The marker file lives in the agent state directory
//! (`~/.eukhe`): the client that shows the notification writes it
//! ([`first_showing`]), the session open that finds the kernel usable
//! removes it ([`forget`]).

use std::io::ErrorKind;
use std::path::Path;

/// The marker's file name in the agent state directory.
const SHOWN_MARKER: &str = "kernel-unavailable-shown";

/// Whether the notification shows now: true the first time since the
/// kernel was last usable. The marker is created atomically, so two
/// clients attaching at once show one notification. A marker that cannot
/// be written shows the notification: shown twice beats never.
#[must_use]
pub fn first_showing(state_dir: &Path) -> bool {
    let marker = state_dir.join(SHOWN_MARKER);
    match std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&marker)
    {
        Ok(_) => true,
        Err(error) if error.kind() == ErrorKind::AlreadyExists => false,
        Err(error) => {
            tracing::warn!(%error, marker = %marker.display(), "kernel notice marker not written");
            true
        }
    }
}

/// The kernel is usable: forget the shown notification, so a later loss
/// shows it again.
pub fn forget(state_dir: &Path) {
    let marker = state_dir.join(SHOWN_MARKER);
    match std::fs::remove_file(&marker) {
        Ok(()) => {}
        Err(error) if error.kind() == ErrorKind::NotFound => {}
        Err(error) => {
            tracing::warn!(%error, marker = %marker.display(), "kernel notice marker not removed");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Once per install state: the first showing, not the next ones, and
    /// again after the kernel was usable in between.
    #[test]
    fn the_notification_shows_once_until_the_kernel_was_usable_again() {
        let dir = tempfile::TempDir::new().expect("state dir");
        assert!(first_showing(dir.path()), "the first attach shows it");
        assert!(!first_showing(dir.path()), "the second does not");
        assert!(!first_showing(dir.path()));
        forget(dir.path());
        forget(dir.path());
        assert!(first_showing(dir.path()), "gone again: it shows again");
        assert!(!first_showing(dir.path()));
    }

    /// A state directory that cannot hold the marker never hides the
    /// notification.
    #[test]
    fn a_marker_that_cannot_be_written_still_shows() {
        let dir = tempfile::TempDir::new().expect("state dir");
        let missing = dir.path().join("missing");
        assert!(first_showing(&missing));
        assert!(first_showing(&missing));
        forget(&missing);
    }
}
