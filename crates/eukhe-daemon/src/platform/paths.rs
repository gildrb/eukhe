//! Daemon endpoint naming (TS: `daemon-supervisor.ts` `workerSocketPath`):
//! every worker socket beside its own supervisor's socket (the default
//! supervisor socket is `eukhe_types::platform::daemon_socket`'s). A socket
//! dir is checked before a bind ([`prepare_socket_dir`], shared with the
//! chat lock endpoints in `eukhe_core::platform::socket_dir`).

use std::path::{Path, PathBuf};

use anyhow::Result;
pub(crate) use eukhe_core::platform::socket_dir::prepare_socket_dir;
#[cfg(test)]
pub(crate) use eukhe_core::platform::socket_dir::SocketDir;

use crate::paths::hash_key;

/// The socket-dir check a supervisor runs before it binds `socket_path`
/// ([`prepare_socket_dir`] on its parent), for a launcher to run before
/// it spawns one: the spawned supervisor's stderr goes nowhere, so a
/// refused dir would otherwise surface only as a startup timeout.
///
/// # Errors
///
/// The refusal [`prepare_socket_dir`] gives the supervisor.
pub fn check_daemon_socket_dir(socket_path: &Path) -> Result<()> {
    match socket_path.parent() {
        Some(parent) if !parent.as_os_str().is_empty() => prepare_socket_dir(parent).map(|_| ()),
        Some(_) | None => Ok(()),
    }
}

/// Worker endpoint next to the supervisor's: in the supervisor socket's own
/// directory (never the per-user default dir, so a daemon on a custom
/// socket keeps every endpoint it mints under that socket's dir), named by
/// [`worker_socket_prefix`] plus the worker id prefix (TS
/// `workerSocketPath`).
#[must_use]
pub fn worker_socket_path(supervisor_socket_path: &Path, worker_id: &str) -> PathBuf {
    supervisor_socket_path
        .parent()
        .unwrap_or(Path::new(""))
        .join(format!(
            "{}{}.sock",
            worker_socket_prefix(supervisor_socket_path),
            &worker_id[..12.min(worker_id.len())]
        ))
}

/// The file-name prefix every worker endpoint of one supervisor shares:
/// `worker-<hash12(supervisor socket)>-`. The hashed key keeps the workers
/// of several supervisors that share one directory apart.
#[must_use]
pub(crate) fn worker_socket_prefix(supervisor_socket_path: &Path) -> String {
    let key = hash_key(&supervisor_socket_path.to_string_lossy(), 12);
    format!("worker-{key}-")
}

// Socket-filesystem identity is the shared platform contract
// `eukhe_types::platform::socket_identity` (re-exported through
// `crate::platform`): the same helper serves stale-file cleanup here and
// direct-transport ticket validation in eukhe-tui/eukhe-cli clients.

pub use eukhe_types::daemon::SocketIdentity;
pub use eukhe_types::platform::socket_identity;
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn worker_socket_names_are_deterministic() {
        let supervisor = Path::new("/fixture/custom/d.sock");
        let a = worker_socket_path(supervisor, "0123456789abcdef");
        let b = worker_socket_path(supervisor, "fedcba9876543210");
        assert_ne!(a, b);
        // Only the first 12 id characters key the name.
        assert_eq!(a, worker_socket_path(supervisor, "0123456789abffff"));
    }

    /// A supervisor's worker endpoints live in ITS socket's directory,
    /// never the per-user default socket dir: a daemon on a temp socket
    /// keeps every endpoint under that temp dir.
    #[test]
    fn worker_sockets_sit_beside_the_supervisor_socket() {
        let supervisor = Path::new("/fixture/custom/d.sock");
        let key = hash_key("/fixture/custom/d.sock", 12);
        assert_eq!(
            worker_socket_path(supervisor, "0123456789abcdef"),
            PathBuf::from(format!("/fixture/custom/worker-{key}-0123456789ab.sock"))
        );
    }
}
