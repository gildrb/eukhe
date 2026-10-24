//! Daemon endpoint naming (TS: `daemon-socket.ts`
//! `defaultDaemonSocketPath` / `daemon-supervisor.ts` `workerSocketPath`):
//! the default supervisor socket under `<tmpdir>/eukhe-<uid>/`, and every
//! worker socket beside its own supervisor's socket. The socket dir is
//! checked before a bind ([`prepare_socket_dir`], whose verdict is the
//! compiled core's: `bend/fsmode.bend`, law `socket_dir_owned`).

use std::os::unix::fs::{DirBuilderExt, MetadataExt};
use std::path::{Path, PathBuf};

use anyhow::{anyhow, Context as _, Result};
use eukhe_bend::rules::fsmode::{self, DirVerdict, Node, Why};
use eukhe_types::platform::access::current_uid;

use crate::paths::hash_key;

/// Default directory holding daemon socket files: `eukhe-<uid>` in
/// `$TMPDIR` (else `/tmp`).
#[must_use]
pub fn socket_dir() -> PathBuf {
    let tmp = std::env::var_os("TMPDIR").map_or_else(|| PathBuf::from("/tmp"), PathBuf::from);
    tmp.join(format!("eukhe-{}", current_uid()))
}

/// What [`prepare_socket_dir`] did with a safe socket dir.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SocketDir {
    /// The dir was missing: it is created with the mode the core gives
    /// (0700), then checked.
    Created,
    /// The dir exists and passes the check.
    Used,
}

/// Make `dir` ready to hold daemon sockets. The verdict is the compiled
/// core's (`eukhe_bend::rules::fsmode::socket_dir`, law `socket_dir_owned`
/// and `fsmode_ffi_answers`): a missing dir (and its missing parents) is
/// created with mode 0700 in one step, with no window. An existing dir,
/// and the dir after a create, must be a real directory (not a symbolic
/// link), owned by this process's uid, with no group or other write bit.
/// Else the bind is refused: another user could replace the socket in
/// that dir and read every frame. Read and search bits are harmless: the
/// socket is 0600 and the peer rule drops other uids.
///
/// # Errors
///
/// Returns an error that names the dir, what was found and what to do
/// when the dir is not safe, or when it cannot be inspected or created.
pub(crate) fn prepare_socket_dir(dir: &Path) -> Result<SocketDir> {
    let found = match std::fs::symlink_metadata(dir) {
        Ok(found) => Some(found),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => {
            return Err(error).with_context(|| format!("inspect the socket dir {}", dir.display()))
        }
    };
    match verdict(found.as_ref()) {
        DirVerdict::Use => Ok(SocketDir::Used),
        DirVerdict::Refuse(why) => Err(refused(dir, why, found.as_ref())),
        DirVerdict::Create(mode) => {
            std::fs::DirBuilder::new()
                .recursive(true)
                .mode(mode)
                .create(dir)
                .with_context(|| format!("create the socket dir {}", dir.display()))?;
            // A dir another user created between the look and the create
            // fails the same check.
            let created = std::fs::symlink_metadata(dir)
                .with_context(|| format!("inspect the socket dir {}", dir.display()))?;
            match verdict(Some(&created)) {
                DirVerdict::Use => Ok(SocketDir::Created),
                DirVerdict::Refuse(why) => Err(refused(dir, why, Some(&created))),
                DirVerdict::Create(_) => Err(anyhow!(
                    "the socket dir {} is still missing after it was created",
                    dir.display()
                )),
            }
        }
    }
}

/// The core's verdict on what `symlink_metadata` found (`None`: nothing).
fn verdict(found: Option<&std::fs::Metadata>) -> DirVerdict {
    let own_uid = current_uid();
    match found {
        None => fsmode::socket_dir(Node::Missing, 0, own_uid, 0),
        Some(found) => {
            let file_type = found.file_type();
            let node = if file_type.is_symlink() {
                Node::Link
            } else if file_type.is_dir() {
                Node::Dir
            } else {
                Node::Other
            };
            fsmode::socket_dir(node, found.uid(), own_uid, found.mode() & 0o7777)
        }
    }
}

/// The error of a refused socket dir: what was found and what to do.
fn refused(dir: &Path, why: Why, found: Option<&std::fs::Metadata>) -> anyhow::Error {
    let own_uid = current_uid();
    let problem = match why {
        Why::Link => "is a symbolic link".to_string(),
        Why::NotDir => "is not a directory".to_string(),
        Why::Owner => format!("is owned by uid {}", found.map_or(0, MetadataExt::uid)),
        Why::Mode => format!(
            "has mode {:04o}, so other users can replace its sockets",
            found.map_or(0, |found| found.mode() & 0o7777)
        ),
    };
    anyhow!(
        "the socket dir {} {problem}. eukhe binds its sockets only in a real directory \
         that uid {own_uid} owns and that no other user can write. Remove that path (or, \
         if it is your own directory, run `chmod go-w` on it), or pass --daemon-socket \
         with a path in a private directory.",
        dir.display()
    )
}

/// Default supervisor endpoint: `daemon.sock` in the socket dir.
#[must_use]
pub fn default_daemon_socket_path() -> PathBuf {
    socket_dir().join("daemon.sock")
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
