//! Where the per-user daemon listens by default: `daemon.sock` in the run
//! dir of the agent state dir (`<agent dir>/run`, default `~/.eukhe/run`),
//! where no program's temp-dir grant reaches it. On Linux the endpoint is
//! an abstract socket named by that path (`transport`); elsewhere it is a
//! socket file there. Naming only: the daemon checks the dir before it
//! binds there.
//!
//! Releases up to 0.10.73 listened in `eukhe-<uid>` under `$TMPDIR`
//! ([`legacy_daemon_socket_path`]); a launcher stops a daemon still
//! serving there.

use std::path::PathBuf;

use crate::platform::access::current_uid;
use crate::platform::dirs::{agent_dir, RUN_DIR_NAME};

/// Default directory of the daemon's and its workers' sockets: the agent
/// dir's run dir. Without an agent dir (no `HOME`, no override) the
/// earlier per-user temp dir ([`legacy_socket_dir`]); the daemon itself
/// refuses to start without an agent dir.
#[must_use]
pub fn socket_dir() -> PathBuf {
    agent_dir().map_or_else(legacy_socket_dir, |dir| dir.join(RUN_DIR_NAME))
}

/// Default supervisor endpoint: `daemon.sock` in the [`socket_dir`].
#[must_use]
pub fn default_daemon_socket_path() -> PathBuf {
    socket_dir().join("daemon.sock")
}

/// The socket dir of releases up to 0.10.73: `eukhe-<uid>` in `$TMPDIR`
/// (else `/tmp`).
#[must_use]
pub fn legacy_socket_dir() -> PathBuf {
    let tmp = std::env::var_os("TMPDIR").map_or_else(|| PathBuf::from("/tmp"), PathBuf::from);
    tmp.join(format!("eukhe-{}", current_uid()))
}

/// The default supervisor socket of releases up to 0.10.73: `daemon.sock`
/// in the [`legacy_socket_dir`].
#[must_use]
pub fn legacy_daemon_socket_path() -> PathBuf {
    legacy_socket_dir().join("daemon.sock")
}
