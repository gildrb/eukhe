//! Where the per-user daemon listens by default (TS `daemon-socket.ts`
//! `defaultDaemonSocketPath`): `daemon.sock` in `eukhe-<uid>` under
//! `$TMPDIR` (else `/tmp`). Naming only: the daemon checks the dir before
//! it binds there.

use std::path::PathBuf;

use crate::platform::access::current_uid;

/// Default directory holding daemon socket files: `eukhe-<uid>` in
/// `$TMPDIR` (else `/tmp`).
#[must_use]
pub fn socket_dir() -> PathBuf {
    let tmp = std::env::var_os("TMPDIR").map_or_else(|| PathBuf::from("/tmp"), PathBuf::from);
    tmp.join(format!("eukhe-{}", current_uid()))
}

/// Default supervisor endpoint: `daemon.sock` in the [`socket_dir`].
#[must_use]
pub fn default_daemon_socket_path() -> PathBuf {
    socket_dir().join("daemon.sock")
}
