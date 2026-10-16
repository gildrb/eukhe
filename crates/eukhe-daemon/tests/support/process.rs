//! A daemon process an e2e test spawned: `SIGKILL`ed and reaped on drop,
//! plus the socket readiness polls. Binary-agnostic: the CLI e2e tests
//! include it too.

#![allow(dead_code)] // each including test binary uses its own subset

use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command};
use std::time::{Duration, Instant};

/// The running daemon serving `socket`; `SIGKILL`ed and reaped on drop.
pub struct Daemon {
    pub child: Child,
    pub socket: PathBuf,
}

impl Drop for Daemon {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

impl Daemon {
    /// Spawn `command`, the daemon for `socket`, without waiting for it.
    #[allow(clippy::zombie_processes)]
    pub fn spawn(command: &mut Command, socket: &Path) -> Daemon {
        let child = command.spawn().expect("spawn the daemon");
        Daemon {
            child,
            socket: socket.to_path_buf(),
        }
    }

    /// Spawn `command` and wait until its socket file appears.
    pub fn spawn_bound(command: &mut Command, socket: &Path, timeout: Duration) -> Daemon {
        let daemon = Daemon::spawn(command, socket);
        wait_socket_file(socket, timeout);
        daemon
    }

    /// Spawn `command` and wait until its socket accepts connections.
    pub fn spawn_listening(command: &mut Command, socket: &Path, timeout: Duration) -> Daemon {
        let daemon = Daemon::spawn(command, socket);
        wait_socket_accepts(socket, timeout);
        daemon
    }
}

/// Wait until the socket file exists.
pub fn wait_socket_file(socket: &Path, timeout: Duration) {
    let deadline = Instant::now() + timeout;
    while !socket.exists() {
        assert!(
            Instant::now() < deadline,
            "socket {} never appeared",
            socket.display()
        );
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// Wait until the socket accepts connections (a restarted supervisor parks
/// on the stale socket file before replacing it, so the file's existence is
/// not readiness).
pub fn wait_socket_accepts(socket: &Path, timeout: Duration) {
    let deadline = Instant::now() + timeout;
    while UnixStream::connect(socket).is_err() {
        assert!(
            Instant::now() < deadline,
            "socket {} never came up",
            socket.display()
        );
        std::thread::sleep(Duration::from_millis(20));
    }
}
