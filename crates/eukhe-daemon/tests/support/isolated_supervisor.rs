//! A supervisor on an isolated socket and agent dir, its stderr appended
//! to a log file the failure messages can point at.

#![allow(dead_code)] // each including test binary uses its own subset

use std::path::Path;
use std::time::Duration;

use super::process::Daemon;

/// The running supervisor; its whole process tree is stopped on drop
/// ([`Daemon`]).
pub struct Supervisor {
    daemon: Daemon,
}

impl Supervisor {
    /// Start a supervisor and wait until its socket accepts (a restarted
    /// supervisor parks on the stale socket file before replacing it, so
    /// the file's existence is not readiness).
    pub fn start(socket: &Path, agent_dir: &Path, log: &Path) -> Supervisor {
        let log = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(log)
            .expect("supervisor log");
        let mut command = super::daemon::supervisor_command(socket, agent_dir);
        command
            .stderr(log)
            .env_remove("PRIME_API_KEY")
            .env_remove("EUKHE_CODING_AGENT_DIR")
            // Orphaned workers of a failed run exit soon instead of after
            // the 5-minute default.
            .env(
                eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
                "30000",
            )
            // Parallel e2e load can starve a fresh worker's boot past the
            // 30 s default.
            .env("EUKHE_DAEMON_WORKER_CONNECT_TIMEOUT_MS", "90000");
        Supervisor {
            daemon: Daemon::spawn_listening(&mut command, socket, Duration::from_mins(3)),
        }
    }

    /// A crash: `SIGKILL` the supervisor alone and reap it; its workers
    /// live on until a successor adopts them or this guard drops.
    pub fn kill(&mut self) {
        self.daemon.kill_supervisor();
    }
}
