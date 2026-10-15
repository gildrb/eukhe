//! A supervisor on an isolated socket and agent dir, its stderr appended
//! to a log file the failure messages can point at.

#![allow(dead_code)] // each including test binary uses its own subset

use std::path::Path;
use std::process::{Child, Stdio};
use std::time::{Duration, Instant};

/// The running supervisor; `SIGKILL`ed on drop.
pub struct Supervisor {
    child: Child,
}

impl Drop for Supervisor {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
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
        let child = super::daemon::daemon_command()
            .arg("supervisor")
            .arg("--socket")
            .arg(socket)
            .arg("--agent-dir")
            .arg(agent_dir)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
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
            .env("EUKHE_DAEMON_WORKER_CONNECT_TIMEOUT_MS", "90000")
            .spawn()
            .expect("spawn the supervisor");
        let supervisor = Supervisor { child };
        let deadline = Instant::now() + Duration::from_mins(3);
        while std::os::unix::net::UnixStream::connect(socket).is_err() {
            assert!(Instant::now() < deadline, "the supervisor never listened");
            std::thread::sleep(Duration::from_millis(20));
        }
        supervisor
    }

    /// `SIGKILL` the supervisor and reap it.
    pub fn kill(mut self) {
        self.child.kill().expect("SIGKILL the supervisor");
        let _ = self.child.wait();
    }
}
