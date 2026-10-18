//! A daemon process an e2e test spawned: stopped with its whole process
//! tree on drop, plus the socket readiness polls. Binary-agnostic: the CLI
//! e2e tests include it too.

#![allow(dead_code)] // each including test binary uses its own subset

use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command};
use std::time::{Duration, Instant};

/// The running daemon serving `socket`. Dropping it stops the supervisor
/// AND its tree: the session workers run detached in their own process
/// groups, so a supervisor-only kill would leave them running over a temp
/// dir the test is about to delete (see [`stop_daemon_tree`]).
pub struct Daemon {
    pub child: Child,
    pub socket: PathBuf,
}

impl Drop for Daemon {
    fn drop(&mut self) {
        stop_daemon_tree(&mut self.child, &self.socket);
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

    /// A crash: `SIGKILL` the supervisor alone and reap it. Its workers
    /// live on (orphaned) for the test to observe; this guard still stops
    /// them on drop unless a successor supervisor serves the socket by then.
    pub fn kill_supervisor(&mut self) {
        self.child.kill().expect("SIGKILL the supervisor");
        self.child.wait().expect("reap the supervisor");
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

/// The bound on the whole teardown: every killed process must have exited
/// by then (`SIGKILL` cannot be caught, so only a wedged kernel misses it).
const TREE_EXIT_BOUND: Duration = Duration::from_secs(10);

/// Stop `supervisor` (the daemon serving `socket`) and every process of its
/// tree, then wait (bounded) for all of them to exit.
///
/// The tree is the supervisor's children plus every process carrying the
/// worker's supervisor-socket env for `socket`: the session workers (each
/// leads its own process group, killed whole) and what they started, a
/// kernel in its own group included - also workers a crashed supervisor
/// orphaned earlier in the test. A running supervisor is frozen
/// (`SIGSTOP`) first, so it cannot spawn or relaunch a worker while its
/// tree is collected. A supervisor that already died leaves its orphans
/// to a successor serving the same socket (a restart test's re-adopted
/// workers); that successor's own guard stops them.
///
/// Best effort by design: this runs in `Drop`, a failing test's unwind
/// included, where a panic would abort the whole test binary.
pub fn stop_daemon_tree(supervisor: &mut Child, socket: &Path) {
    let running = matches!(supervisor.try_wait(), Ok(None));
    let deadline = Instant::now() + TREE_EXIT_BOUND;
    #[cfg(target_os = "linux")]
    let children = if running {
        tree::freeze_and_pin_children(supervisor.id())
    } else {
        Vec::new()
    };
    let _ = supervisor.kill();
    let _ = supervisor.wait();
    #[cfg(target_os = "linux")]
    {
        let owns_tree = running || !tree::successor_serves(socket, supervisor.id());
        tree::kill_and_wait(&children, deadline);
        while owns_tree && Instant::now() < deadline {
            let members = tree::pin_members(socket);
            if members.is_empty() {
                break;
            }
            tree::kill_and_wait(&members, deadline);
        }
    }
    #[cfg(not(target_os = "linux"))]
    let _ = (running, deadline, socket);
}

/// The `/proc` census and the pinned (`pidfd`) kills behind
/// [`stop_daemon_tree`].
#[cfg(target_os = "linux")]
mod tree {
    use std::os::fd::OwnedFd;
    use std::os::unix::ffi::OsStrExt;
    use std::path::Path;
    use std::time::Instant;

    use rustix::event::{poll, PollFd, PollFlags, Timespec};
    use rustix::process::{
        getpgid, kill_process, kill_process_group, pidfd_open, pidfd_send_signal, Pid, PidfdFlags,
        Signal,
    };

    /// The env var the supervisor stamps on every worker it spawns (and the
    /// worker's own children inherit).
    const SUPERVISOR_SOCKET_ENV: &str = "EUKHE_INTERNAL_DAEMON_SUPERVISOR_SOCKET";

    fn pid(raw: u32) -> Option<Pid> {
        i32::try_from(raw).ok().and_then(Pid::from_raw)
    }

    fn proc_pids() -> impl Iterator<Item = u32> {
        std::fs::read_dir("/proc")
            .into_iter()
            .flatten()
            .flatten()
            .filter_map(|entry| entry.file_name().to_str()?.parse().ok())
    }

    /// `/proc/<pid>/stat`'s parent pid (the field after the parenthesized
    /// command name, which may itself contain spaces or parentheses).
    fn parent_of(pid: u32) -> Option<u32> {
        let stat = std::fs::read_to_string(format!("/proc/{pid}/stat")).ok()?;
        let (_, after_name) = stat.rsplit_once(')')?;
        after_name.split_whitespace().nth(1)?.parse().ok()
    }

    fn nul_fields(pid: u32, file: &str) -> Vec<Vec<u8>> {
        std::fs::read(format!("/proc/{pid}/{file}"))
            .unwrap_or_default()
            .split(|byte| *byte == 0)
            .map(<[u8]>::to_vec)
            .collect()
    }

    /// Whether `pid` carries the worker env naming `socket`.
    fn carries_marker(pid: u32, socket: &Path) -> bool {
        let mut marker = format!("{SUPERVISOR_SOCKET_ENV}=").into_bytes();
        marker.extend_from_slice(socket.as_os_str().as_bytes());
        nul_fields(pid, "environ").contains(&marker)
    }

    /// Freeze the running supervisor and pin its current children. Frozen
    /// and unreaped, it keeps every child's pid from being recycled, and a
    /// child it forked but has not exec'd yet is among them.
    pub(super) fn freeze_and_pin_children(supervisor: u32) -> Vec<(u32, OwnedFd)> {
        if let Some(supervisor) = pid(supervisor) {
            let _ = kill_process(supervisor, Signal::STOP);
        }
        proc_pids()
            .filter(|candidate| parent_of(*candidate) == Some(supervisor))
            .filter_map(|child| Some((child, pidfd_open(pid(child)?, PidfdFlags::empty()).ok()?)))
            .collect()
    }

    /// Pin every live process carrying the worker env for `socket`. The
    /// marker is re-read after the pin, so a pid recycled between the
    /// census and the pin is never taken for a member.
    pub(super) fn pin_members(socket: &Path) -> Vec<(u32, OwnedFd)> {
        let own = std::process::id();
        proc_pids()
            .filter(|candidate| *candidate != own && carries_marker(*candidate, socket))
            .filter_map(|member| {
                let fd = pidfd_open(pid(member)?, PidfdFlags::empty()).ok()?;
                carries_marker(member, socket).then_some((member, fd))
            })
            .collect()
    }

    /// Whether another live supervisor serves `socket` (a restart test's
    /// successor): a process other than `predecessor` whose argv names the
    /// socket after `--socket` or `--daemon-socket`.
    pub(super) fn successor_serves(socket: &Path, predecessor: u32) -> bool {
        let socket = socket.as_os_str().as_bytes();
        proc_pids()
            .filter(|candidate| *candidate != predecessor)
            .any(|candidate| {
                nul_fields(candidate, "cmdline").windows(2).any(|pair| {
                    (pair[0] == b"--socket" || pair[0] == b"--daemon-socket") && pair[1] == socket
                })
            })
    }

    /// `SIGKILL` each pinned process (and the process group it leads), then
    /// wait for each to exit, at most until `deadline`.
    pub(super) fn kill_and_wait(targets: &[(u32, OwnedFd)], deadline: Instant) {
        for (member, fd) in targets {
            if let Some(raw) = pid(*member) {
                if getpgid(Some(raw)).is_ok_and(|group| group == raw) {
                    let _ = kill_process_group(raw, Signal::KILL);
                }
            }
            let _ = pidfd_send_signal(fd, Signal::KILL);
        }
        for (_, fd) in targets {
            let budget = deadline.saturating_duration_since(Instant::now());
            let timeout = Timespec {
                tv_sec: i64::try_from(budget.as_secs()).unwrap_or(i64::MAX),
                tv_nsec: budget.subsec_nanos().into(),
            };
            // A pidfd polls readable once its process has exited.
            let mut fds = [PollFd::new(fd, PollFlags::IN)];
            let _ = poll(&mut fds, Some(&timeout));
        }
    }
}
