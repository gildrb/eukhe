//! The process holding a daemon socket, found through the socket itself
//! rather than by process name: a renamed or older build (a pre-rename
//! `prime-agent` supervisor) keeps the socket bound under another name, and
//! the name-based census never sees it.
//!
//! Linux maps the listening socket's inode (`/proc/net/unix`) to the pid
//! whose `/proc/<pid>/fd` holds it. macOS has no `/proc`; the best effort
//! there is the `lsof -U` census the discovery scan already uses, with `ps`
//! for the owner's uid and command line (`ps` joins argv with spaces, so a
//! socket path containing spaces cannot be verified there and the holder is
//! reported, never signaled).
//!
//! A holder is only ever signaled when it is this user's process and its
//! command line is an eukhe-family supervisor (`--mode daemon`) launched on
//! exactly this socket (`--daemon-socket <socket>`, or no socket flag when
//! the socket is the default one, as a service unit starts it).

use std::path::Path;
use std::time::{Duration, Instant};

use eukhe_core::platform::process::{kill_pid, Signal};
use eukhe_types::platform::process::{is_process_alive, process_start_id};

/// Executable names of the product family: this build and the pre-rename
/// one, whose supervisors may still hold the socket after an upgrade.
const FAMILY_NAMES: [&str; 2] = ["eukhe", "prime-agent"];

/// How long a holder gets to exit after SIGTERM (a supervisor stops its
/// workers first) before SIGKILL.
const TERM_GRACE: Duration = Duration::from_secs(5);
/// How long the SIGKILL may take to land.
const KILL_GRACE: Duration = Duration::from_secs(2);

/// One process holding the socket's listener.
#[derive(Debug, Clone)]
pub(crate) struct SocketOwner {
    pub pid: u32,
    /// The command line, for the family check and the error messages.
    pub argv: Vec<String>,
    /// Whether the process runs as this user.
    pub same_user: bool,
    /// The process identity at lookup time: a signal is sent only while
    /// the pid still names this process.
    pub start_id: Option<String>,
}

/// Who holds a socket.
#[derive(Debug, Clone)]
pub(crate) enum SocketHolder {
    /// This user's eukhe-family supervisor launched on this socket: safe to
    /// stop.
    Daemon(SocketOwner),
    /// Anything else; never signaled. `reason` says why.
    Other { owner: SocketOwner, reason: String },
}

impl SocketOwner {
    /// The command line as one string, for messages.
    pub(crate) fn command(&self) -> String {
        self.argv.join(" ")
    }

    /// Stop the holder: SIGTERM, a bounded grace, then SIGKILL. True once
    /// the process is gone (a zombie counts as gone). Every signal is gated
    /// on the start id seen at lookup, so a recycled pid is never hit.
    pub(crate) fn terminate(&self) -> bool {
        let still_same = || {
            is_process_alive(self.pid).unwrap_or(false)
                && (self.start_id.is_none()
                    || process_start_id(self.pid).as_deref() == self.start_id.as_deref())
        };
        let wait_gone = |grace: Duration| {
            let deadline = Instant::now() + grace;
            while still_same() {
                if Instant::now() >= deadline {
                    return false;
                }
                std::thread::sleep(Duration::from_millis(25));
            }
            true
        };
        let Ok(pid) = i32::try_from(self.pid) else {
            return false;
        };
        if !still_same() {
            return true;
        }
        let _ = kill_pid(pid, Signal::Term);
        if wait_gone(TERM_GRACE) {
            return true;
        }
        if still_same() {
            let _ = kill_pid(pid, Signal::Kill);
        }
        wait_gone(KILL_GRACE)
    }

    /// Why this holder must not be stopped; `None` when it is this user's
    /// eukhe-family supervisor on `socket_path`.
    fn refusal(&self, socket_path: &Path) -> Option<String> {
        if !self.same_user {
            return Some("it belongs to another user".to_string());
        }
        let family = |path: &str| {
            Path::new(path)
                .file_name()
                .and_then(|name| name.to_str())
                .map(|name| name.strip_suffix(" (deleted)").unwrap_or(name))
                .is_some_and(|name| {
                    FAMILY_NAMES.iter().any(|family| {
                        name == *family
                            || name
                                .strip_prefix(family)
                                .is_some_and(|rest| rest.starts_with('-'))
                    })
                })
        };
        let executable = eukhe_types::platform::process::process_executable_path(self.pid);
        let named_family = self.argv.first().is_some_and(|argv0| family(argv0))
            || executable
                .as_deref()
                .and_then(Path::to_str)
                .is_some_and(family);
        if !named_family {
            return Some("it is not an eukhe executable".to_string());
        }
        let daemon_mode = self
            .argv
            .windows(2)
            .any(|pair| pair[0] == "--mode" && pair[1] == "daemon")
            || self.argv.iter().any(|arg| arg == "--mode=daemon");
        if !daemon_mode {
            return Some("it is not running in --mode daemon".to_string());
        }
        // A supervisor started without `--daemon-socket` (a service unit)
        // listens on the default socket.
        let socket_arg = self
            .argv
            .windows(2)
            .find(|pair| pair[0] == "--daemon-socket")
            .map(|pair| pair[1].as_str())
            .or_else(|| {
                self.argv
                    .iter()
                    .find_map(|arg| arg.strip_prefix("--daemon-socket="))
            });
        let on_socket = match socket_arg {
            Some(path) => Path::new(path) == socket_path,
            None => socket_path == eukhe_daemon::socket::default_daemon_socket_path(),
        };
        if !on_socket {
            return Some(format!(
                "its command line does not name --daemon-socket {}",
                socket_path.display()
            ));
        }
        None
    }
}

/// The process listening on `socket_path`, classified. `None` when no
/// holder is visible (nothing listens, the platform cannot tell, or the
/// holder's process table entry is unreadable).
pub(crate) fn socket_holder(socket_path: &Path) -> Option<SocketHolder> {
    let owners = listening_owners(socket_path);
    // One listener can be shared by several processes (an inherited fd):
    // any verified supervisor among them is the daemon.
    let mut first_other: Option<(SocketOwner, String)> = None;
    for owner in owners {
        match owner.refusal(socket_path) {
            None => return Some(SocketHolder::Daemon(owner)),
            Some(reason) => {
                if first_other.is_none() {
                    first_other = Some((owner, reason));
                }
            }
        }
    }
    first_other.map(|(owner, reason)| SocketHolder::Other { owner, reason })
}

/// Every process holding the listening socket at `socket_path` (Linux:
/// `/proc/net/unix` inode → `/proc/<pid>/fd`).
#[cfg(target_os = "linux")]
fn listening_owners(socket_path: &Path) -> Vec<SocketOwner> {
    use std::os::unix::fs::MetadataExt as _;
    let Ok(unix) = std::fs::read("/proc/net/unix") else {
        return Vec::new();
    };
    let inodes: Vec<String> = super::scan::parse_proc_net_unix(&unix)
        .into_iter()
        .filter(|(_, path)| Path::new(path) == socket_path)
        .map(|(inode, _)| inode)
        .collect();
    if inodes.is_empty() {
        return Vec::new();
    }
    let own_uid = std::fs::metadata("/proc/self").ok().map(|meta| meta.uid());
    super::scan::proc_socket_inodes()
        .into_iter()
        .filter(|(_, _, held)| inodes.iter().any(|inode| held.contains(inode)))
        .filter_map(|(pid, _, _)| {
            let cmdline = std::fs::read(format!("/proc/{pid}/cmdline")).ok()?;
            let uid = std::fs::metadata(format!("/proc/{pid}")).ok()?.uid();
            Some(SocketOwner {
                pid,
                argv: cmdline
                    .split(|byte| *byte == 0)
                    .filter(|arg| !arg.is_empty())
                    .map(|arg| String::from_utf8_lossy(arg).into_owned())
                    .collect(),
                same_user: own_uid == Some(uid),
                start_id: process_start_id(pid),
            })
        })
        .collect()
}

/// macOS: the `lsof -U` census for the pid, `ps` for the uid and command
/// line (best effort, see the module docs).
#[cfg(target_os = "macos")]
fn listening_owners(socket_path: &Path) -> Vec<SocketOwner> {
    let Some(stdout) = super::scan::capture_stdout("lsof", &["-nP", "-F", "pn", "-U"]) else {
        return Vec::new();
    };
    let ps_field = |pid: u32, field: &str| {
        super::scan::capture_stdout("ps", &["-o", field, "-p", &pid.to_string()])
            .map(|out| out.trim().to_string())
            .filter(|out| !out.is_empty())
    };
    let own_uid = ps_field(std::process::id(), "uid=");
    super::scan::parse_lsof_listeners(&stdout)
        .into_iter()
        .filter(|listener| listener.socket_path == socket_path)
        .filter_map(|listener| {
            let pid = listener.pid;
            let args = ps_field(pid, "args=")?;
            Some(SocketOwner {
                pid,
                argv: args.split_whitespace().map(str::to_string).collect(),
                same_user: own_uid.is_some() && ps_field(pid, "uid=") == own_uid,
                start_id: process_start_id(pid),
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn owner(argv: &[&str], same_user: bool) -> SocketOwner {
        SocketOwner {
            // No live process: the executable lookup answers None, so the
            // family check runs on argv0.
            pid: u32::MAX,
            argv: argv.iter().map(|arg| (*arg).to_string()).collect(),
            same_user,
            start_id: None,
        }
    }

    #[test]
    fn only_a_same_user_family_supervisor_on_this_socket_may_be_stopped() {
        let socket = Path::new("/run/test/daemon.sock");
        let cases: [(&[&str], bool, Option<&str>); 8] = [
            (
                &[
                    "/nix/store/x/libexec/eukhe/prime-agent",
                    "--mode",
                    "daemon",
                    "--daemon-socket",
                    "/run/test/daemon.sock",
                ],
                true,
                None,
            ),
            (
                &[
                    "/opt/eukhe",
                    "--mode=daemon",
                    "--daemon-socket=/run/test/daemon.sock",
                ],
                true,
                None,
            ),
            (
                &[
                    "/opt/eukhe",
                    "--mode",
                    "daemon",
                    "--daemon-socket",
                    "/run/test/daemon.sock",
                ],
                false,
                Some("it belongs to another user"),
            ),
            (
                &[
                    "/usr/bin/python3",
                    "--mode",
                    "daemon",
                    "--daemon-socket",
                    "/run/test/daemon.sock",
                ],
                true,
                Some("it is not an eukhe executable"),
            ),
            (
                &[
                    "/opt/eukhed",
                    "--mode",
                    "daemon",
                    "--daemon-socket",
                    "/run/test/daemon.sock",
                ],
                true,
                Some("it is not an eukhe executable"),
            ),
            (
                &[
                    "/opt/eukhe",
                    "--mode",
                    "rpc",
                    "--daemon-socket",
                    "/run/test/daemon.sock",
                ],
                true,
                Some("it is not running in --mode daemon"),
            ),
            (
                &[
                    "/opt/eukhe",
                    "--mode",
                    "daemon",
                    "--daemon-socket",
                    "/run/other.sock",
                ],
                true,
                Some("its command line does not name --daemon-socket /run/test/daemon.sock"),
            ),
            // No socket flag: only the default socket is this daemon's.
            (
                &["/opt/eukhe", "--mode", "daemon"],
                true,
                Some("its command line does not name --daemon-socket /run/test/daemon.sock"),
            ),
        ];
        for (argv, same_user, expected) in cases {
            assert_eq!(
                owner(argv, same_user).refusal(socket).as_deref(),
                expected,
                "{argv:?}"
            );
        }
    }
}
