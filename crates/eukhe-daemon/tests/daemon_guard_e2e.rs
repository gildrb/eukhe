//! The e2e `Daemon` guard (`support/process.rs`) stops the supervisor's
//! whole tree: the session workers run detached in their own process
//! groups, so a guard that killed only the supervisor left every worker
//! running over the temp dir its test then deleted. Both tests pin the
//! worker (pidfd) before the drop and require it exited once the drop
//! returns; the supervisor-lost exit window stays at its 5-minute default,
//! so the worker's own orphan exit cannot explain the death.
#![cfg(target_os = "linux")]

use std::os::fd::OwnedFd;
use std::path::Path;
use std::time::{Duration, Instant};

use rustix::event::{poll, PollFd, PollFlags, Timespec};
use rustix::process::{pidfd_open, Pid, PidfdFlags};
use serde_json::json;

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
#[path = "support/wire_client.rs"]
mod wire_client;

use process::Daemon;
use wire_client::WireClient;

const BUDGET: Duration = Duration::from_secs(60);

/// A supervisor with one scripted session; answers the guard and the
/// pinned worker.
fn daemon_with_a_worker(dir: &Path) -> (Daemon, OwnedFd) {
    let socket = dir.join("daemon.sock");
    let agent_dir = dir.join("agent");
    let sessions = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions).expect("sessions dir");
    let script = dir.join("script.json");
    std::fs::write(
        &script,
        json!({ "responses": [{ "text": "hi" }] }).to_string(),
    )
    .expect("write the script");
    let daemon = Daemon::spawn_listening(
        &mut daemon::supervisor_command(&socket, &agent_dir),
        &socket,
        BUDGET,
    );
    let mut client = WireClient::connect(&socket);
    let created = client.request(
        &json!({ "type": "create", "config": {
            "cwd": dir.to_string_lossy(),
            "sessionDir": sessions.to_string_lossy(),
            "script": script.to_string_lossy(),
        }}),
        BUDGET,
    );
    assert_eq!(created["success"], true, "create: {created}");
    let workers = children_of(daemon.child.id());
    assert_eq!(workers.len(), 1, "one worker child: {workers:?}");
    let worker = pidfd_open(
        Pid::from_raw(i32::try_from(workers[0]).expect("pid")).expect("pid"),
        PidfdFlags::empty(),
    )
    .expect("pin the worker");
    (daemon, worker)
}

/// The supervisor's live children (`/proc/<pid>/stat`'s parent field).
fn children_of(parent: u32) -> Vec<u32> {
    std::fs::read_dir("/proc")
        .expect("read /proc")
        .flatten()
        .filter_map(|entry| entry.file_name().to_str()?.parse::<u32>().ok())
        .filter(|pid| {
            std::fs::read_to_string(format!("/proc/{pid}/stat"))
                .ok()
                .and_then(|stat| {
                    let (_, after_name) = stat.rsplit_once(')')?;
                    after_name.split_whitespace().nth(1)?.parse::<u32>().ok()
                })
                == Some(parent)
        })
        .collect()
}

/// Whether the pinned process has exited (its pidfd polls readable).
fn exited(worker: &OwnedFd) -> bool {
    let mut fds = [PollFd::new(worker, PollFlags::IN)];
    let now = Timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    poll(&mut fds, Some(&now)).expect("poll the worker pidfd") == 1
}

#[test]
fn a_dropped_daemon_leaves_no_worker_alive() {
    let dir = tempfile::tempdir().expect("temp dir");
    let (daemon, worker) = daemon_with_a_worker(dir.path());
    assert!(!exited(&worker), "the worker runs before the drop");

    let started = Instant::now();
    drop(daemon);
    assert!(
        exited(&worker),
        "the worker outlived its dropped daemon guard"
    );
    assert!(
        started.elapsed() < Duration::from_secs(10),
        "the teardown outlived its bound: {:?}",
        started.elapsed()
    );
}

#[test]
fn a_crashed_daemons_guard_stops_its_orphaned_worker() {
    let dir = tempfile::tempdir().expect("temp dir");
    let (mut daemon, worker) = daemon_with_a_worker(dir.path());

    // The crash leaves the worker running, orphaned.
    daemon.kill_supervisor();
    assert!(
        !exited(&worker),
        "the detached worker survives its supervisor's SIGKILL"
    );

    drop(daemon);
    assert!(
        exited(&worker),
        "the orphaned worker outlived its crashed daemon's guard"
    );
}
