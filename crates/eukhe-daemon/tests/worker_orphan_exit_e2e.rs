//! Worker orphan-exit e2e (TS `exitIfSupervisorOrphanedForTooLong`
//! parity): a session worker whose supervisor socket never answers must
//! exit on the supervisor-lost window instead of lingering forever - even
//! with session work in flight that can never settle - and a worker whose
//! supervisor is reachable must survive the same window. Leaked workers
//! from earlier e2e suites starve later test binaries on the shared
//! mission box, so the exit is load-bearing for test hygiene too (the
//! eukhe-daemon/eukhe-cli spawn helpers arm it with a short window).
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

/// Kill a leftover worker at scope exit (the control case ends alive).
struct WorkerGuard {
    child: Child,
}

impl Drop for WorkerGuard {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Spawn the real `eukhe-daemon worker` binary under a supervisor socket it
/// must monitor, with the supervisor-lost exit window at zero (exit at the
/// first availability check that cannot connect).
fn spawn_worker(dir: &Path, supervisor_socket: &Path) -> WorkerGuard {
    std::fs::create_dir_all(dir.join("agent")).expect("agent dir");
    let child = Command::new(env!("CARGO_BIN_EXE_eukhe-daemon"))
        .arg("worker")
        .env(eukhe_daemon::worker::WORKER_ROLE_ENV, "1")
        .env(
            eukhe_daemon::worker::WORKER_TOKEN_ENV,
            "orphan-e2e-bootstrap-token",
        )
        .env(
            eukhe_daemon::worker::WORKER_ACTIVE_SESSION_ID_ENV,
            "orphan-e2e-session",
        )
        .env(
            eukhe_daemon::worker::WORKER_SOCKET_ENV,
            dir.join("worker.sock"),
        )
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_SOCKET_ENV,
            supervisor_socket,
        )
        .env(
            eukhe_daemon::worker::WORKER_RECOVERY_JOURNAL_ENV,
            dir.join("recovery.jsonl"),
        )
        .env("EUKHE_CODING_AGENT_DIR", dir.join("agent"))
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "0",
        )
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn eukhe-daemon worker");
    WorkerGuard { child }
}

/// Wait until the worker's socket file appears (the worker booted and
/// bound it).
fn wait_worker_socket(socket: &Path) {
    let deadline = Instant::now() + Duration::from_secs(15);
    while !socket.exists() {
        assert!(Instant::now() < deadline, "worker socket never appeared");
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// Wait for the child to exit on its own within `budget`; false when it is
/// still running at the deadline.
fn wait_exit(child: &mut Child, budget: Duration) -> bool {
    let deadline = Instant::now() + budget;
    loop {
        if let Some(status) = child.try_wait().expect("poll worker") {
            assert!(status.success(), "worker exited with {status}");
            return true;
        }
        if Instant::now() >= deadline {
            return false;
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}

#[test]
fn orphaned_worker_exits_when_the_supervisor_socket_never_answers() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    // A supervisor socket nobody ever bound: the worker's availability
    // checks can never connect.
    let supervisor_socket = dir.path().join("never-bound-supervisor.sock");
    let mut worker = spawn_worker(dir.path(), &supervisor_socket);
    wait_worker_socket(&dir.path().join("worker.sock"));
    // The first availability check (1.5s after boot) sees the unreachable
    // socket and the zero window exits the worker.
    assert!(
        wait_exit(&mut worker.child, Duration::from_secs(15)),
        "the orphaned worker exited on the supervisor-lost window"
    );
    // The TS graceful exit owns its socket file: the orphan exit removes
    // it, so a respawn does not wait out the stale-socket path.
    assert!(
        !dir.path().join("worker.sock").exists(),
        "the exited worker removed its socket file"
    );
}

#[test]
fn worker_with_a_reachable_supervisor_survives_the_lost_window() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let supervisor_socket = dir.path().join("live-supervisor.sock");
    let listener = UnixListener::bind(&supervisor_socket).expect("bind supervisor socket");
    let mut worker = spawn_worker(dir.path(), &supervisor_socket);
    wait_worker_socket(&dir.path().join("worker.sock"));
    // Past the first availability check (1.5s) with margin: the reachable
    // supervisor resets the absence timer every check, so the same zero
    // window that exits the orphan case must leave this worker alive.
    std::thread::sleep(Duration::from_secs(4));
    let exited = worker.child.try_wait().expect("poll worker").is_some();
    assert!(
        !exited,
        "the worker survived the lost window while its supervisor answered"
    );
    drop(listener);
}

/// The supervisor under test, `SIGKILLed` at scope exit at the latest.
struct Supervisor {
    child: Child,
}

impl Drop for Supervisor {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// A real supervisor whose workers inherit `lost_window_ms` as their
/// supervisor-lost exit window.
fn spawn_supervisor(socket: &Path, agent_dir: &Path, lost_window_ms: &str) -> Supervisor {
    std::fs::create_dir_all(agent_dir).expect("agent dir");
    let child = Command::new(env!("CARGO_BIN_EXE_eukhe-daemon"))
        .arg("supervisor")
        .arg("--socket")
        .arg(socket)
        .arg("--agent-dir")
        .arg(agent_dir)
        .env("EUKHE_CODING_AGENT_DIR", agent_dir)
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            lost_window_ms,
        )
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn eukhe-daemon supervisor");
    let supervisor = Supervisor { child };
    let deadline = Instant::now() + Duration::from_secs(15);
    while UnixStream::connect(socket).is_err() {
        assert!(Instant::now() < deadline, "supervisor socket never came up");
        std::thread::sleep(Duration::from_millis(20));
    }
    supervisor
}

/// JSONL supervisor client (command envelopes, id-matched responses).
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> Self {
        let stream = UnixStream::connect(socket).expect("connect supervisor");
        stream
            .set_read_timeout(Some(Duration::from_secs(60)))
            .expect("set read timeout");
        let writer = stream.try_clone().expect("clone socket");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
        };
        let hello = client.read_line();
        assert_eq!(hello["type"], "daemon_hello", "{hello}");
        client
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        loop {
            line.clear();
            let read = self
                .reader
                .read_line(&mut line)
                .expect("read supervisor line");
            assert!(read > 0, "supervisor closed the connection");
            if !line.trim().is_empty() {
                return serde_json::from_str(line.trim()).expect("parse supervisor line");
            }
        }
    }

    /// Send one command and return its id-matched response (event lines
    /// in between are skipped).
    fn request(&mut self, id: &str, command: &Value) -> Value {
        let mut line = json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "command": command,
        })
        .to_string();
        line.push('\n');
        self.writer
            .write_all(line.as_bytes())
            .expect("send command");
        loop {
            let response = self.read_line();
            if response["id"] == id {
                return response;
            }
        }
    }
}

/// The process start time of `pid` (`/proc/<pid>/stat` field 22), `None`
/// once the process is gone or a zombie: pairs with the pid to identify
/// the process across a possible pid reuse.
fn live_start_time(pid: u32) -> Option<String> {
    let stat = std::fs::read_to_string(format!("/proc/{pid}/stat")).ok()?;
    // Fields after the parenthesized comm: state is the first, start
    // time the 20th.
    let fields: Vec<&str> = stat.rsplit_once(')')?.1.split_whitespace().collect();
    if fields.first() == Some(&"Z") {
        return None;
    }
    fields.get(19).map(ToString::to_string)
}

/// SIGKILL `pid` at scope exit unless it already exited (a failing run
/// must not leak the very worker it caught lingering).
struct PidGuard {
    pid: u32,
    start_time: String,
}

impl Drop for PidGuard {
    fn drop(&mut self) {
        if live_start_time(self.pid).as_ref() == Some(&self.start_time) {
            let _ = Command::new("kill")
                .arg("-9")
                .arg(self.pid.to_string())
                .status();
        }
    }
}

/// Work that can never settle once the supervisor is gone must not pin
/// the orphan forever: the session's turn waits an hour on its scripted
/// reply, the supervisor is `SIGKILLed` mid-turn, and the worker still
/// exits - ongoing work defers the supervisor-lost exit by at most one
/// more window. Before the bound, the run kept the monitor deferring on
/// every check and the worker lingered (orphaned, reparented to init) for
/// as long as the turn lasted.
#[test]
fn orphaned_worker_with_a_never_ending_run_exits_within_the_bound() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let sessions_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    let script = dir.path().join("script.json");
    std::fs::write(
        &script,
        json!({ "responses": [ { "text": "never in time", "delayMs": 3_600_000 } ] }).to_string(),
    )
    .expect("write script");
    let socket = dir.path().join("daemon.sock");
    let mut supervisor = spawn_supervisor(&socket, &agent_dir, "1000");
    let mut client = Client::connect(&socket);

    let created = client.request(
        "c1",
        &json!({
            "type": "create",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": sessions_dir.to_string_lossy(),
                "script": script.to_string_lossy(),
            },
        }),
    );
    assert_eq!(created["success"], true, "create failed: {created}");
    let session_id = created["data"]["id"]
        .as_str()
        .or_else(|| created["data"]["activeSessionId"].as_str())
        .expect("active session id")
        .to_string();
    let prompted = client.request(
        "p1",
        &json!({ "type": "prompt", "activeSessionId": session_id, "message": "wait forever" }),
    );
    assert_eq!(prompted["success"], true, "prompt failed: {prompted}");

    // The turn is live (streaming on the scripted delay) before the kill.
    let deadline = Instant::now() + Duration::from_secs(30);
    let worker_pid = loop {
        let state = client.request(
            "s1",
            &json!({ "type": "get_state", "activeSessionId": session_id }),
        );
        assert_eq!(state["success"], true, "get_state failed: {state}");
        if state["data"]["isStreaming"] == true {
            break u32::try_from(state["data"]["workerPid"].as_u64().expect("worker pid"))
                .expect("pid fits u32");
        }
        assert!(Instant::now() < deadline, "the turn never started: {state}");
        std::thread::sleep(Duration::from_millis(20));
    };
    let start_time = live_start_time(worker_pid).expect("worker alive");
    let _worker = PidGuard {
        pid: worker_pid,
        start_time: start_time.clone(),
    };

    // Hard-kill the supervisor: the worker's supervisor-lost monitor is the
    // only cleanup left, and the turn will not end on its own for an hour.
    supervisor.child.kill().expect("SIGKILL supervisor");
    let _ = supervisor.child.wait();

    // Bound: the 5s check cadence finds the socket gone, and the next check
    // past two 1s windows exits (~10s); the budget covers slow boxes and
    // stays far below the hour the turn would take.
    let deadline = Instant::now() + Duration::from_secs(90);
    while live_start_time(worker_pid).as_ref() == Some(&start_time) {
        assert!(
            Instant::now() < deadline,
            "orphaned worker {worker_pid} still alive with its turn in flight"
        );
        std::thread::sleep(Duration::from_millis(100));
    }
}
