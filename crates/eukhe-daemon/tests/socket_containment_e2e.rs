//! Socket containment e2e: a supervisor on a custom socket keeps every
//! endpoint it mints - its own socket, its workers' sockets, their cleanup
//! lock dirs - under that socket's directory, never the per-user default
//! socket dir (`<TMPDIR>/eukhe-<uid>`), and leaves none behind: a stopped
//! worker's socket is gone with it, and the leftovers a dead predecessor
//! on the same socket left are reaped when the supervisor starts.
//!
//! The supervisor runs with `TMPDIR` pinned to a fixture dir, so "the
//! default socket dir" is observable here without ever touching the real
//! per-user one. Linux-only (`/proc` liveness), like the other
//! eukhe-daemon e2e verifiers.
#![cfg(target_os = "linux")]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

struct Daemon {
    child: Child,
}

impl Drop for Daemon {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

// The timeout panic path cannot wait on the child; the test process exits
// immediately afterwards, reaping it.
#[allow(clippy::zombie_processes)]
fn spawn_supervisor(socket: &Path, agent_dir: &Path, tmp_dir: &Path) -> Daemon {
    let child = Command::new(env!("CARGO_BIN_EXE_eukhe-daemon"))
        .arg("supervisor")
        .arg("--socket")
        .arg(socket)
        .arg("--agent-dir")
        .arg(agent_dir)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .env_remove("PRIME_API_KEY")
        .env_remove("EUKHE_CODING_AGENT_DIR")
        .env_remove("EUKHE_DAEMON_SOCKET")
        .env("TMPDIR", tmp_dir)
        .spawn()
        .expect("spawn eukhe-daemon supervisor");
    let deadline = Instant::now() + Duration::from_secs(10);
    while Instant::now() < deadline {
        if UnixStream::connect(socket).is_ok() {
            return Daemon { child };
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    panic!("supervisor socket never appeared");
}

/// One client connection over the supervisor socket.
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    /// Connect and read the hello. The supervisor accepts only once its
    /// boot passes (the predecessor reap, the stale-endpoint sweep) ran,
    /// so a hello proves the boot sweep is done.
    fn connect(socket: &Path) -> Client {
        let stream = UnixStream::connect(socket).expect("connect");
        let writer = stream.try_clone().expect("clone");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
        };
        let hello = client.read_line();
        assert_eq!(hello["type"], "daemon_hello");
        client
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        let deadline = Instant::now() + Duration::from_mins(2);
        self.reader
            .get_mut()
            .set_read_timeout(Some(Duration::from_millis(100)))
            .expect("timeout");
        loop {
            match self.reader.read_line(&mut line) {
                Ok(0) => panic!("supervisor closed the connection"),
                Ok(_) if line.trim().is_empty() => line.clear(),
                Ok(_) => return serde_json::from_str(line.trim()).expect("parse line"),
                Err(error) => {
                    assert!(
                        Instant::now() < deadline,
                        "timed out waiting for supervisor line: {error}"
                    );
                }
            }
        }
    }

    fn request(&mut self, id: &str, command: &Value) -> Value {
        let mut line = serde_json::to_string(&json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "command": command,
        }))
        .expect("serialize command");
        line.push('\n');
        self.writer.write_all(line.as_bytes()).expect("send");
        self.writer.flush().expect("flush");
        loop {
            let response = self.read_line();
            if response.get("id").and_then(Value::as_str) == Some(id) {
                return response;
            }
        }
    }
}

/// The sorted entries of a directory.
fn entries(dir: &Path) -> Vec<PathBuf> {
    let mut entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read dir")
        .map(|entry| entry.expect("dir entry").path())
        .collect();
    entries.sort();
    entries
}

/// Liveness that ignores zombies (a killed child nobody has reaped yet
/// keeps its `/proc` entry until the status is collected).
fn process_alive(pid: u64) -> bool {
    let Ok(stat) = std::fs::read_to_string(format!("/proc/{pid}/stat")) else {
        return false;
    };
    let Some((_, rest)) = stat.rsplit_once(')') else {
        return false;
    };
    let state = rest.split_whitespace().next().unwrap_or_default();
    !state.starts_with('Z') && !state.starts_with('X')
}

/// The worker socket path and pid the session's descriptor records.
fn worker_of(agent_dir: &Path, socket: &Path, session_id: &str) -> (PathBuf, u64) {
    let descriptor_dir = eukhe_daemon::descriptor::descriptor_dir(agent_dir, socket);
    let descriptor = std::fs::read_dir(&descriptor_dir)
        .expect("descriptor dir readable")
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().and_then(|ext| ext.to_str()) == Some("json"))
        .filter_map(|path| std::fs::read_to_string(path).ok())
        .filter_map(|content| serde_json::from_str::<Value>(&content).ok())
        .find(|descriptor| descriptor.to_string().contains(session_id))
        .expect("the session worker's descriptor");
    (
        PathBuf::from(
            descriptor["socketPath"]
                .as_str()
                .expect("worker socket path"),
        ),
        descriptor["pid"].as_u64().expect("worker pid"),
    )
}

/// The guard against the per-user socket dir filling up with worker
/// sockets of test (and custom-socket) daemons: the worker socket lives
/// beside the supervisor's socket while the session runs, the default
/// socket dir never appears, a stopped session leaves no worker socket,
/// and a dead predecessor's worker socket and orphaned lock dir are gone
/// once the supervisor serves.
#[test]
fn a_custom_socket_supervisor_keeps_and_cleans_its_endpoints_beside_its_socket() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket_dir = dir.path().join("sock");
    let socket = socket_dir.join("d.sock");
    let agent_dir = dir.path().join("agent");
    let tmp_dir = dir.path().join("tmp");
    for path in [&socket_dir, &agent_dir.join("sessions"), &tmp_dir] {
        std::fs::create_dir_all(path).expect("fixture dir");
    }

    // A dead predecessor's leftovers beside this socket, named the way
    // this socket's worker endpoints are: a worker socket nobody listens
    // on, and the cleanup lock dir of a holder that crashed.
    let leftover = |worker_id: &str| {
        let minted = eukhe_daemon::socket::worker_socket_path(&socket, worker_id);
        socket_dir.join(minted.file_name().expect("worker socket name"))
    };
    let stale_socket = leftover("dead00000000");
    drop(UnixListener::bind(&stale_socket).expect("bind stale worker socket"));
    let orphan_lock = PathBuf::from(format!("{}.lock", leftover("gone00000000").display()));
    std::fs::create_dir(&orphan_lock).expect("orphan lock dir");
    let crashed =
        filetime::FileTime::from_system_time(std::time::SystemTime::now() - Duration::from_mins(1));
    filetime::set_file_mtime(&orphan_lock, crashed).expect("age the orphan lock");

    let daemon = spawn_supervisor(&socket, &agent_dir, &tmp_dir);
    let mut client = Client::connect(&socket);
    assert_eq!(
        entries(&socket_dir),
        vec![socket.clone()],
        "the boot sweep reaps the predecessor's dead worker endpoints"
    );

    let script = dir.path().join("faux.json");
    std::fs::write(
        &script,
        json!({ "engine": "faux", "responses": [{ "text": "contained" }] }).to_string(),
    )
    .expect("write faux script");
    let created = client.request(
        "create",
        &json!({
            "type": "create",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": agent_dir.join("sessions").to_string_lossy(),
                "script": script.to_string_lossy(),
                "name": "containment",
            },
        }),
    );
    assert_eq!(created["success"], true, "create failed: {created}");
    let active_id = created["data"]["activeSessionId"]
        .as_str()
        .or_else(|| created["data"]["id"].as_str())
        .expect("active session id")
        .to_string();
    let session_id = created["data"]["sessionId"]
        .as_str()
        .expect("durable session id");

    let (worker_socket, worker_pid) = worker_of(&agent_dir, &socket, session_id);
    let mut live = vec![socket.clone(), worker_socket];
    live.sort();
    assert_eq!(
        entries(&socket_dir),
        live,
        "the live worker's socket sits beside the supervisor's"
    );
    assert_eq!(
        entries(&tmp_dir),
        Vec::<PathBuf>::new(),
        "nothing lands in the default socket dir"
    );

    let killed = client.request(
        "kill",
        &json!({ "type": "kill", "activeSessionId": active_id }),
    );
    assert_eq!(killed["success"], true, "kill failed: {killed}");
    // The worker unlinks its socket on its routed close, before it exits.
    let deadline = Instant::now() + Duration::from_secs(30);
    while process_alive(worker_pid) && Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(50));
    }
    assert!(
        !process_alive(worker_pid),
        "the worker must exit on the stop"
    );
    assert_eq!(
        entries(&socket_dir),
        vec![socket.clone()],
        "the stopped worker leaves no socket or lock dir behind"
    );
    assert_eq!(
        entries(&tmp_dir),
        Vec::<PathBuf>::new(),
        "nothing lands in the default socket dir"
    );

    drop(client);
    drop(daemon);
}
