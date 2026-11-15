//! Socket containment e2e: a supervisor on a custom socket keeps every
//! endpoint it mints - its own socket, its workers' sockets, their pid
//! records and cleanup lock dirs - under that socket's directory, never the
//! per-user default socket dir (`<agent dir>/run`) nor the temp dir of
//! earlier releases (`<TMPDIR>/eukhe-<uid>`), and leaves none behind: a
//! stopped worker's endpoint is gone with it, and the leftovers a dead
//! predecessor on the same socket left are reaped when the supervisor
//! starts.
//!
//! The default socket: two clients share the supervisor in the run dir, a
//! stale socket file and pid record there do not stop it, and a process of
//! another uid is refused at both ends (it cannot talk to the supervisor,
//! and a client does not talk to an endpoint it bound first).
//!
//! The supervisor runs with `TMPDIR` pinned to a fixture dir, so the old
//! default socket dir is observable here without ever touching the real
//! per-user one. Linux-only (`/proc` liveness, abstract endpoints whose
//! listeners leave a pid record beside the path), like the other
//! eukhe-daemon e2e verifiers.
#![cfg(target_os = "linux")]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_command;
use process::Daemon;

fn spawn_supervisor(socket: &Path, agent_dir: &Path, tmp_dir: &Path) -> Daemon {
    Daemon::spawn_listening(
        supervisor_command(socket, agent_dir)
            .env_remove("EUKHE_CODING_AGENT_DIR")
            .env_remove("EUKHE_DAEMON_SOCKET")
            .env("TMPDIR", tmp_dir),
        socket,
        Duration::from_secs(10),
    )
}

/// The socket file a crashed endpoint leaves behind: bound but never
/// listening, so a connect is refused even while a descriptor copy lives.
/// A bound-then-dropped LISTENER gives no such guarantee in a test process:
/// a concurrent test's `fork` copies its descriptor, and the copy keeps the
/// socket accepting until that child's `exec` closes it.
fn bind_dead_socket(path: &Path) {
    let socket = socket2::Socket::new(socket2::Domain::UNIX, socket2::Type::STREAM, None)
        .expect("dead socket fixture: create");
    let address = socket2::SockAddr::unix(path).expect("dead socket fixture: address");
    socket.bind(&address).expect("dead socket fixture: bind");
}

/// The file a live endpoint at `socket` leaves in its dir: its pid record
/// (the endpoint itself is an abstract socket).
fn record(socket: &Path) -> PathBuf {
    eukhe_types::platform::transport::record_path(socket)
}

/// The pid recorded for the endpoint at `socket`.
fn recorded_pid(socket: &Path) -> u32 {
    std::fs::read_to_string(record(socket))
        .expect("pid record")
        .trim()
        .parse()
        .expect("a pid")
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
        let stream = eukhe_types::platform::transport::connect_std(socket).expect("connect");
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
    bind_dead_socket(&stale_socket);
    let orphan_lock = PathBuf::from(format!("{}.lock", leftover("gone00000000").display()));
    std::fs::create_dir(&orphan_lock).expect("orphan lock dir");
    let crashed =
        filetime::FileTime::from_system_time(std::time::SystemTime::now() - Duration::from_mins(1));
    filetime::set_file_mtime(&orphan_lock, crashed).expect("age the orphan lock");

    let daemon = spawn_supervisor(&socket, &agent_dir, &tmp_dir);
    let mut client = Client::connect(&socket);
    assert_eq!(
        entries(&socket_dir),
        vec![record(&socket)],
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
    assert_eq!(
        recorded_pid(&worker_socket),
        u32::try_from(worker_pid).expect("pid")
    );
    let mut live = vec![record(&socket), record(&worker_socket)];
    live.sort();
    assert_eq!(
        entries(&socket_dir),
        live,
        "the live worker's endpoint sits beside the supervisor's"
    );
    assert_eq!(
        entries(&tmp_dir),
        Vec::<PathBuf>::new(),
        "nothing lands in the old default socket dir"
    );
    assert!(
        !agent_dir.join("run").exists(),
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
        vec![record(&socket)],
        "the stopped worker leaves no socket, record or lock dir behind"
    );
    assert_eq!(
        entries(&tmp_dir),
        Vec::<PathBuf>::new(),
        "nothing lands in the old default socket dir"
    );

    drop(client);
    drop(daemon);
}

/// The default socket of `agent_dir`: `daemon.sock` in its run dir.
fn default_socket(agent_dir: &Path) -> PathBuf {
    agent_dir.join("run").join("daemon.sock")
}

/// A client the way eukhe's clients connect: both ends' rules of the
/// compiled core, so the supervisor must run as this uid and be the
/// process recorded for the socket.
fn connect_as_client(
    socket: &Path,
) -> std::io::Result<Box<dyn eukhe_types::platform::transport::BlockingTransportStream>> {
    eukhe_types::platform::transport::connect_blocking(
        socket,
        eukhe_bend::rules::server_peer::PEER_RULES,
    )
}

/// Two clients reach the supervisor on the default socket at once: it
/// listens in the agent dir's run dir (mode 0700), as an abstract socket
/// with no file at the path, and its pid is the one recorded there.
#[test]
fn two_clients_share_the_supervisor_in_the_run_dir() {
    use std::os::unix::fs::PermissionsExt as _;
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let tmp_dir = dir.path().join("tmp");
    for path in [&agent_dir.join("sessions"), &tmp_dir] {
        std::fs::create_dir_all(path).expect("fixture dir");
    }
    let socket = default_socket(&agent_dir);
    let daemon = spawn_supervisor(&socket, &agent_dir, &tmp_dir);
    let mut first = Client::connect(&socket);
    let mut second = Client::connect(&socket);
    for (client, id) in [(&mut first, "one"), (&mut second, "two")] {
        let listed = client.request(id, &json!({ "type": "list" }));
        assert_eq!(listed["success"], true, "{listed}");
    }
    assert!(
        connect_as_client(&socket).is_ok(),
        "the core's rules accept the supervisor"
    );
    let run_dir = agent_dir.join("run");
    let mode = std::fs::metadata(&run_dir)
        .expect("run dir")
        .permissions()
        .mode();
    assert_eq!(mode & 0o777, 0o700, "the run dir is private");
    assert_eq!(
        entries(&run_dir),
        vec![record(&socket)],
        "no socket file, one record"
    );
    assert_eq!(
        Some(recorded_pid(&socket)),
        Some(daemon.child.id()),
        "the record names the supervisor"
    );
    assert_eq!(entries(&tmp_dir), Vec::<PathBuf>::new());
    drop((first, second));
    drop(daemon);
}

/// What a crash leaves in the run dir - a socket file nobody listens on
/// (an earlier release's) and the pid record of a process that is gone -
/// does not stop the next supervisor: it binds, records its own pid, and
/// clients accept it.
#[test]
fn a_stale_socket_and_record_do_not_stop_the_next_supervisor() {
    use std::os::unix::fs::PermissionsExt as _;
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let tmp_dir = dir.path().join("tmp");
    let run_dir = agent_dir.join("run");
    for path in [&agent_dir.join("sessions"), &tmp_dir, &run_dir] {
        std::fs::create_dir_all(path).expect("fixture dir");
    }
    std::fs::set_permissions(&run_dir, std::fs::Permissions::from_mode(0o700)).expect("private");
    let socket = default_socket(&agent_dir);
    bind_dead_socket(&socket);
    // Above the kernel's pid limit (2^22): no process has it.
    std::fs::write(record(&socket), "4194305\n").expect("stale record");
    assert!(connect_as_client(&socket).is_err(), "nothing serves yet");

    let daemon = spawn_supervisor(&socket, &agent_dir, &tmp_dir);
    let _client = Client::connect(&socket);
    assert!(
        connect_as_client(&socket).is_ok(),
        "the new supervisor is accepted"
    );
    assert_eq!(
        Some(recorded_pid(&socket)),
        Some(daemon.child.id()),
        "the stale record is replaced"
    );
    drop(daemon);
}

/// Child mode of [`a_process_of_another_uid_is_refused_at_both_ends`]:
/// this test binary, run as another uid. `connect`: connect to the
/// abstract name and print what came back (`closed` when the listener
/// closed without a frame); `listen`: bind the abstract name first, print
/// `listening`, and hold it.
const OTHER_UID_ROLE: &str = "EUKHE_TEST_OTHER_UID_ROLE";
const OTHER_UID_PATH: &str = "EUKHE_TEST_OTHER_UID_PATH";

#[test]
fn other_uid_child_mode() {
    use std::os::linux::net::SocketAddrExt as _;
    use std::os::unix::ffi::OsStrExt as _;
    let (Some(role), Some(path)) = (
        std::env::var_os(OTHER_UID_ROLE),
        std::env::var_os(OTHER_UID_PATH),
    ) else {
        return;
    };
    let name = std::os::unix::net::SocketAddr::from_abstract_name(path.as_bytes()).expect("name");
    match role.to_str() {
        Some("connect") => {
            let stream = UnixStream::connect_addr(&name).expect("connect");
            stream
                .set_read_timeout(Some(Duration::from_secs(10)))
                .expect("timeout");
            let mut line = String::new();
            match BufReader::new(stream).read_line(&mut line) {
                Ok(0) => println!("other-uid: closed"),
                Ok(_) => println!("other-uid: got {}", line.trim()),
                Err(error) => println!("other-uid: error {error}"),
            }
        }
        Some("listen") => {
            let _listener = std::os::unix::net::UnixListener::bind_addr(&name).expect("bind");
            println!("other-uid: listening");
            std::io::stdout().flush().expect("flush");
            std::thread::sleep(Duration::from_secs(60));
        }
        other => panic!("unknown role {other:?}"),
    }
}

/// This test binary as another uid: a copy others may read and run, run
/// by `unshare` in a user namespace that maps the user's subordinate uids
/// (`/etc/subuid`) and switches to its root, which is a subordinate uid
/// outside. `None` when the host cannot do that (no `unshare --map-auto`,
/// no subordinate uids).
fn other_uid_command(copy_dir: &Path, role: &str, path: &Path) -> Option<std::process::Command> {
    use std::os::unix::fs::PermissionsExt as _;
    let exe = copy_dir.join("other-uid-child");
    if !exe.exists() {
        std::fs::copy(std::env::current_exe().expect("test binary"), &exe)
            .expect("copy test binary");
        std::fs::set_permissions(&exe, std::fs::Permissions::from_mode(0o755)).expect("exe mode");
        std::fs::set_permissions(copy_dir, std::fs::Permissions::from_mode(0o755))
            .expect("dir mode");
    }
    let probe = std::process::Command::new("unshare")
        .args([
            "--user",
            "--map-auto",
            "--setuid",
            "0",
            "--setgid",
            "0",
            "--",
        ])
        .arg(&exe)
        .args(["--exact", "other_uid_child_mode"])
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status();
    if !probe.is_ok_and(|status| status.success()) {
        return None;
    }
    let mut command = std::process::Command::new("unshare");
    command
        .args([
            "--user",
            "--map-auto",
            "--setuid",
            "0",
            "--setgid",
            "0",
            "--",
        ])
        .arg(&exe)
        .args(["--exact", "other_uid_child_mode", "--nocapture"])
        .env(OTHER_UID_ROLE, role)
        .env(OTHER_UID_PATH, path)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null());
    Some(command)
}

/// The first `other-uid:` line a child printed.
fn other_uid_line(child: &mut std::process::Child) -> String {
    let stdout = child.stdout.take().expect("child stdout");
    BufReader::new(stdout)
        .lines()
        .map_while(Result::ok)
        .find(|line| line.starts_with("other-uid: "))
        .unwrap_or_default()
}

/// A process of another uid is refused at both ends: the supervisor
/// closes its connection before a frame (no hello), and a client refuses
/// an abstract name it bound first, even with its pid on record.
#[test]
fn a_process_of_another_uid_is_refused_at_both_ends() {
    let copy_dir = tempfile::Builder::new()
        .prefix("eukhe-other-uid")
        .tempdir_in("/tmp")
        .expect("copy dir");
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let tmp_dir = dir.path().join("tmp");
    for path in [&agent_dir.join("sessions"), &tmp_dir] {
        std::fs::create_dir_all(path).expect("fixture dir");
    }
    let socket = default_socket(&agent_dir);
    let Some(mut connect) = other_uid_command(copy_dir.path(), "connect", &socket) else {
        eprintln!("SKIP: this host cannot run a process as another uid (unshare --map-auto with /etc/subuid)");
        return;
    };
    let daemon = spawn_supervisor(&socket, &agent_dir, &tmp_dir);
    let mut child = connect.spawn().expect("spawn the other uid's client");
    assert_eq!(
        other_uid_line(&mut child),
        "other-uid: closed",
        "the supervisor sends it nothing"
    );
    let _ = child.wait();
    let _client = Client::connect(&socket);
    drop(daemon);

    let squatted = dir.path().join("squat").join("daemon.sock");
    std::fs::create_dir_all(squatted.parent().expect("dir")).expect("squat dir");
    let mut foreign = other_uid_command(copy_dir.path(), "listen", &squatted)
        .expect("probed above")
        .spawn()
        .expect("spawn the other uid's listener");
    assert_eq!(other_uid_line(&mut foreign), "other-uid: listening");
    std::fs::write(record(&squatted), format!("{}\n", foreign.id())).expect("its pid on record");
    let error = connect_as_client(&squatted).expect_err("refused");
    assert_eq!(error.kind(), std::io::ErrorKind::PermissionDenied);
    assert!(error.to_string().contains("not by this user"), "{error}");
    let _ = foreign.kill();
    let _ = foreign.wait();
}
