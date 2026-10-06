//! The launcher replaces a daemon it cannot use (an older eukhe version, a
//! pre-rename `prime-agent` build answering another protocol name) and
//! `shutdown --force` stops a renamed daemon found by its socket.
//!
//! Every launcher run is this test binary re-exec'd in a child mode with
//! the fixture's state environment pinned on its spawn (agent dir, TMPDIR,
//! no inherited daemon socket), so the supervisor it starts never touches
//! the ambient environment's real paths.
#![cfg(unix)]

use std::io::{BufRead as _, BufReader, Write as _};
use std::os::unix::net::UnixStream;
use std::os::unix::process::{CommandExt as _, ExitStatusExt as _};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use serde_json::{json, Value};
use tokio::io::{AsyncBufReadExt as _, AsyncWriteExt as _};

/// Environment keys a surrounding eukhe session sets; none may leak into
/// the launcher or the supervisors it spawns.
const SCRUB_ENV: [&str; 10] = [
    "EUKHE_DAEMON_SOCKET",
    "EUKHE_INTERNAL_DAEMON_WORKER",
    "EUKHE_INTERNAL_DAEMON_WORKER_TOKEN",
    "EUKHE_INTERNAL_DAEMON_WORKER_ACTIVE_SESSION_ID",
    "EUKHE_INTERNAL_DAEMON_WORKER_INSTANCE_ID",
    "EUKHE_INTERNAL_DAEMON_WORKER_RECOVERY_JOURNAL",
    "EUKHE_INTERNAL_DAEMON_SUPERVISOR_SOCKET",
    "EUKHE_INTERNAL_ORPHAN_PROCESS_JOURNAL",
    "EUKHE_INTERNAL_SESSION_LEASES",
    "EUKHE_INTERNAL_SESSION_LEASE_OWNER_ID",
];

/// Child mode: run the launcher against this socket and print the outcome.
const LAUNCHER_SOCKET_ENV: &str = "EUKHE_TEST_REPLACEMENT_LAUNCHER_SOCKET";
/// Child mode: serve a pre-rename daemon's hello on this socket.
const FOREIGN_SOCKET_ENV: &str = "EUKHE_TEST_FOREIGN_DAEMON_SOCKET";
/// The line the foreign child prints once its socket listens.
const FOREIGN_READY: &str = "foreign daemon listening";
/// The version an outdated mock daemon reports.
const OLD_VERSION: &str = "0.0.1-old";

fn cli_binary() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_eukhe"))
}

/// Pin the state environment of a spawned process inside `root`.
fn pin_state_env(command: &mut Command, root: &Path) {
    let agent_dir = root.join("agent");
    let tmp_dir = root.join("tmp");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    std::fs::create_dir_all(&tmp_dir).expect("tmp dir");
    command
        .env("EUKHE_CODING_AGENT_DIR", &agent_dir)
        .env("TMPDIR", &tmp_dir)
        .env("EUKHE_TELEMETRY", "0")
        // A supervisor killed at teardown must not leak its session workers
        // into later test binaries.
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "15000",
        );
    for key in SCRUB_ENV {
        command.env_remove(key);
    }
}

/// Run the launcher (`ensure_daemon_running_with`, the path every
/// daemon-backed mode takes first) in a child process.
fn run_launcher(root: &Path, socket: &Path) -> Output {
    let mut command = Command::new(std::env::current_exe().expect("test binary"));
    command
        .args(["--exact", "launcher_child_mode", "--nocapture"])
        .current_dir(root)
        .env(LAUNCHER_SOCKET_ENV, socket)
        .stdin(Stdio::null());
    pin_state_env(&mut command, root);
    command.output().expect("spawn launcher child")
}

/// The launcher outcome lines the child printed (`ready: ...`,
/// `notice: ...`), libtest's own output filtered out.
fn launcher_report(output: &Output) -> Vec<String> {
    assert!(
        output.status.success(),
        "launcher failed: {}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|line| line.starts_with("ready: ") || line.starts_with("notice: "))
        .map(str::to_string)
        .collect()
}

/// Child mode for the launcher runs (a plain test run without the env var
/// passes trivially).
#[test]
fn launcher_child_mode() {
    let Some(socket) = std::env::var_os(LAUNCHER_SOCKET_ENV) else {
        return;
    };
    let socket = PathBuf::from(socket);
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("runtime");
    let cwd = std::env::current_dir().expect("cwd");
    let ready = runtime
        .block_on(eukhe_cli::ensure_daemon_running_with(
            &cli_binary(),
            &socket,
            &cwd,
        ))
        .expect("ensure the daemon");
    println!("ready: {ready:?}");
    println!("notice: {:?}", ready.notice());
}

/// Child mode: a pre-rename supervisor stand-in. Its argv is the old
/// daemon's (`prime-agent ... --mode daemon --daemon-socket <socket>`, set
/// by the spawner through argv0 and libtest's trailing filters), every
/// connection gets the old protocol name's hello, and every command but
/// `shutdown` gets an empty success. It ignores `shutdown`: only a signal
/// stops it.
#[test]
fn foreign_daemon_child_mode() {
    let Some(socket) = std::env::var_os(FOREIGN_SOCKET_ENV) else {
        return;
    };
    let listener = std::os::unix::net::UnixListener::bind(PathBuf::from(socket)).expect("bind");
    println!("{FOREIGN_READY}");
    std::io::stdout().flush().expect("flush");
    let hello = json!({
        "type": "daemon_hello",
        "protocol": { "name": "prime-agent.daemon", "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION },
        "schemaId": eukhe_types::daemon::DAEMON_SCHEMA_ID,
        "appVersion": "0.9.9-eukhe.1",
    });
    for stream in listener.incoming() {
        let Ok(mut stream) = stream else { continue };
        let hello = hello.clone();
        std::thread::spawn(move || {
            let _ = writeln!(stream, "{hello}");
            let Ok(reader) = stream.try_clone() else {
                return;
            };
            for line in BufReader::new(reader).lines().map_while(Result::ok) {
                let Ok(envelope) = serde_json::from_str::<Value>(&line) else {
                    continue;
                };
                let command = envelope["command"]["type"].as_str().unwrap_or_default();
                if command == "shutdown" {
                    continue;
                }
                let response = json!({
                    "type": "response", "id": envelope["id"], "command": command,
                    "success": true, "data": { "sessions": [] },
                });
                let _ = writeln!(stream, "{response}");
            }
        });
    }
}

/// Spawn the foreign stand-in on `socket` and wait for its ready line.
fn spawn_foreign_daemon(root: &Path, socket: &Path) -> Child {
    let mut command = Command::new(std::env::current_exe().expect("test binary"));
    command
        .arg0("prime-agent")
        .args(["--exact", "foreign_daemon_child_mode", "--nocapture", "--"])
        .args(["--mode", "daemon", "--daemon-socket"])
        .arg(socket)
        .env(FOREIGN_SOCKET_ENV, socket)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null());
    pin_state_env(&mut command, root);
    let mut child = command.spawn().expect("spawn foreign daemon");
    let stdout = child.stdout.take().expect("foreign stdout");
    let mut lines = BufReader::new(stdout).lines().map_while(Result::ok);
    let ready = lines.any(|line| line == FOREIGN_READY);
    assert!(ready, "the foreign daemon never listened");
    // Keep draining: libtest's own later lines (its slow-test notice) must
    // not hit a closed pipe and end the stand-in early.
    std::thread::spawn(move || lines.for_each(drop));
    child
}

/// Kills the foreign stand-in on scope exit when a test left it running.
struct ForeignDaemon(Child);

impl Drop for ForeignDaemon {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// Wait (bounded) for the stand-in to exit; its exit status.
fn wait_exit(child: &mut Child) -> Option<std::process::ExitStatus> {
    let deadline = Instant::now() + Duration::from_secs(15);
    loop {
        if let Some(status) = child.try_wait().expect("wait foreign daemon") {
            return Some(status);
        }
        if Instant::now() > deadline {
            return None;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// The hello of whatever listens on `socket` now.
fn read_hello(socket: &Path) -> Value {
    let stream = UnixStream::connect(socket).expect("daemon socket");
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .expect("read timeout");
    let mut hello = String::new();
    BufReader::new(stream)
        .read_line(&mut hello)
        .expect("read hello");
    serde_json::from_str(&hello).expect("parse hello")
}

/// The replacement supervisor's identity fields from its hello.
fn identity(hello: &Value) -> Value {
    json!({
        "protocol": hello["protocol"]["name"],
        "appVersion": hello["appVersion"],
    })
}

fn current_identity() -> Value {
    json!({ "protocol": "eukhe.daemon", "appVersion": env!("CARGO_PKG_VERSION") })
}

/// Cleanup for a supervisor the launcher spawned detached: force-shutdown
/// over the wire, SIGKILL when it does not stop.
struct DetachedDaemon {
    socket: PathBuf,
}

impl Drop for DetachedDaemon {
    fn drop(&mut self) {
        let Ok(mut stream) = UnixStream::connect(&self.socket) else {
            return;
        };
        if stream
            .set_read_timeout(Some(Duration::from_secs(2)))
            .is_err()
        {
            return;
        }
        let mut hello = String::new();
        let Ok(reader) = stream.try_clone() else {
            return;
        };
        if BufReader::new(reader).read_line(&mut hello).is_err() {
            return;
        }
        let pid = serde_json::from_str::<Value>(&hello)
            .ok()
            .and_then(|hello| hello["supervisorPid"].as_i64());
        let command = json!({
            "type": "command", "id": "test-cleanup",
            "protocol": { "name": "eukhe.daemon", "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION },
            "command": { "type": "shutdown", "force": true }
        });
        let _ = writeln!(stream, "{command}");
        let deadline = Instant::now() + Duration::from_secs(10);
        while UnixStream::connect(&self.socket).is_ok() {
            if Instant::now() > deadline {
                if let Some(pid) = pid.and_then(|pid| i32::try_from(pid).ok()) {
                    // SAFETY: the pid comes from this fixture supervisor's
                    // own hello; it owns its session, so the group kill
                    // takes its workers with it.
                    unsafe {
                        libc::kill(-pid, libc::SIGKILL);
                        libc::kill(pid, libc::SIGKILL);
                    }
                }
                return;
            }
            std::thread::sleep(Duration::from_millis(50));
        }
    }
}

/// An in-process supervisor of an older eukhe version: same protocol and
/// schema, `appVersion` [`OLD_VERSION`]; `list` reports one session, busy
/// or idle; `shutdown` is counted, answered, and stops the listener.
async fn serve_old_daemon(
    listener: tokio::net::UnixListener,
    socket: PathBuf,
    busy: bool,
    shutdowns: Arc<AtomicUsize>,
) {
    let (stop_tx, mut stop_rx) = tokio::sync::watch::channel(false);
    loop {
        tokio::select! {
            accepted = listener.accept() => {
                let Ok((stream, _)) = accepted else { break };
                let stop_tx = stop_tx.clone();
                let shutdowns = Arc::clone(&shutdowns);
                tokio::spawn(async move {
                    let (reader, mut writer) = stream.into_split();
                    let hello = json!({
                        "type": "daemon_hello",
                        "protocol": { "name": "eukhe.daemon", "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION },
                        "schemaId": eukhe_types::daemon::DAEMON_SCHEMA_ID,
                        "appVersion": OLD_VERSION,
                    });
                    if writer.write_all(format!("{hello}\n").as_bytes()).await.is_err() {
                        return;
                    }
                    let mut lines = tokio::io::BufReader::new(reader).lines();
                    while let Ok(Some(line)) = lines.next_line().await {
                        let Ok(envelope) = serde_json::from_str::<Value>(&line) else { continue };
                        let command = envelope["command"]["type"].as_str().unwrap_or_default().to_string();
                        let data = match command.as_str() {
                            "list" => json!({ "sessions": [{
                                "activeSessionId": "old-1",
                                "sessionId": "old-1",
                                "activity": if busy { "working" } else { "idle" },
                                "isSessionActive": busy,
                                "isStreaming": busy,
                                "isCompacting": false,
                                "attachedClients": 0,
                            }] }),
                            _ => json!({}),
                        };
                        let response = json!({
                            "type": "response", "id": envelope["id"], "command": command,
                            "success": true, "data": data,
                        });
                        let _ = writer.write_all(format!("{response}\n").as_bytes()).await;
                        if command == "shutdown" {
                            shutdowns.fetch_add(1, Ordering::SeqCst);
                            let _ = stop_tx.send(true);
                            return;
                        }
                    }
                });
            }
            _ = stop_rx.changed() => break,
        }
    }
    drop(listener);
    let _ = std::fs::remove_file(socket);
}

/// An idle daemon of an older eukhe version is shut down and replaced by
/// this build; the launcher reports a current daemon and no notice.
#[tokio::test(flavor = "multi_thread")]
async fn an_idle_older_version_daemon_is_replaced() {
    let fixture = tempfile::tempdir().expect("fixture");
    let root = fixture.path().to_path_buf();
    let socket = root.join("d.sock");
    let _replacement = DetachedDaemon {
        socket: socket.clone(),
    };
    let shutdowns = Arc::new(AtomicUsize::new(0));
    let listener = tokio::net::UnixListener::bind(&socket).expect("bind old daemon");
    let old = tokio::spawn(serve_old_daemon(
        listener,
        socket.clone(),
        false,
        Arc::clone(&shutdowns),
    ));

    let output = {
        let (root, socket) = (root.clone(), socket.clone());
        tokio::task::spawn_blocking(move || run_launcher(&root, &socket))
            .await
            .expect("launcher join")
    };

    assert_eq!(
        launcher_report(&output),
        vec!["ready: Current".to_string(), "notice: None".to_string()]
    );
    assert_eq!(shutdowns.load(Ordering::SeqCst), 1, "old daemon shut down");
    old.await.expect("old daemon task");
    let hello = tokio::task::spawn_blocking(move || read_hello(&socket))
        .await
        .expect("hello join");
    assert_eq!(identity(&hello), current_identity());
}

/// A busy daemon of an older eukhe version keeps running: the launcher
/// uses it and reports the one-line notice naming its version.
#[tokio::test(flavor = "multi_thread")]
async fn a_busy_older_version_daemon_is_kept_with_a_notice() {
    let fixture = tempfile::tempdir().expect("fixture");
    let root = fixture.path().to_path_buf();
    let socket = root.join("d.sock");
    let shutdowns = Arc::new(AtomicUsize::new(0));
    let listener = tokio::net::UnixListener::bind(&socket).expect("bind old daemon");
    let old = tokio::spawn(serve_old_daemon(
        listener,
        socket.clone(),
        true,
        Arc::clone(&shutdowns),
    ));

    let output = {
        let (root, socket) = (root.clone(), socket.clone());
        tokio::task::spawn_blocking(move || run_launcher(&root, &socket))
            .await
            .expect("launcher join")
    };

    assert_eq!(
        launcher_report(&output),
        vec![
            format!("ready: Outdated {{ version: \"{OLD_VERSION}\" }}"),
            format!(
                "notice: Some(\"The background service runs eukhe {OLD_VERSION}; it restarts on the next idle start (or run: eukhe shutdown).\")"
            ),
        ]
    );
    assert_eq!(shutdowns.load(Ordering::SeqCst), 0, "busy daemon untouched");
    let hello = tokio::task::spawn_blocking(move || read_hello(&socket))
        .await
        .expect("hello join");
    assert_eq!(
        hello["appVersion"], OLD_VERSION,
        "the old daemon still serves"
    );
    old.abort();
}

/// A pre-rename daemon answering another protocol name holds the socket:
/// the launcher finds it through the socket, stops it (SIGTERM), and starts
/// this build — no startup timeout.
#[test]
fn a_foreign_protocol_daemon_is_stopped_and_replaced() {
    let fixture = tempfile::tempdir().expect("fixture");
    let root = fixture.path();
    let socket = root.join("d.sock");
    let _replacement = DetachedDaemon {
        socket: socket.clone(),
    };
    let mut foreign = ForeignDaemon(spawn_foreign_daemon(root, &socket));

    let started = Instant::now();
    let output = run_launcher(root, &socket);

    assert_eq!(
        launcher_report(&output),
        vec!["ready: Current".to_string(), "notice: None".to_string()]
    );
    assert!(
        started.elapsed() < Duration::from_secs(25),
        "the replacement must not ride the startup timeout"
    );
    let status = wait_exit(&mut foreign.0).expect("the foreign daemon exited");
    assert_eq!(status.signal(), Some(libc::SIGTERM));
    assert_eq!(identity(&read_hello(&socket)), current_identity());
}

/// Run a discovery command against the renamed daemon's socket (the way
/// the user's own default socket is targeted); its JSON report.
fn run_discovery(root: &Path, socket: &Path, args: &[&str]) -> (Value, Option<i32>) {
    let mut command = Command::new(cli_binary());
    command.args(args).stdin(Stdio::null());
    pin_state_env(&mut command, root);
    command.env("EUKHE_DAEMON_SOCKET", socket);
    let output = command.output().expect("run discovery command");
    let report = serde_json::from_slice(&output.stdout).unwrap_or_else(|_| {
        panic!(
            "{args:?} json: {}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    (report, output.status.code())
}

/// `status` and `shutdown --force` find a renamed daemon (its process name
/// is not `eukhe`, and its hello carries no pid) by the process holding its
/// socket: `status` names its pid and calls it stale (another protocol),
/// and `shutdown --force` stops it although it ignores the shutdown
/// request.
#[test]
fn shutdown_force_stops_a_renamed_daemon_found_by_its_socket() {
    let fixture = tempfile::tempdir().expect("fixture");
    let root = fixture.path();
    // Inside the root's agent dir: the invocation's state root owns it.
    let socket = root.join("agent").join("d.sock");
    std::fs::create_dir_all(root.join("agent")).expect("agent dir");
    let mut foreign = ForeignDaemon(spawn_foreign_daemon(root, &socket));
    let pid = foreign.0.id();

    let (status, code) = run_discovery(root, &socket, &["status", "--json"]);
    assert_eq!(
        (status, code),
        (
            json!([{
                "socketPath": socket.display().to_string(),
                "pid": pid,
                "version": "0.9.9-eukhe.1",
                "protocolVersion": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION,
                "schemaId": eukhe_types::daemon::DAEMON_SCHEMA_ID,
                "pidSource": "listener",
                "sessionCount": 0,
                "status": "stale",
                "isDefault": true,
            }]),
            Some(0)
        )
    );

    let (report, code) = run_discovery(root, &socket, &["shutdown", "--force", "--json"]);
    assert_eq!(
        (report, code),
        (
            json!({
                "stopped": [{
                    "socketPath": socket.display().to_string(),
                    "action": format!("force-killed unresponsive background service (pid {pid})"),
                }],
                "failed": [],
            }),
            Some(0)
        )
    );
    assert!(
        wait_exit(&mut foreign.0).is_some(),
        "the renamed daemon exited"
    );
}
