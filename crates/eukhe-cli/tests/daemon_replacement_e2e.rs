//! The launcher replaces a daemon it cannot use (an older eukhe version, a
//! pre-rename `prime-agent` build answering another protocol name) only on
//! an interactive start, never replaces a newer daemon or a daemon of a
//! background client's start, and `shutdown --force` stops a renamed
//! daemon found by its socket.
//!
//! Every launcher run is this test binary re-exec'd in a child mode with
//! the fixture's state environment pinned on its spawn (agent dir, TMPDIR,
//! no inherited daemon socket), so the supervisor it starts never touches
//! the ambient environment's real paths.
#![cfg(unix)]

use std::io::{BufRead as _, BufReader, Write as _};
use std::os::unix::fs::PermissionsExt as _;
use std::os::unix::net::UnixStream;
use std::os::unix::process::{CommandExt as _, ExitStatusExt as _};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use eukhe_tui::daemon_build::{Build, Caller};
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
/// Child mode: the launcher's caller, `interactive` or `background`.
const LAUNCHER_CALLER_ENV: &str = "EUKHE_TEST_REPLACEMENT_LAUNCHER_CALLER";
/// Child mode: the client build the launcher runs as, `<version> <build
/// id>`.
const LAUNCHER_BUILD_ENV: &str = "EUKHE_TEST_REPLACEMENT_LAUNCHER_BUILD";
/// Child mode: serve a pre-rename daemon's hello on this socket.
const FOREIGN_SOCKET_ENV: &str = "EUKHE_TEST_FOREIGN_DAEMON_SOCKET";
/// The line the foreign child prints once its socket listens.
const FOREIGN_READY: &str = "foreign daemon listening";
/// The version an outdated mock daemon reports.
const OLD_VERSION: &str = "0.0.1-old";
/// The older client build of the replacement ping-pong (an old `eukhe
/// dashboard`).
const PING_PONG_OLD: Build<'static> = Build {
    version: "0.9.9-main.46",
    id: "eukhe-daemon-rs-0.9.9-main.46",
};

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
/// daemon-backed mode takes first) in a child process, as `client` started
/// by `caller`.
fn run_launcher(root: &Path, socket: &Path, client: Build<'_>, caller: Caller) -> Output {
    let caller = match caller {
        Caller::Interactive => "interactive",
        Caller::Background => "background",
    };
    let mut command = Command::new(std::env::current_exe().expect("test binary"));
    command
        .args(["--exact", "launcher_child_mode", "--nocapture"])
        .current_dir(root)
        .env(LAUNCHER_SOCKET_ENV, socket)
        .env(LAUNCHER_CALLER_ENV, caller)
        .env(
            LAUNCHER_BUILD_ENV,
            format!("{} {}", client.version, client.id),
        )
        .stdin(Stdio::null());
    pin_state_env(&mut command, root);
    command.output().expect("spawn launcher child")
}

/// The launcher outcome lines the child printed (`ready: ...`,
/// `error: ...`), libtest's own output filtered out.
fn launcher_report(output: &Output) -> Vec<String> {
    assert!(
        output.status.success(),
        "launcher failed: {}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|line| line.starts_with("ready: ") || line.starts_with("error: "))
        .map(str::to_string)
        .collect()
}

/// The launcher report of a start that kept the daemon with `notice`.
fn kept(notice: &str) -> Vec<String> {
    vec![format!("ready: Kept {{ notice: {notice:?} }}")]
}

fn current() -> Vec<String> {
    vec!["ready: Current".to_string()]
}

/// A socket path in a private directory (the agent dir, mode 0700): a
/// supervisor binds its socket only there.
fn private_socket(root: &Path) -> PathBuf {
    let dir = root.join("agent");
    std::fs::create_dir_all(&dir).expect("agent dir");
    std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).expect("private dir");
    dir.join("d.sock")
}

/// Child mode for the launcher runs (a plain test run without the env var
/// passes trivially).
#[test]
fn launcher_child_mode() {
    let Some(socket) = std::env::var_os(LAUNCHER_SOCKET_ENV) else {
        return;
    };
    let socket = PathBuf::from(socket);
    let caller = match std::env::var(LAUNCHER_CALLER_ENV).as_deref() {
        Ok("interactive") => Caller::Interactive,
        Ok("background") => Caller::Background,
        other => panic!("unknown launcher caller {other:?}"),
    };
    let build = std::env::var(LAUNCHER_BUILD_ENV).expect("client build");
    let (version, id) = build.split_once(' ').expect("`<version> <build id>`");
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("runtime");
    let cwd = std::env::current_dir().expect("cwd");
    match runtime.block_on(eukhe_cli::ensure_daemon_running_with(
        &cli_binary(),
        Build { version, id },
        &socket,
        &cwd,
        caller,
    )) {
        Ok(ready) => println!("ready: {ready:?}"),
        Err(error) => println!("error: {error:#}"),
    }
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
    json!({ "protocol": "eukhe.daemon", "appVersion": eukhe_build_info::VERSION })
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
                    // The pid comes from this fixture supervisor's own
                    // hello; it owns its session, so the group kill takes
                    // its workers with it. Ignored as before: best-effort
                    // teardown.
                    let pid = nix::unistd::Pid::from_raw(pid);
                    let _ = nix::sys::signal::killpg(pid, nix::sys::signal::Signal::SIGKILL);
                    let _ = nix::sys::signal::kill(pid, nix::sys::signal::Signal::SIGKILL);
                }
                return;
            }
            std::thread::sleep(Duration::from_millis(50));
        }
    }
}

/// A mock supervisor: its build, its schema, and whether it has work.
struct MockDaemon {
    version: String,
    build_id: String,
    schema: &'static str,
    busy: bool,
}

impl MockDaemon {
    /// An idle mock of `version` and `build_id` with this build's schema.
    fn idle(version: &str, build_id: &str) -> Self {
        Self {
            version: version.to_string(),
            build_id: build_id.to_string(),
            schema: eukhe_types::daemon::DAEMON_SCHEMA_ID,
            busy: false,
        }
    }
}

/// An in-process supervisor stand-in of the eukhe protocol: the hello of
/// `mock` with the idle-shutdown capability. Each `shutdown` request is
/// counted; an idle mock agrees and stops its listener, a busy mock
/// refuses. Every other command gets an empty success.
async fn serve_mock_daemon(
    listener: tokio::net::UnixListener,
    socket: PathBuf,
    mock: MockDaemon,
    shutdowns: Arc<AtomicUsize>,
) {
    let hello = json!({
        "type": "daemon_hello",
        "protocol": { "name": "eukhe.daemon", "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION },
        "schemaId": mock.schema,
        "appVersion": mock.version,
        "runtime": { "buildId": mock.build_id },
        "serverCapabilities": [eukhe_types::daemon::IDLE_SHUTDOWN_CAPABILITY],
    });
    let (stop_tx, mut stop_rx) = tokio::sync::watch::channel(false);
    loop {
        tokio::select! {
            accepted = listener.accept() => {
                let Ok((stream, _)) = accepted else { break };
                let stop_tx = stop_tx.clone();
                let shutdowns = Arc::clone(&shutdowns);
                let hello = hello.clone();
                let busy = mock.busy;
                tokio::spawn(async move {
                    let (reader, mut writer) = stream.into_split();
                    if writer.write_all(format!("{hello}\n").as_bytes()).await.is_err() {
                        return;
                    }
                    let mut lines = tokio::io::BufReader::new(reader).lines();
                    while let Ok(Some(line)) = lines.next_line().await {
                        let Ok(envelope) = serde_json::from_str::<Value>(&line) else { continue };
                        let command = envelope["command"]["type"].as_str().unwrap_or_default().to_string();
                        let stops = command == "shutdown" && !busy;
                        let response = json!({
                            "type": "response", "id": envelope["id"], "command": command,
                            "success": command != "shutdown" || stops, "data": {},
                        });
                        if command == "shutdown" {
                            shutdowns.fetch_add(1, Ordering::SeqCst);
                        }
                        let _ = writer.write_all(format!("{response}\n").as_bytes()).await;
                        if stops {
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

/// Serve `mock` on `socket`: its task and its count of shutdown requests.
fn start_mock(socket: &Path, mock: MockDaemon) -> (tokio::task::JoinHandle<()>, Arc<AtomicUsize>) {
    let shutdowns = Arc::new(AtomicUsize::new(0));
    let listener = tokio::net::UnixListener::bind(socket).expect("bind mock daemon");
    let task = tokio::spawn(serve_mock_daemon(
        listener,
        socket.to_path_buf(),
        mock,
        Arc::clone(&shutdowns),
    ));
    (task, shutdowns)
}

/// [`run_launcher`] off the runtime that serves the mocks; its report.
async fn launch(root: &Path, socket: &Path, client: Build<'static>, caller: Caller) -> Vec<String> {
    let (root, socket) = (root.to_path_buf(), socket.to_path_buf());
    tokio::task::spawn_blocking(move || {
        launcher_report(&run_launcher(&root, &socket, client, caller))
    })
    .await
    .expect("launcher join")
}

/// The hello of whatever listens on `socket`, off the runtime.
async fn hello_now(socket: &Path) -> Value {
    let socket = socket.to_path_buf();
    tokio::task::spawn_blocking(move || read_hello(&socket))
        .await
        .expect("hello join")
}

/// What a client says when it keeps an older daemon.
fn older_daemon_notice(daemon_version: &str) -> String {
    format!("The background service runs eukhe {daemon_version}; it restarts on the next idle interactive start (or run: eukhe shutdown).")
}

/// What an older client says about a newer daemon.
fn older_client_notice(client_version: &str, daemon_version: &str) -> String {
    format!("this eukhe (v{client_version}) is older than the running daemon (v{daemon_version}): update or run `eukhe shutdown`")
}

/// An idle daemon of an older eukhe version is shut down and replaced by
/// this build on an interactive start; the launcher reports a current
/// daemon.
#[tokio::test(flavor = "multi_thread")]
async fn an_idle_older_version_daemon_is_replaced() {
    let fixture = tempfile::tempdir().expect("fixture");
    let (root, socket) = (fixture.path(), private_socket(fixture.path()));
    let _replacement = DetachedDaemon {
        socket: socket.clone(),
    };
    let (old, shutdowns) = start_mock(
        &socket,
        MockDaemon::idle(OLD_VERSION, "eukhe-daemon-rs-0.0.1-old"),
    );

    assert_eq!(
        launch(root, &socket, Build::THIS, Caller::Interactive).await,
        current()
    );
    assert_eq!(shutdowns.load(Ordering::SeqCst), 1, "old daemon shut down");
    old.await.expect("old daemon task");
    assert_eq!(identity(&hello_now(&socket).await), current_identity());
}

/// A busy daemon of an older eukhe version refuses the idle shutdown and
/// keeps running: the launcher uses it and reports the notice naming its
/// version.
#[tokio::test(flavor = "multi_thread")]
async fn a_busy_older_version_daemon_is_kept_with_a_notice() {
    let fixture = tempfile::tempdir().expect("fixture");
    let (root, socket) = (fixture.path(), fixture.path().join("d.sock"));
    let mock = MockDaemon {
        busy: true,
        ..MockDaemon::idle(OLD_VERSION, "eukhe-daemon-rs-0.0.1-old")
    };
    let (old, shutdowns) = start_mock(&socket, mock);

    assert_eq!(
        launch(root, &socket, Build::THIS, Caller::Interactive).await,
        kept(&older_daemon_notice(OLD_VERSION))
    );
    assert_eq!(shutdowns.load(Ordering::SeqCst), 1, "asked once, refused");
    assert_eq!(
        hello_now(&socket).await["appVersion"],
        OLD_VERSION,
        "the old daemon still serves"
    );
    old.abort();
}

// Regression (the replacement ping-pong): an old `eukhe dashboard`
// (0.9.9-main.46) replaced the daemon of a new TUI, whose relaunch of the
// lost daemon replaced it back, forever. A background start (the
// dashboard, the gateway, ACP, the TUI's relaunch) keeps an idle older
// daemon; only an interactive start replaces it, once. After that, the old
// build's starts keep the newer daemon and say why.
#[tokio::test(flavor = "multi_thread")]
async fn an_older_daemon_is_replaced_once_and_only_by_an_interactive_start() {
    let fixture = tempfile::tempdir().expect("fixture");
    let root = fixture.path();
    let socket = private_socket(root);
    let _replacement = DetachedDaemon {
        socket: socket.clone(),
    };
    let (old, shutdowns) = start_mock(
        &socket,
        MockDaemon::idle(PING_PONG_OLD.version, PING_PONG_OLD.id),
    );

    for _ in 0..2 {
        assert_eq!(
            launch(root, &socket, Build::THIS, Caller::Background).await,
            kept(&older_daemon_notice(PING_PONG_OLD.version))
        );
    }
    assert_eq!(
        shutdowns.load(Ordering::SeqCst),
        0,
        "no background replacement"
    );

    assert_eq!(
        launch(root, &socket, Build::THIS, Caller::Interactive).await,
        current()
    );
    assert_eq!(shutdowns.load(Ordering::SeqCst), 1, "one replacement");
    old.await.expect("old daemon task");
    let supervisor_pid = hello_now(&socket).await["supervisorPid"].clone();

    let older_client = kept(&older_client_notice(
        PING_PONG_OLD.version,
        eukhe_build_info::VERSION,
    ));
    for caller in [Caller::Background, Caller::Interactive] {
        assert_eq!(
            launch(root, &socket, PING_PONG_OLD, caller).await,
            older_client
        );
    }
    assert_eq!(
        hello_now(&socket).await["supervisorPid"],
        supervisor_pid,
        "the old build's starts keep the newer daemon"
    );
}

/// The exact pair of the ping-pong: a 0.9.9-main.46 client finds an idle
/// 0.10.40 daemon. Neither its interactive start nor its background start
/// replaces it; both use it and say that this eukhe is older.
#[tokio::test(flavor = "multi_thread")]
async fn an_older_client_keeps_a_newer_daemon_with_its_message() {
    let fixture = tempfile::tempdir().expect("fixture");
    let (root, socket) = (fixture.path(), fixture.path().join("d.sock"));
    let (newer, shutdowns) = start_mock(
        &socket,
        MockDaemon::idle("0.10.40", "eukhe-daemon-rs-0.10.40+0123456789ab"),
    );

    for caller in [Caller::Interactive, Caller::Background] {
        assert_eq!(
            launch(root, &socket, PING_PONG_OLD, caller).await,
            kept(&older_client_notice(PING_PONG_OLD.version, "0.10.40"))
        );
    }
    assert_eq!(
        shutdowns.load(Ordering::SeqCst),
        0,
        "the newer daemon untouched"
    );
    assert_eq!(hello_now(&socket).await["appVersion"], "0.10.40");
    newer.abort();
}

/// An older client that cannot speak the newer daemon's protocol exits
/// with its message and leaves the daemon running.
#[tokio::test(flavor = "multi_thread")]
async fn an_older_client_exits_with_its_message_on_an_incompatible_newer_daemon() {
    let fixture = tempfile::tempdir().expect("fixture");
    let (root, socket) = (fixture.path(), fixture.path().join("d.sock"));
    let mock = MockDaemon {
        schema: "eukhe.daemon.future",
        ..MockDaemon::idle("0.10.40", "eukhe-daemon-rs-0.10.40+0123456789ab")
    };
    let (newer, shutdowns) = start_mock(&socket, mock);

    assert_eq!(
        launch(root, &socket, PING_PONG_OLD, Caller::Interactive).await,
        vec![format!(
            "error: {}",
            older_client_notice(PING_PONG_OLD.version, "0.10.40")
        )]
    );
    assert_eq!(
        shutdowns.load(Ordering::SeqCst),
        0,
        "the newer daemon untouched"
    );
    newer.abort();
}

/// A daemon of this version but another build is not replaced, even by an
/// idle interactive start; the launcher names the build that runs.
#[tokio::test(flavor = "multi_thread")]
async fn another_build_of_this_version_is_kept_with_a_notice() {
    let fixture = tempfile::tempdir().expect("fixture");
    let (root, socket) = (fixture.path(), fixture.path().join("d.sock"));
    let version = eukhe_build_info::VERSION;
    let (other, shutdowns) = start_mock(
        &socket,
        MockDaemon::idle(version, &format!("eukhe-daemon-rs-{version}+0123456789ab")),
    );

    assert_eq!(
        launch(root, &socket, Build::THIS, Caller::Interactive).await,
        kept(&format!(
            "The background service runs another build of eukhe {version} ({version}+0123456789ab); it does not restart automatically (run: eukhe shutdown)."
        ))
    );
    assert_eq!(
        shutdowns.load(Ordering::SeqCst),
        0,
        "no automatic replacement"
    );
    other.abort();
}

/// A pre-rename daemon answering another protocol name holds the socket:
/// an interactive start finds it through the socket, stops it (SIGTERM),
/// and starts this build — no startup timeout.
#[test]
fn a_foreign_protocol_daemon_is_stopped_and_replaced() {
    let fixture = tempfile::tempdir().expect("fixture");
    let root = fixture.path();
    let socket = private_socket(root);
    let _replacement = DetachedDaemon {
        socket: socket.clone(),
    };
    let mut foreign = ForeignDaemon(spawn_foreign_daemon(root, &socket));

    let started = Instant::now();
    let output = run_launcher(root, &socket, Build::THIS, Caller::Interactive);

    assert_eq!(launcher_report(&output), current());
    assert!(
        started.elapsed() < Duration::from_secs(25),
        "the replacement must not ride the startup timeout"
    );
    let status = wait_exit(&mut foreign.0).expect("the foreign daemon exited");
    assert_eq!(status.signal(), Some(libc::SIGTERM));
    assert_eq!(identity(&read_hello(&socket)), current_identity());
}

/// A supervisor of this very build is current everywhere: `status --json`
/// reports it `current` with this build's identity, and a second client
/// start uses it instead of replacing it (the same supervisor pid keeps
/// the socket). A daemon judged stale here would be shut down and
/// respawned on every client start.
#[test]
fn a_daemon_of_this_build_is_current_and_kept_by_the_next_client_start() {
    let fixture = tempfile::tempdir().expect("fixture");
    let root = fixture.path();
    // Inside the root's agent dir: the invocation's state root owns it.
    let socket = root.join("agent").join("d.sock");
    let _daemon = DetachedDaemon {
        socket: socket.clone(),
    };

    assert_eq!(
        launcher_report(&run_launcher(
            root,
            &socket,
            Build::THIS,
            Caller::Interactive
        )),
        current()
    );
    let hello = read_hello(&socket);
    let supervisor_pid = hello["supervisorPid"].as_u64().expect("supervisor pid");
    assert_eq!(
        hello["runtime"]["buildId"],
        json!(eukhe_build_info::DAEMON_BUILD_ID)
    );

    let (status, code) = run_discovery(root, &socket, &["status", "--json"]);
    assert_eq!(code, Some(0));
    let row = &status[0];
    assert_eq!(
        json!({
            "socketPath": row["socketPath"],
            "pid": row["pid"],
            "version": row["version"],
            "protocolVersion": row["protocolVersion"],
            "schemaId": row["schemaId"],
            "buildId": row["buildId"],
            "status": row["status"],
        }),
        json!({
            "socketPath": socket.display().to_string(),
            "pid": supervisor_pid,
            "version": eukhe_build_info::VERSION,
            "protocolVersion": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION,
            "schemaId": eukhe_types::daemon::DAEMON_SCHEMA_ID,
            "buildId": eukhe_build_info::DAEMON_BUILD_ID,
            "status": "current",
        }),
        "status report: {status}"
    );

    assert_eq!(
        launcher_report(&run_launcher(
            root,
            &socket,
            Build::THIS,
            Caller::Interactive
        )),
        current()
    );
    assert_eq!(
        read_hello(&socket)["supervisorPid"].as_u64(),
        Some(supervisor_pid),
        "the next client start must keep the current daemon"
    );
}

// Regression (the replacement ping-pong), on a real supervisor: two client
// builds share one socket. The new build's daemon runs; the old build's
// background reconnects and interactive starts keep it and say that the
// old client is older; the new build's starts keep it. Round after round,
// the same supervisor serves: no client replaces another's daemon.
#[test]
fn two_client_builds_do_not_replace_each_other() {
    let fixture = tempfile::tempdir().expect("fixture");
    let root = fixture.path();
    let socket = private_socket(root);
    let _daemon = DetachedDaemon {
        socket: socket.clone(),
    };
    let report = |client: Build<'_>, caller: Caller| {
        launcher_report(&run_launcher(root, &socket, client, caller))
    };

    assert_eq!(report(Build::THIS, Caller::Interactive), current());
    let supervisor_pid = read_hello(&socket)["supervisorPid"].clone();
    let older_client = kept(&older_client_notice(
        PING_PONG_OLD.version,
        eukhe_build_info::VERSION,
    ));
    for _ in 0..3 {
        assert_eq!(report(PING_PONG_OLD, Caller::Background), older_client);
        assert_eq!(report(Build::THIS, Caller::Background), current());
        assert_eq!(report(PING_PONG_OLD, Caller::Interactive), older_client);
        assert_eq!(report(Build::THIS, Caller::Interactive), current());
    }
    assert_eq!(
        read_hello(&socket)["supervisorPid"],
        supervisor_pid,
        "one supervisor serves every round"
    );
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
