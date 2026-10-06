// Harness fns are linear scripts; pid and length narrowing sits at OS
// boundaries where the values are bounded.
#![allow(
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap
)]

//! Real-terminal e2e for the remote (SSH) Anthropic login: the real
//! supervisor, the re-executed test binary as the interactive client (the
//! same `main_with_runtime` entry point the shipped binary calls) on a pty,
//! and a local fake token endpoint (`EUKHE_ANTHROPIC_TOKEN_URL`). The
//! harness reads the sign-in URL the panel shows -- whole, from the byte
//! stream -- and plays the browser on another machine: it pastes the
//! address of the failed localhost page (bracketed or typed, short or
//! long, inline or fullscreen), pastes a wrong one first, or lands the
//! browser callback itself. Every path must end logged in with one token
//! exchange carrying the login's code, state, and redirect.

use std::collections::VecDeque;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::os::fd::{AsRawFd, OwnedFd};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::{Duration, Instant};

use nix::fcntl::{fcntl, FcntlArg::F_SETFL, OFlag};
use nix::pty::{openpty, Winsize};
use serde_json::{json, Value};

/// The parent hands the child its launch through this env var; unset, the
/// child test passes trivially (a plain `cargo test` runs only parents).
const CHILD_ENV: &str = "EUKHE_ANTHROPIC_REMOTE_LOGIN_CHILD";
/// The registered redirect the flow's callback server listens on.
const CALLBACK_PORT: u16 = 53692;
const AUTHORIZE_PREFIX: &str = "https://claude.ai/oauth/authorize?";
/// The logged-in status row's tail (its head wraps on a narrow screen).
const LOGGED_IN: &str = "Credentials saved to";

/// Every parent test logs in through the one registered callback port:
/// they run one at a time.
fn port_lock() -> std::sync::MutexGuard<'static, ()> {
    static LOCK: Mutex<()> = Mutex::new(());
    LOCK.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The interactive client half: the shipped entry point on the parent's
/// pty, attached to the parent's supervisor.
#[test]
fn anthropic_remote_login_child_mode() {
    let Ok(config) = std::env::var(CHILD_ENV) else {
        return;
    };
    let config: Value = serde_json::from_str(&config).expect("child config");
    std::env::set_current_dir(config["cwd"].as_str().expect("cwd")).expect("child cwd");
    let args = vec![
        "--daemon-socket".to_string(),
        config["socket"].as_str().expect("socket").to_string(),
    ];
    let _ = eukhe_cli::main_with_runtime(&args, &eukhe_cli::PrintRuntime);
}

/// The fake token endpoint: records every request body and answers the
/// scripted statuses in order (200 once the script runs out).
struct TokenServer {
    url: String,
    bodies: Arc<Mutex<Vec<Value>>>,
}

impl TokenServer {
    fn start(statuses: Vec<u16>) -> TokenServer {
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind token server");
        let url = format!(
            "http://127.0.0.1:{}/v1/oauth/token",
            listener.local_addr().expect("addr").port()
        );
        let bodies = Arc::new(Mutex::new(Vec::new()));
        let recorded = Arc::clone(&bodies);
        let mut statuses: VecDeque<u16> = statuses.into();
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(stream) = stream else { return };
                let Some(body) = read_request_body(&stream) else {
                    continue;
                };
                recorded
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner)
                    .push(serde_json::from_str(&body).unwrap_or(Value::String(body)));
                let status = statuses.pop_front().unwrap_or(200);
                let reply = if status == 200 {
                    r#"{"access_token":"e2e-access","refresh_token":"e2e-refresh","expires_in":3600}"#
                } else {
                    r#"{"error":"invalid_grant","error_description":"Invalid authorization code"}"#
                };
                let mut stream = stream;
                let _ = write!(
                    stream,
                    "HTTP/1.1 {status} X\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n\r\n{reply}",
                    reply.len()
                );
            }
        });
        TokenServer { url, bodies }
    }

    fn bodies(&self) -> Vec<Value> {
        self.bodies
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

/// One HTTP request's body (by `content-length`).
fn read_request_body(stream: &TcpStream) -> Option<String> {
    let mut reader = BufReader::new(stream);
    let mut length = 0usize;
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line).ok()? == 0 {
            return None;
        }
        let line = line.trim_end();
        if line.is_empty() {
            break;
        }
        if let Some((name, value)) = line.split_once(':') {
            if name.eq_ignore_ascii_case("content-length") {
                length = value.trim().parse().ok()?;
            }
        }
    }
    let mut body = vec![0u8; length];
    reader.read_exact(&mut body).ok()?;
    String::from_utf8(body).ok()
}

struct Supervisor {
    child: Child,
    socket: PathBuf,
}

impl Drop for Supervisor {
    fn drop(&mut self) {
        let supervisor_pid = graceful_shutdown(&self.socket);
        let workers = supervisor_pid.map(child_pids_of).unwrap_or_default();
        let _ = self.child.kill();
        let _ = self.child.wait();
        for pid in workers {
            // SAFETY: a plain signal to a worker pid this test spawned.
            unsafe {
                libc::kill(pid as i32, libc::SIGKILL);
            }
        }
    }
}

fn child_pids_of(ppid: u32) -> Vec<u32> {
    let Ok(entries) = std::fs::read_dir("/proc") else {
        return Vec::new();
    };
    entries
        .flatten()
        .filter_map(|entry| {
            let child = entry.file_name().to_string_lossy().parse::<u32>().ok()?;
            let stat = std::fs::read_to_string(format!("/proc/{child}/stat")).ok()?;
            let (_, rest) = stat.rsplit_once(')')?;
            let parent = rest.split_whitespace().nth(1)?.parse::<u32>().ok()?;
            (parent == ppid).then_some(child)
        })
        .collect()
}

/// The protocol shutdown; returns the supervisor pid its hello names.
fn graceful_shutdown(socket: &Path) -> Option<u32> {
    let stream = std::os::unix::net::UnixStream::connect(socket).ok()?;
    let mut writer = stream.try_clone().ok()?;
    let mut reader = BufReader::new(stream);
    let mut hello = String::new();
    reader.read_line(&mut hello).ok()?;
    let hello: Value = serde_json::from_str(hello.trim()).ok()?;
    let pid = hello["supervisorPid"].as_u64()? as u32;
    let shutdown = json!({
        "type": "command",
        "id": "remote-login-e2e-shutdown",
        "protocol": { "name": "eukhe.daemon", "version": 7 },
        "command": { "type": "shutdown" },
    });
    let _ = writeln!(writer, "{shutdown}");
    let _ = writer.flush();
    let deadline = Instant::now() + Duration::from_secs(10);
    while Path::new(&format!("/proc/{pid}")).exists() && Instant::now() < deadline {
        std::thread::sleep(Duration::from_millis(20));
    }
    Some(pid)
}

/// The test's isolated world: home, agent dir, supervisor, token server.
/// Fields drop in order: the supervisor stops before its dir goes.
struct World {
    _supervisor: Supervisor,
    tokens: TokenServer,
    agent_dir: PathBuf,
    socket: PathBuf,
    dir: tempfile::TempDir,
}

impl World {
    fn new(screen: Screen, statuses: Vec<u16>) -> World {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(agent_dir.join("sessions")).expect("agent dir");
        std::fs::create_dir_all(dir.path().join("project")).expect("project dir");
        std::fs::create_dir_all(dir.path().join("tmp")).expect("tmp dir");
        let fullscreen = match screen {
            Screen::Inline => false,
            Screen::Fullscreen => true,
        };
        std::fs::write(
            agent_dir.join("settings.json"),
            json!({
                "onboardingShown": true,
                "onboardingCompleted": true,
                "terminal": { "fullscreen": fullscreen },
            })
            .to_string(),
        )
        .expect("settings");
        std::fs::write(
            dir.path().join("script.json"),
            json!({ "responses": ["unused"] }).to_string(),
        )
        .expect("faux script");
        let socket = dir.path().join("daemon.sock");
        let mut command = Command::new(env!("CARGO_BIN_EXE_eukhe"));
        command
            .args(["--mode", "daemon", "--daemon-socket"])
            .arg(&socket)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        isolate(&mut command, dir.path(), &agent_dir);
        let child = command.spawn().expect("spawn the supervisor");
        let deadline = Instant::now() + Duration::from_secs(15);
        while !socket.exists() {
            assert!(
                Instant::now() < deadline,
                "the supervisor socket never appeared"
            );
            std::thread::sleep(Duration::from_millis(20));
        }
        World {
            agent_dir: agent_dir.clone(),
            socket: socket.clone(),
            _supervisor: Supervisor { child, socket },
            tokens: TokenServer::start(statuses),
            dir,
        }
    }

    /// The interactive client on a `cols` x 30 pty.
    fn client(&self, cols: u16) -> Client {
        let pty = openpty(
            Some(&Winsize {
                ws_row: 30,
                ws_col: cols,
                ws_xpixel: 0,
                ws_ypixel: 0,
            }),
            None,
        )
        .expect("open pty");
        let slave = pty.slave;
        let slave_fd = slave.as_raw_fd();
        let mut command = Command::new(std::env::current_exe().expect("test binary"));
        command
            .args([
                "--exact",
                "anthropic_remote_login_child_mode",
                "--nocapture",
            ])
            .env(
                CHILD_ENV,
                json!({
                    "socket": self.socket.display().to_string(),
                    "cwd": self.dir.path().join("project").display().to_string(),
                })
                .to_string(),
            )
            .env("EUKHE_ANTHROPIC_TOKEN_URL", &self.tokens.url)
            .env("TERM", "xterm-256color")
            .stdin(slave.try_clone().expect("clone pty slave"))
            .stdout(slave.try_clone().expect("clone pty slave"))
            .stderr(slave.try_clone().expect("clone pty slave"));
        isolate(&mut command, self.dir.path(), &self.agent_dir);
        // SAFETY: post-fork pre-exec in the child only; no allocation.
        unsafe {
            command.pre_exec(move || {
                nix::unistd::setsid()?;
                if libc::ioctl(slave_fd, libc::TIOCSCTTY as libc::c_ulong, 0) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        let child = command.spawn().expect("spawn the interactive client");
        drop(command);
        drop(slave);
        Client {
            child,
            pty: PtyReader::new(pty.master),
        }
    }

    /// The stored credential, once the login wrote it.
    fn stored_access(&self) -> Option<String> {
        let auth: Value =
            serde_json::from_str(&std::fs::read_to_string(self.agent_dir.join("auth.json")).ok()?)
                .ok()?;
        auth["anthropic"]["access"].as_str().map(str::to_string)
    }
}

/// Pin every state path of a spawned process inside the test's dir.
fn isolate(command: &mut Command, root: &Path, agent_dir: &Path) {
    command
        .env("HOME", root)
        .env("TMPDIR", root.join("tmp"))
        .env("EUKHE_CODING_AGENT_DIR", agent_dir)
        .env("EUKHE_SESSION_DIR", agent_dir.join("sessions"))
        .env("EUKHE_OFFLINE", "1")
        .env("EUKHE_TELEMETRY", "0")
        .env("EUKHE_FAUX_SCRIPT", root.join("script.json"))
        .env("BROWSER", "/bin/true")
        .env_remove("TMUX")
        .env_remove("RLM_DEPTH")
        .env_remove("SSH_CONNECTION")
        .env_remove("SSH_CLIENT");
    for var in [
        eukhe_daemon::worker::WORKER_ROLE_ENV,
        eukhe_daemon::worker::WORKER_TOKEN_ENV,
        eukhe_daemon::worker::WORKER_ACTIVE_SESSION_ID_ENV,
        eukhe_daemon::worker::WORKER_RECOVERY_JOURNAL_ENV,
        eukhe_daemon::worker::WORKER_SUPERVISOR_SOCKET_ENV,
        eukhe_daemon::worker::WORKER_SOCKET_ENV,
        eukhe_daemon::worker::WORKER_INSTANCE_ID_ENV,
        eukhe_daemon::worker::WORKER_SCRIPT_ENV,
        eukhe_daemon::lease::SESSION_LEASE_OWNER_ID_ENV,
    ] {
        command.env_remove(var);
    }
}

#[derive(Clone, Copy)]
enum Screen {
    Inline,
    Fullscreen,
}

/// How the harness's "user" puts text into the field.
#[derive(Clone, Copy)]
enum Paste {
    /// A bracketed paste (what a modern terminal sends).
    Bracketed,
    /// Plain keystrokes (a terminal or multiplexer without bracketed
    /// paste).
    Typed,
}

struct Client {
    child: Child,
    pty: PtyReader,
}

impl Client {
    /// `/login`, then the Anthropic subscription row; returns the sign-in
    /// URL read whole from the byte stream.
    fn open_anthropic_login(&mut self) -> url::Url {
        self.pty.wait_for("[D] ", "the chat footer");
        self.pty.write(b"/login");
        self.pty.wait_for("/login", "the typed command");
        self.pty.write(b"\r");
        self.pty
            .wait_for("Anthropic (Claude Pro", "the provider rows");
        self.pty.write(b"\x1b[B");
        std::thread::sleep(Duration::from_millis(200));
        self.pty.write(b"\r");
        self.pty.wait_for("Paste value", "the paste field");
        let text = strip_escapes(&self.pty.output);
        let start = text.rfind(AUTHORIZE_PREFIX).expect("the sign-in URL shows");
        let url: String = text[start..]
            .chars()
            .take_while(char::is_ascii_graphic)
            .collect();
        url::Url::parse(&url).expect("the shown URL parses")
    }

    fn paste(&mut self, text: &str, paste: Paste) {
        match paste {
            Paste::Bracketed => {
                self.pty
                    .write(format!("\x1b[200~{text}\x1b[201~").as_bytes());
            }
            // Keystrokes arrive in terminal-sized writes.
            Paste::Typed => {
                for chunk in text.as_bytes().chunks(256) {
                    self.pty.write(chunk);
                    std::thread::sleep(Duration::from_millis(20));
                    self.pty.drain();
                }
            }
        }
        std::thread::sleep(Duration::from_millis(300));
        self.pty.write(b"\r");
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// Non-blocking reader over the pty master.
struct PtyReader {
    file: std::fs::File,
    output: Vec<u8>,
}

impl PtyReader {
    fn new(master: OwnedFd) -> PtyReader {
        fcntl(master.as_raw_fd(), F_SETFL(OFlag::O_NONBLOCK)).expect("pty master non-blocking");
        PtyReader {
            file: master.into(),
            output: Vec::new(),
        }
    }

    fn drain(&mut self) {
        let mut buffer = vec![0u8; 65536];
        while let Ok(n) = self.file.read(&mut buffer) {
            if n == 0 {
                break;
            }
            self.output.extend_from_slice(&buffer[..n]);
        }
    }

    /// Write all of `payload`, draining the child's output while the
    /// pty's input queue is full.
    fn write(&mut self, payload: &[u8]) {
        let deadline = Instant::now() + Duration::from_secs(30);
        let mut rest = payload;
        while !rest.is_empty() {
            match self.file.write(rest) {
                Ok(n) => rest = &rest[n..],
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                    assert!(Instant::now() < deadline, "the pty never took the input");
                    self.drain();
                    std::thread::sleep(Duration::from_millis(10));
                }
                Err(error) => panic!("write to the pty: {error}"),
            }
        }
    }

    /// Drain until `needle` shows in the escape-stripped stream.
    fn wait_for(&mut self, needle: &str, what: &str) {
        let deadline = Instant::now() + Duration::from_secs(45);
        loop {
            self.drain();
            let text = strip_escapes(&self.output);
            if text.contains(needle) {
                return;
            }
            assert!(
                Instant::now() < deadline,
                "timeout waiting for {what} ({needle:?}); stream tail:\n{}",
                &text[text.len().saturating_sub(3000)..]
            );
            std::thread::sleep(Duration::from_millis(20));
        }
    }
}

/// The stream without CSI and OSC sequences: a soft-wrapped URL's pieces
/// are adjacent once the styling between them drops.
fn strip_escapes(bytes: &[u8]) -> String {
    let text = String::from_utf8_lossy(bytes);
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\x1b' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('[') => {
                for c in chars.by_ref() {
                    if ('@'..='~').contains(&c) {
                        break;
                    }
                }
            }
            Some(']') => {
                while let Some(c) = chars.next() {
                    if c == '\x07' {
                        break;
                    }
                    if c == '\x1b' {
                        chars.next();
                        break;
                    }
                }
            }
            Some(_) | None => {}
        }
    }
    out
}

fn query(url: &url::Url, name: &str) -> String {
    url.query_pairs().find(|(key, _)| key == name).map_or_else(
        || panic!("the sign-in URL carries {name}"),
        |(_, value)| value.to_string(),
    )
}

/// The one exchange the login made: the pasted code, the login's state
/// (its PKCE verifier), and the registered redirect.
fn assert_exchange(world: &World, url: &url::Url, code: &str) {
    let state = query(url, "state");
    let bodies = world.tokens.bodies();
    assert_eq!(
        bodies.last(),
        Some(&json!({
            "grant_type": "authorization_code",
            "client_id": query(url, "client_id"),
            "code": code,
            "state": state,
            "redirect_uri": "http://localhost:53692/callback",
            "code_verifier": state,
        })),
        "{bodies:?}"
    );
    assert_eq!(world.stored_access().as_deref(), Some("e2e-access"));
}

/// The paste path, end to end, for one terminal shape.
fn paste_logs_in(screen: Screen, cols: u16, paste: Paste, code: &str) {
    let _port = port_lock();
    let world = World::new(screen, Vec::new());
    let mut client = world.client(cols);
    let url = client.open_anthropic_login();
    for name in [
        "code",
        "client_id",
        "response_type",
        "redirect_uri",
        "scope",
        "code_challenge",
        "code_challenge_method",
        "state",
    ] {
        query(&url, name);
    }
    // The address bar of the failed localhost page, copied with the
    // stray whitespace a terminal copy adds.
    let redirect = format!(
        "  http://localhost:53692/callback?code={code}&state={}  ",
        query(&url, "state")
    );
    client.paste(&redirect, paste);
    client.pty.wait_for(LOGGED_IN, "the logged-in status");
    assert_exchange(&world, &url, code);
}

#[test]
fn a_pasted_redirect_logs_in_inline() {
    if std::env::var(CHILD_ENV).is_ok() {
        return;
    }
    paste_logs_in(Screen::Inline, 100, Paste::Bracketed, "e2e-code");
}

#[test]
fn a_typed_long_redirect_logs_in_on_a_narrow_fullscreen() {
    if std::env::var(CHILD_ENV).is_ok() {
        return;
    }
    let long_code = "Ab9-_".repeat(500);
    paste_logs_in(Screen::Fullscreen, 40, Paste::Typed, &long_code);
}

#[test]
fn a_wrong_state_paste_then_the_right_one_logs_in() {
    if std::env::var(CHILD_ENV).is_ok() {
        return;
    }
    let _port = port_lock();
    let world = World::new(Screen::Inline, Vec::new());
    let mut client = world.client(100);
    let url = client.open_anthropic_login();
    client.paste(
        "http://localhost:53692/callback?code=stale&state=from-another-login",
        Paste::Bracketed,
    );
    client
        .pty
        .wait_for("different login attempt", "the state mismatch notice");
    assert!(
        world.tokens.bodies().is_empty(),
        "no exchange for a mismatch"
    );
    client.paste(
        &format!("fresh-code#{}", query(&url, "state")),
        Paste::Bracketed,
    );
    client.pty.wait_for(LOGGED_IN, "the logged-in status");
    assert_exchange(&world, &url, "fresh-code");
}

#[test]
fn a_failed_exchange_then_a_retried_paste_logs_in() {
    if std::env::var(CHILD_ENV).is_ok() {
        return;
    }
    let _port = port_lock();
    let world = World::new(Screen::Inline, vec![400]);
    let mut client = world.client(100);
    let url = client.open_anthropic_login();
    let redirect = format!(
        "http://127.0.0.1:53692/callback/?code=first-code&state={}#",
        query(&url, "state")
    );
    client.paste(&redirect, Paste::Bracketed);
    client
        .pty
        .wait_for("Invalid authorization code", "the exchange failure reason");
    client.paste(
        &format!(
            "http://localhost:53692/callback?code=second-code&state={}",
            query(&url, "state")
        ),
        Paste::Bracketed,
    );
    client.pty.wait_for(LOGGED_IN, "the logged-in status");
    assert_eq!(world.tokens.bodies().len(), 2);
    assert_exchange(&world, &url, "second-code");
}

#[test]
fn the_browser_callback_logs_in_when_it_arrives_first() {
    if std::env::var(CHILD_ENV).is_ok() {
        return;
    }
    let _port = port_lock();
    if TcpListener::bind(("127.0.0.1", CALLBACK_PORT)).is_err() {
        // Another process holds the registered port: the callback cannot
        // reach this login (the paste tests cover that case).
        eprintln!("skipped: port {CALLBACK_PORT} is busy");
        return;
    }
    let world = World::new(Screen::Inline, Vec::new());
    let mut client = world.client(100);
    let url = client.open_anthropic_login();
    let mut stream =
        TcpStream::connect(("127.0.0.1", CALLBACK_PORT)).expect("the callback server listens");
    write!(
        stream,
        "GET /callback?code=callback-code&state={} HTTP/1.1\r\nhost: localhost\r\nconnection: close\r\n\r\n",
        query(&url, "state")
    )
    .expect("the browser redirect");
    let mut response = String::new();
    let _ = stream.read_to_string(&mut response);
    assert!(response.starts_with("HTTP/1.1 200"), "{response}");
    client.pty.wait_for(LOGGED_IN, "the logged-in status");
    assert_exchange(&world, &url, "callback-code");
}
