// The Tier-C/D ruling (fleet-uniform, 2026-09-28): stack-resident futures
// by design on hot paths (boxing 130 fns is allocation-churn with zero
// correctness gain); the fn-length threshold is a style gate, not
// correctness (the harness fns are intentionally linear); 64-bit targets -
// the narrowing sits at OS/protocol boundaries where the values are
// bounded (pid syscalls, epoch/elapsed milliseconds, calendar math,
// guarded parses), and checked conversions would add panic paths where
// silent wrap was deliberate (the one genuinely-suspect family, args.rs's
// parse_positive_u32 lacking its u32::MAX bound, is flagged in the lane
// dossier for the conductor).
#![allow(
    clippy::large_futures,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]

//! End-to-end ACP-mode verification: the real binary serves the ACP
//! JSON-RPC surface over stdio on the daemon-attached transport (a
//! sandboxed supervisor hosting a scripted faux worker), and the emitted
//! frames are checked against the TS capture corpus
//! (`crates/eukhe-daemon/testdata/acp`).

use std::io::{BufRead, BufReader, Write};
use std::process::{Child, Command, Stdio};
use std::sync::mpsc::{channel, Receiver};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

/// The child plus the tempdir it runs in: the tempdir must outlive the
/// child process (its cwd), so it is held on the struct.
struct AcpChild {
    child: Child,
    /// `None` once [`AcpChild::close_stdin`] sent EOF.
    stdin: Option<std::process::ChildStdin>,
    lines: Receiver<String>,
    next_id: u64,
    /// Held (never read) so the child's cwd directory outlives the process:
    /// dropping the tempdir deletes it and the child's `current_dir` fails.
    /// `None` for a second child sharing another child's home.
    _home: Option<tempfile::TempDir>,
    spawn_stderr: Option<std::process::ChildStderr>,
    /// The sandboxed supervisor socket the child spawned: the drop shuts
    /// the supervisor down with it (a killed child must not leak the
    /// supervisor into later test binaries).
    socket: std::path::PathBuf,
}

impl AcpChild {
    /// Wire one spawned process into the reader thread and the handle:
    /// the tempdir is held on the struct so the child's cwd directory
    /// outlives the process, and the supervisor socket is the one the
    /// drop shuts down.
    fn wrap(
        mut child: std::process::Child,
        home: Option<tempfile::TempDir>,
        socket: std::path::PathBuf,
    ) -> AcpChild {
        let stdin = child.stdin.take().expect("stdin piped");
        let stdout = child.stdout.take().expect("stdout piped");
        let stderr = child.stderr.take().expect("stderr piped");
        let (tx, lines) = channel();
        std::thread::spawn(move || {
            let reader = BufReader::new(stdout);
            for line in reader.lines() {
                match line {
                    Ok(line) => {
                        if tx.send(line).is_err() {
                            return;
                        }
                    }
                    Err(_) => return,
                }
            }
        });
        AcpChild {
            child,
            stdin: Some(stdin),
            lines,
            next_id: 0,
            _home: home,
            spawn_stderr: Some(stderr),
            socket,
        }
    }

    /// The daemon-attached transport: the child spawns its own sandboxed
    /// supervisor on `<home>/daemon.sock` and hosts the scripted worker
    /// through the `EUKHE_FAUX_SCRIPT` create-config seam;
    /// the drop shuts the supervisor down. The socket sits on the struct
    /// for tests that speak raw daemon commands alongside the ACP frames.
    fn spawn(args: &[&str], script: &serde_json::Value) -> AcpChild {
        let home = tempfile::TempDir::new().unwrap();
        let socket = home.path().join("daemon.sock");
        std::fs::write(home.path().join("worker-script.json"), script.to_string()).unwrap();
        let child = daemon_attached_command(home.path(), &socket, args)
            .spawn()
            .expect("binary present");
        Self::wrap(child, Some(home), socket)
    }

    /// The daemon-attached lane whose `rlm.spawn` children are scripted:
    /// `<home>/child-script.json` rides the `EUKHE_FAUX_CHILD_SCRIPT`
    /// create-config seam (the worker already consumes the key), and the
    /// parent worker's kernel runs the given interpreter (the env flows
    /// ACP -> supervisor -> worker).
    fn spawn_with_child_script(
        args: &[&str],
        script: &serde_json::Value,
        child_script: &serde_json::Value,
        kernel_python: &std::path::Path,
    ) -> AcpChild {
        let home = tempfile::TempDir::new().unwrap();
        let socket = home.path().join("daemon.sock");
        let child_script_path = home.path().join("child-script.json");
        std::fs::write(home.path().join("worker-script.json"), script.to_string()).unwrap();
        std::fs::write(&child_script_path, child_script.to_string()).unwrap();
        let child = daemon_attached_command(home.path(), &socket, args)
            .env("EUKHE_FAUX_CHILD_SCRIPT", &child_script_path)
            .env("EUKHE_KERNEL_PYTHON", kernel_python)
            .spawn()
            .expect("binary present");
        Self::wrap(child, Some(home), socket)
    }

    fn send(&mut self, frame: &Value) {
        let mut line = serde_json::to_string(&frame).unwrap();
        line.push('\n');
        let stdin = self.stdin.as_mut().expect("stdin open");
        stdin.write_all(line.as_bytes()).unwrap();
        stdin.flush().unwrap();
    }

    /// Send EOF: the client disconnects.
    fn close_stdin(&mut self) {
        self.stdin = None;
    }

    fn request(&mut self, method: &str, params: &Value) -> u64 {
        self.next_id += 1;
        let id = self.next_id;
        self.send(&json!({ "jsonrpc": "2.0", "id": id, "method": method, "params": params }));
        id
    }

    fn notify(&mut self, method: &str, params: &Value) {
        self.send(&json!({ "jsonrpc": "2.0", "method": method, "params": params }));
    }

    /// Read frames until the request `id` answers; returns the answer with
    /// the notifications seen before it, in order.
    fn wait_response(&mut self, id: u64, timeout: Duration) -> (Value, Vec<Value>) {
        let deadline = Instant::now() + timeout;
        let mut notifications = Vec::new();
        loop {
            let timeout_left = deadline.saturating_duration_since(Instant::now());
            assert!(
                !timeout_left.is_zero(),
                "timed out waiting for response {id}"
            );
            match self.lines.recv_timeout(timeout_left) {
                Ok(line) => {
                    let frame: Value = serde_json::from_str(&line).expect("valid JSON line");
                    if frame.get("id").and_then(Value::as_u64) == Some(id)
                        && (frame.get("result").is_some() || frame.get("error").is_some())
                    {
                        return (frame, notifications);
                    }
                    notifications.push(frame);
                }
                Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                    panic!("timed out waiting for response {id}")
                }
                Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
                    panic!("ACP server closed stdout")
                }
            }
        }
    }

    /// Read frames until one matches — the predicate readiness signal,
    /// never a timer. The frames before it are dropped.
    fn wait_frame(
        &mut self,
        timeout: Duration,
        mut frame_matches: impl FnMut(&Value) -> bool,
    ) -> Value {
        let deadline = Instant::now() + timeout;
        loop {
            let timeout_left = deadline.saturating_duration_since(Instant::now());
            assert!(
                !timeout_left.is_zero(),
                "the stream never published the awaited frame"
            );
            let line = self
                .lines
                .recv_timeout(timeout_left)
                .expect("the ACP stream stayed open");
            let frame: Value = serde_json::from_str(&line).expect("valid JSON line");
            if frame_matches(&frame) {
                return frame;
            }
        }
    }

    /// Read frames until one `sessionUpdate` of `kind` arrives — the
    /// observed-event readiness signal, never a timer. The frames
    /// before it are dropped.
    fn wait_update(&mut self, kind: &str, timeout: Duration) {
        self.wait_frame(timeout, |frame| {
            frame["params"]["update"]["sessionUpdate"] == kind
        });
    }
}

/// The daemon-attached child's command on `home` and `socket`: the
/// supervisor-lost exit (TS `exitIfSupervisorOrphanedForTooLong`) runs on
/// a short window (the env flows child -> supervisor -> worker) instead
/// of the 5-minute default, and the worker script is
/// `<home>/worker-script.json`.
fn daemon_attached_command(
    home: &std::path::Path,
    socket: &std::path::Path,
    args: &[&str],
) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_eukhe"));
    command
        .args(args)
        .arg("--daemon-socket")
        .arg(socket)
        .env("HOME", home)
        .env("EUKHE_FAUX_SCRIPT", home.join("worker-script.json"))
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "15000",
        )
        .current_dir(home)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    command
}

/// The sandbox's single worker descriptor.
fn worker_descriptor(home: &std::path::Path) -> Value {
    std::fs::read_dir(home.join(".eukhe/daemon-workers"))
        .expect("descriptor instances")
        .flatten()
        .flat_map(|instance| {
            std::fs::read_dir(instance.path())
                .expect("instance dir")
                .flatten()
        })
        .filter_map(|file| {
            serde_json::from_str::<Value>(&std::fs::read_to_string(file.path()).ok()?).ok()
        })
        .find(|descriptor| descriptor.get("authenticationToken").is_some())
        .expect("the worker descriptor")
}

impl Drop for AcpChild {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
        if let Some(mut stderr) = self.spawn_stderr.take() {
            use std::io::Read;
            let mut text = String::new();
            let _ = stderr.read_to_string(&mut text);
            if !text.is_empty() {
                eprintln!("ACP child stderr: {text}");
            }
        }
        shutdown_sandboxed_daemon(&self.socket);
    }
}

fn initialize_params() -> Value {
    json!({
        "protocolVersion": 1,
        "clientCapabilities": {},
        "clientInfo": { "name": "acp-e2e", "title": "ACP E2E", "version": "0.0.1" },
    })
}

const TIMEOUT: Duration = Duration::from_mins(1);

/// Assert a settled turn's stop reason, printing the whole response
/// envelope on mismatch: an `internal_error`'s failure text (the
/// `eukhe turn failed: <failure>` message) is otherwise lost — the
/// `stopReason: null` arms of `assert_eq!` show only the null.
fn assert_end_turn(response: &Value) {
    assert_eq!(
        response["result"]["stopReason"], "end_turn",
        "the turn's response envelope: {response}"
    );
}

/// `initialize` + `session/new` on a daemon-attached child; the ACP session id.
fn initialize_and_new_session(client: &mut AcpChild) -> String {
    let init = client.request("initialize", &initialize_params());
    let _ = client.wait_response(init, TIMEOUT);
    new_session(client)
}

fn new_session(client: &mut AcpChild) -> String {
    let new = client.request("session/new", &json!({ "mcpServers": [] }));
    let (new_response, _) = client.wait_response(new, TIMEOUT);
    new_response["result"]["sessionId"]
        .as_str()
        .unwrap_or_else(|| panic!("session/new succeeds: {new_response}"))
        .to_string()
}

fn assert_prompt_ends_turn(client: &mut AcpChild, session_id: &str, text: &str) -> Vec<Value> {
    let prompt = client.request(
        "session/prompt",
        &json!({ "sessionId": session_id, "prompt": [{ "type": "text", "text": text }] }),
    );
    let (prompt_response, updates) = client.wait_response(prompt, Duration::from_mins(2));
    assert_eq!(
        prompt_response["result"]["stopReason"], "end_turn",
        "{prompt_response}"
    );
    updates
}

/// The supervisor's live sessions (`list`).
fn live_sessions(socket: &std::path::Path) -> Vec<Value> {
    let list = daemon_request(
        socket,
        "live-sessions",
        &json!({ "type": "list", "includeClientOwned": true }),
    );
    list["data"]["sessions"]
        .as_array()
        .unwrap_or_else(|| panic!("a session list: {list}"))
        .clone()
}

/// Stop the sandboxed supervisor a test spawned (the shared-daemon
/// product behavior leaves it running; a test owns its sandbox).
fn shutdown_sandboxed_daemon(socket: &std::path::Path) {
    use std::io::Write as _;
    let Ok(mut stream) = eukhe_types::platform::transport::connect_blocking(socket) else {
        return;
    };
    let frame = format!(
            "{{\"type\":\"command\",\"id\":\"shutdown-test\",\"protocol\":{{\"name\":\"eukhe.daemon\",\"version\":{}}},\"command\":{{\"type\":\"shutdown\"}}}}\n",
            eukhe_types::daemon::DAEMON_PROTOCOL_VERSION
        );
    let _ = stream.write_all(frame.as_bytes());
    let _ = stream.flush();
    // The supervisor exits after the shutdown response.
    std::thread::sleep(Duration::from_millis(300));
}

/// One raw daemon command on a fresh connection (the hello frame is skipped by the id match).
fn daemon_request(socket: &std::path::Path, id: &str, command: &Value) -> Value {
    use std::io::{BufRead as _, BufReader, Write as _};
    let mut writer =
        eukhe_types::platform::transport::connect_blocking(socket).expect("daemon socket");
    let reader = writer.try_clone_box().expect("daemon socket clone");
    let _ = reader.set_read_timeout(Duration::from_mins(2));
    let protocol =
        json!({ "name": "eukhe.daemon", "version": eukhe_types::daemon::DAEMON_PROTOCOL_VERSION });
    let frame = json!({ "type": "command", "id": id, "protocol": protocol, "command": command });
    writeln!(writer, "{frame}").expect("daemon frame");
    writer.flush().expect("daemon flush");
    BufReader::new(reader)
        .lines()
        .map(|line| {
            serde_json::from_str::<Value>(&line.expect("daemon line")).expect("daemon JSON")
        })
        .find(|frame| frame["id"] == json!(id))
        .unwrap_or_else(|| panic!("the daemon closed without answering {id}"))
}

/// The kernel Python with eukhe-runtime installed; set
/// `EUKHE_E2E_KERNEL_PYTHON` to point at an explicit interpreter instead.
/// Without one, the live RLM quiescence lanes below skip (with a note).
fn kernel_python() -> Option<std::path::PathBuf> {
    if let Some(explicit) = std::env::var_os("EUKHE_E2E_KERNEL_PYTHON") {
        let explicit = std::path::PathBuf::from(explicit);
        assert!(
            explicit.exists(),
            "EUKHE_E2E_KERNEL_PYTHON {} not found",
            explicit.display()
        );
        return Some(explicit);
    }
    let candidate = std::path::PathBuf::from(std::env::var("HOME").map_or_else(
        |_| "/home/ubuntu/.eukhe/kernel-venv/bin/python".to_string(),
        |home| format!("{home}/.eukhe/kernel-venv/bin/python"),
    ));
    if candidate.exists() {
        return Some(candidate);
    }
    eprintln!(
        "kernel python {} not found; skipping live RLM quiescence e2e",
        candidate.display()
    );
    None
}

mod compaction_rlm;
mod daemon_attached;
mod protocol;
mod stop_close;
