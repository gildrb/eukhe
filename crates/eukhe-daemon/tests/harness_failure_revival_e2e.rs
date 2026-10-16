//! End-to-end verifier for a worker whose durable Harness fails mid-run (a
//! Storage error: here the session's files turn unwritable, as on a full
//! disk). The worker must not linger as a "busy" zombie: it records the
//! typed failure, exits, and the supervisor revives the session from
//! Storage, where the run resumes and the steer queued before the failure
//! is delivered and answered.
#![allow(clippy::too_many_lines)]

use std::io::{BufRead, BufReader, Write};
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_args;
use process::Daemon;

const DEADLINE: Duration = Duration::from_secs(60);

fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Daemon {
    let supervisor = Daemon::spawn(
        supervisor_args(
            &mut Command::new(env!("CARGO_BIN_EXE_eukhe-daemon")),
            socket,
            agent_dir,
        )
        .env_remove("PRIME_API_KEY")
        .env_remove("EUKHE_CODING_AGENT_DIR")
        // A supervisor killed at teardown must not leak its workers.
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "15000",
        ),
        socket,
    );
    wait_until("the supervisor socket", || socket.exists());
    supervisor
}

#[track_caller]
fn wait_until(what: &str, mut done: impl FnMut() -> bool) {
    let deadline = Instant::now() + DEADLINE;
    while !done() {
        assert!(Instant::now() < deadline, "timed out waiting for {what}");
        std::thread::sleep(Duration::from_millis(50));
    }
}

struct Client {
    reader: BufReader<std::os::unix::net::UnixStream>,
    writer: std::os::unix::net::UnixStream,
    next_id: u64,
}

impl Client {
    fn connect(socket: &Path) -> Client {
        let stream = std::os::unix::net::UnixStream::connect(socket).expect("connect");
        stream
            .set_read_timeout(Some(Duration::from_mins(2)))
            .expect("read timeout");
        let writer = stream.try_clone().expect("clone");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
            next_id: 0,
        };
        assert_eq!(client.read_line()["type"], "daemon_hello");
        client
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        loop {
            line.clear();
            let read = self.reader.read_line(&mut line).expect("read line");
            assert!(read > 0, "the supervisor closed the connection");
            if !line.trim().is_empty() {
                return serde_json::from_str(line.trim()).expect("parse line");
            }
        }
    }

    /// Send `command` and return its response (events are skipped).
    fn request(&mut self, command: Value) -> Value {
        self.next_id += 1;
        let id = format!("r{}", self.next_id);
        let mut envelope = json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": 7 },
        });
        envelope["command"] = command;
        let mut line = serde_json::to_string(&envelope).expect("serialize");
        line.push('\n');
        self.writer
            .write_all(line.as_bytes())
            .expect("write command");
        loop {
            let response = self.read_line();
            if response.get("id").and_then(Value::as_str) == Some(id.as_str()) {
                return response;
            }
        }
    }
}

/// The text of a wire message (string content or text parts).
fn text(message: &Value) -> String {
    match &message["content"] {
        Value::String(text) => text.clone(),
        Value::Array(parts) => parts
            .iter()
            .filter_map(|part| part["text"].as_str())
            .collect(),
        _ => String::new(),
    }
}

/// Make `dir`'s tree unwritable (or writable again).
fn set_writable(dir: &Path, writable: bool) {
    let (dir_mode, file_mode) = if writable {
        (0o755, 0o644)
    } else {
        (0o555, 0o444)
    };
    for entry in std::fs::read_dir(dir).expect("storage dir") {
        let path = entry.expect("storage entry").path();
        if path.is_dir() {
            set_writable(&path, writable);
        } else {
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(file_mode))
                .expect("file mode");
        }
    }
    std::fs::set_permissions(dir, std::fs::Permissions::from_mode(dir_mode)).expect("dir mode");
}

fn process_alive(pid: u64) -> bool {
    Command::new("kill")
        .args(["-0", &pid.to_string()])
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

#[test]
fn a_failed_harness_exits_the_worker_and_the_revival_drains_the_steer() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let sessions = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions).expect("sessions dir");
    let socket = dir.path().join("daemon.sock");
    let script = dir.path().join("faux.json");
    // A tool round, then a generation that holds the run open.
    std::fs::write(
        &script,
        json!({ "engine": "faux", "responses": [
            { "content": [{ "type": "toolCall", "name": "missing_tool", "arguments": {}, "id": "call-1" }] },
            { "text": "lost", "delayMs": 600_000 },
        ] })
        .to_string(),
    )
    .expect("write faux script");
    let _supervisor = spawn_supervisor(&socket, &agent_dir);
    let mut client = Client::connect(&socket);
    let created = client.request(json!({
        "type": "create",
        "config": {
            "cwd": dir.path().to_string_lossy(),
            "sessionDir": sessions.to_string_lossy(),
            "script": script.to_string_lossy(),
            "name": "harness-failure",
        },
    }));
    assert_eq!(created["success"], true, "create failed: {created}");
    let session = created["data"]["activeSessionId"]
        .as_str()
        .expect("active session id")
        .to_string();
    let messages = |client: &mut Client| -> Option<Vec<Value>> {
        let response =
            client.request(json!({ "type": "get_messages", "activeSessionId": session }));
        (response["success"] == true).then(|| {
            response["data"]["messages"]
                .as_array()
                .cloned()
                .unwrap_or_default()
        })
    };

    let prompted = client.request(json!({
        "type": "prompt", "activeSessionId": session, "message": "go",
    }));
    assert_eq!(prompted["success"], true, "prompt failed: {prompted}");
    wait_until("the tool round", || {
        messages(&mut client).is_some_and(|messages| {
            messages
                .iter()
                .any(|message| message["role"] == "toolResult")
        })
    });
    let steered = client.request(json!({
        "type": "steer", "activeSessionId": session, "message": "S",
    }));
    assert_eq!(steered["success"], true, "steer failed: {steered}");
    let state = client.request(json!({ "type": "get_state", "activeSessionId": session }));
    assert_eq!(state["success"], true, "get_state failed: {state}");
    let worker_pid = state["data"]["workerPid"].as_u64().expect("worker pid");
    let storage = PathBuf::from(
        state["data"]["sessionFile"]
            .as_str()
            .expect("session storage"),
    );
    // The revived worker reads the script anew: it answers at once.
    std::fs::write(
        &script,
        json!({ "engine": "faux", "responses": ["done"], "repeatLastResponse": true }).to_string(),
    )
    .expect("rewrite faux script");

    // The disk refuses writes: the next commit fails the Harness.
    set_writable(&storage, false);
    let refused = client.request(json!({
        "type": "follow_up", "activeSessionId": session, "message": "refused",
    }));
    assert_eq!(
        refused["success"], false,
        "the failing commit answers: {refused}"
    );
    let log = eukhe_daemon::paths::daemon_log_path(&socket, &agent_dir);
    wait_until("the worker's harness-failure exit", || {
        std::fs::read_to_string(&log)
            .is_ok_and(|log| log.contains("exited unexpectedly (durable session failed"))
    });
    set_writable(&storage, true);
    assert!(!process_alive(worker_pid), "the failed worker exited");

    // The revival resumes the run, and the queued steer is answered.
    wait_until("the steer's answer after the revival", || {
        messages(&mut client).is_some_and(|messages| {
            messages
                .iter()
                .position(|message| message["role"] == "user" && text(message) == "S")
                .is_some_and(|steer| {
                    messages[steer..]
                        .iter()
                        .any(|message| message["role"] == "assistant")
                })
        })
    });
    let idle = client.request(json!({ "type": "wait_for_idle", "activeSessionId": session }));
    assert_eq!(idle["success"], true, "never went idle: {idle}");
    let users: Vec<String> = messages(&mut client)
        .expect("messages")
        .iter()
        .filter(|message| message["role"] == "user")
        .map(text)
        .collect();
    assert_eq!(users, ["go", "S"]);
}
