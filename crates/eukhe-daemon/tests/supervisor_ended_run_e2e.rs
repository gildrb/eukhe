//! End-to-end verifier for the runs the supervisor ends itself: a worker
//! that stopped answering (stopped by a signal mid-turn) is killed and
//! restarted. The session's turn ends with the notice row that says why
//! (no client waits on a run that will not answer), the run the storage
//! holds does not go on, and the next prompt in the same session is
//! answered.

use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
#[path = "support/wire_client.rs"]
mod wire_client;
use daemon::supervisor_args;
use process::Daemon;
use wire_client::WireClient;

const ROUTE: Duration = Duration::from_secs(60);
/// The responsiveness probe's window (60 s) plus its confirming ping, the
/// kill, and the relaunch.
const DEADLINE: Duration = Duration::from_secs(150);
const NOTICE: &str = "eukhe.worker_restart";

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
        std::thread::sleep(Duration::from_millis(100));
    }
}

fn signal(pid: u64, name: &str) {
    let _ = Command::new("kill")
        .args([&format!("-{name}"), &pid.to_string()])
        .stderr(Stdio::null())
        .status();
}

fn process_alive(pid: u64) -> bool {
    Command::new("kill")
        .args(["-0", &pid.to_string()])
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
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

/// One session over a faux script whose generation holds its run open for
/// ten minutes.
struct Session {
    _dir: tempfile::TempDir,
    socket: std::path::PathBuf,
    agent_dir: std::path::PathBuf,
    script: std::path::PathBuf,
    _supervisor: Daemon,
    client: WireClient,
    id: String,
}

impl Session {
    fn open(name: &str) -> Session {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let agent_dir = dir.path().join("agent");
        let sessions = agent_dir.join("sessions");
        std::fs::create_dir_all(&sessions).expect("sessions dir");
        let socket = dir.path().join("daemon.sock");
        let script = dir.path().join("faux.json");
        std::fs::write(
            &script,
            json!({ "engine": "faux", "responses": [
                { "text": "hung", "delayMs": 600_000 },
            ] })
            .to_string(),
        )
        .expect("write faux script");
        let supervisor = spawn_supervisor(&socket, &agent_dir);
        let mut client = WireClient::connect(&socket);
        let created = client.request(
            &json!({
                "type": "create",
                "config": {
                    "cwd": dir.path().to_string_lossy(),
                    "sessionDir": sessions.to_string_lossy(),
                    "script": script.to_string_lossy(),
                    "name": name,
                },
            }),
            ROUTE,
        );
        assert_eq!(created["success"], true, "create failed: {created}");
        let id = created["data"]["activeSessionId"]
            .as_str()
            .expect("active session id")
            .to_string();
        Session {
            _dir: dir,
            socket,
            agent_dir,
            script,
            _supervisor: supervisor,
            client,
            id,
        }
    }

    fn request(&mut self, mut command: Value) -> Value {
        command["activeSessionId"] = json!(self.id);
        self.client.request(&command, ROUTE)
    }

    fn messages(&mut self) -> Vec<Value> {
        let response = self.request(json!({ "type": "get_messages" }));
        response["data"]["messages"]
            .as_array()
            .cloned()
            .unwrap_or_default()
    }

    fn worker_pid(&mut self) -> u64 {
        let state = self.request(json!({ "type": "get_state" }));
        assert_eq!(state["success"], true, "get_state failed: {state}");
        state["data"]["workerPid"].as_u64().expect("worker pid")
    }

    /// Prompt and wait until the faux generation holds the run open.
    fn start_hung_turn(&mut self) {
        let prompted = self.request(json!({ "type": "prompt", "message": "go" }));
        assert_eq!(prompted["success"], true, "prompt failed: {prompted}");
        wait_until("the run to stream", || {
            let state = self.request(json!({ "type": "get_state" }));
            state["data"]["isStreaming"] == true
        });
    }

    /// From now on every generation answers at once: a run a reopen
    /// resumed would answer before the next prompt does.
    fn answer_at_once(&self) {
        std::fs::write(
            &self.script,
            json!({ "engine": "faux", "responses": ["done"], "repeatLastResponse": true })
                .to_string(),
        )
        .expect("rewrite faux script");
    }

    fn log_contains(&self, needle: &str) -> bool {
        std::fs::read_to_string(eukhe_daemon::paths::daemon_log_path(
            &self.socket,
            &self.agent_dir,
        ))
        .is_ok_and(|log| log.contains(needle))
    }

    /// The turn ended with the notice and no run goes on; then the next
    /// prompt in the session is answered.
    fn assert_ended_then_answers(&mut self, notice: &str) {
        let idle = self.request(json!({ "type": "wait_for_idle" }));
        assert_eq!(idle["success"], true, "never went idle: {idle}");
        let messages = self.messages();
        let notices: Vec<String> = messages
            .iter()
            .filter(|message| message["customType"] == NOTICE)
            .map(text)
            .collect();
        assert_eq!(
            notices,
            [notice.to_string()],
            "one notice row: {messages:?}"
        );
        assert!(
            !messages
                .iter()
                .any(|message| message["role"] == "assistant" && text(message) == "done"),
            "the interrupted run did not resume: {messages:?}"
        );
        let prompted = self.request(json!({ "type": "prompt", "message": "again" }));
        assert_eq!(prompted["success"], true, "prompt failed: {prompted}");
        wait_until("the next prompt's answer", || {
            let messages = self.messages();
            messages
                .iter()
                .position(|message| message["role"] == "user" && text(message) == "again")
                .is_some_and(|again| {
                    messages[again..]
                        .iter()
                        .any(|message| message["role"] == "assistant" && text(message) == "done")
                })
        });
    }
}

#[test]
fn a_worker_that_stops_answering_is_restarted_and_its_turn_ends() {
    let mut session = Session::open("hung-worker");
    session.start_hung_turn();
    let hung = session.worker_pid();
    signal(hung, "STOP");
    session.answer_at_once();
    wait_until("the hung worker's kill", || {
        session.log_contains("did not answer for 60s; killing it to restart it")
    });
    wait_until("the hung worker's exit", || !process_alive(hung));
    session.assert_ended_then_answers(
        "The session worker stopped responding for 60s; Eukhe restarted it and stopped the turn. Send the message again to retry.",
    );
    assert_ne!(
        session.worker_pid(),
        hung,
        "a fresh worker serves the session"
    );
}

#[test]
fn a_worker_paused_inside_the_window_keeps_its_run() {
    let mut session = Session::open("paused-worker");
    session.start_hung_turn();
    let paused = session.worker_pid();
    signal(paused, "STOP");
    std::thread::sleep(Duration::from_secs(40));
    signal(paused, "CONT");
    let state = session.request(json!({ "type": "get_state" }));
    assert_eq!(
        state["data"]["isStreaming"], true,
        "the run goes on: {state}"
    );
    assert_eq!(session.worker_pid(), paused, "the same worker serves it");
    assert!(
        !session.log_contains("did not answer"),
        "a worker paused inside the window is never killed"
    );
}
