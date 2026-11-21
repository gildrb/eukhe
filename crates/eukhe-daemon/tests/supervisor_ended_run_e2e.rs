//! End-to-end verifier for the runs the supervisor interrupts itself: a
//! worker that stopped answering (stopped by a signal mid-turn) is killed
//! and restarted, and a worker that crashes past the restart budget is
//! relaunched once more by itself. Either way the reopen stops the run the
//! storage holds, writes the notice row that says why, and continues the
//! turn with no client prompting it.

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
        .env_remove("EUKHE_CODING_AGENT_DIR")
        // A supervisor killed at teardown must not leak its workers.
        .env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "15000",
        ),
        socket,
    );
    wait_until("the supervisor socket", || {
        eukhe_types::platform::endpoints::endpoint_exists(socket)
    });
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
    /// The selector commands address: the active session id.
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

    /// The reopen wrote one notice row and continued the turn by itself:
    /// the continuation is answered after the row, with no prompt.
    fn assert_continued(&mut self, notice: &str) {
        wait_until("the continued turn's answer", || {
            let messages = self.messages();
            messages
                .iter()
                .position(|message| message["customType"] == NOTICE)
                .is_some_and(|row| {
                    messages[row..]
                        .iter()
                        .any(|message| message["role"] == "assistant" && text(message) == "done")
                })
        });
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
    }
}

#[test]
fn a_worker_that_stops_answering_is_restarted_and_its_turn_continues() {
    let mut session = Session::open("hung-worker");
    session.start_hung_turn();
    let hung = session.worker_pid();
    signal(hung, "STOP");
    session.answer_at_once();
    wait_until("the hung worker's kill", || {
        session.log_contains("did not answer for 60s; killing it to restart it")
    });
    wait_until("the hung worker's exit", || !process_alive(hung));
    session.assert_continued(
        "The session worker stopped responding for 60s; Eukhe restarted it and continued the turn (automatic continue 1 of this turn).",
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

#[test]
fn a_crash_loop_past_the_restart_budget_continues_its_turn() {
    let mut session = Session::open("crash-loop");
    session.start_hung_turn();
    // Each relaunch replays the create and resumes the run: kill every
    // worker the supervisor brings up until the restart budget runs out.
    for kill in 0..6 {
        if kill == 5 {
            session.answer_at_once();
        }
        let pid = session.worker_pid();
        signal(pid, "KILL");
        wait_until("the killed worker's exit", || !process_alive(pid));
    }
    // Nobody reopens the session: the supervisor relaunches the worker by
    // itself, and its reopen continues the turn.
    wait_until("the relaunch past the budget", || {
        session.log_contains(
            "failed 6 times in the restart window; relaunching it to continue its turn",
        )
    });
    session.assert_continued(
        "The session worker crashed 6 times in a row; Eukhe restarted it and continued the turn (automatic continue 1 of this turn).",
    );
}
