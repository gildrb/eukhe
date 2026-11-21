//! End-to-end verifier for the autonomous run: a daemon worker session
//! over the scripted faux engine. A run with checks (the commands of the
//! removed gates are command checks) takes the checks' return with its
//! evidence and stops when the checks end the claim; a run without checks
//! is continued with its prompt, as a durable user row, until the
//! session's budget (the removed limits set it) stops it. Neither stop
//! writes a row.
use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_command;
use process::Daemon;

// The durable session storage reader the CLI e2e suites share.
#[path = "../../eukhe-cli/tests/support/durable_store.rs"]
mod durable_store;

fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Daemon {
    std::fs::create_dir_all(agent_dir).expect("agent dir");
    Daemon::spawn_bound(
        supervisor_command(socket, agent_dir)
            .env_remove("EUKHE_CODING_AGENT_DIR")
            // A supervisor killed at teardown must not leak its session workers
            // into later test binaries: the worker's supervisor-lost exit (TS
            // `exitIfSupervisorOrphanedForTooLong`) runs on this short window
            // instead of the 5-minute default.
            .env(
                eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
                "15000",
            ),
        socket,
        Duration::from_secs(10),
    )
}

/// One client connection: request/response plus every session event that
/// streamed while the response was outstanding.
struct Client {
    reader: BufReader<std::os::unix::net::UnixStream>,
    writer: std::os::unix::net::UnixStream,
    events: Vec<Value>,
}

impl Client {
    fn connect(socket: &Path) -> Client {
        let stream = eukhe_types::platform::transport::connect_std(socket).expect("connect");
        let writer = stream.try_clone().expect("clone");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
            events: Vec::new(),
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

    fn send_command(&mut self, id: &str, command: &Value) {
        let envelope = json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "command": command,
        });
        let mut line = serde_json::to_string(&envelope).expect("serialize");
        line.push('\n');
        self.writer
            .write_all(line.as_bytes())
            .unwrap_or_else(|error| panic!("write command {id}: {error}"));
    }

    /// The response for `id`, with every session event observed on the way.
    fn request(&mut self, id: &str) -> Value {
        let deadline = Instant::now() + Duration::from_mins(3);
        loop {
            assert!(Instant::now() < deadline, "no response for id {id}");
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                return line;
            }
            self.collect_event(&line);
        }
    }

    fn collect_event(&mut self, line: &Value) {
        if line.get("type").and_then(Value::as_str) == Some("session_event") {
            self.events.push(line["event"].clone());
        }
    }

    /// Drain pending session events until the socket stays quiet for
    /// `quiet_ms` (the supervisor buffers a routed command's events).
    fn drain_events(&mut self, quiet_ms: Duration) {
        let deadline = Instant::now() + Duration::from_secs(30);
        let mut last_line = Instant::now();
        let mut line = String::new();
        loop {
            assert!(Instant::now() < deadline, "event drain timed out");
            self.reader
                .get_mut()
                .set_read_timeout(Some(Duration::from_millis(100)))
                .expect("timeout");
            match self.reader.read_line(&mut line) {
                Ok(0) => return,
                Ok(_) => {
                    let value: Value = serde_json::from_str(line.trim()).expect("parse line");
                    self.collect_event(&value);
                    last_line = Instant::now();
                    line.clear();
                }
                Err(_) => {
                    if last_line.elapsed() >= quiet_ms {
                        return;
                    }
                }
            }
        }
    }
}

/// The harness: a supervisor and a faux-scripted session over the real
/// agent engine.
struct Harness {
    dir: tempfile::TempDir,
    _supervisor: Daemon,
    client: Client,
    session_id: String,
}

fn setup(name: &str, responses: &Value) -> Harness {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let script = dir.path().join("faux.json");
    std::fs::write(
        &script,
        json!({ "engine": "faux", "responses": responses }).to_string(),
    )
    .expect("write faux script");
    // The session works in a directory of its own: the checks fingerprint
    // it, and the agent dir (the session's own storage) is outside it.
    let work = dir.path().join("work");
    std::fs::create_dir_all(&work).expect("work dir");
    let socket = dir.path().join(format!("{name}.sock"));
    let supervisor = spawn_supervisor(&socket, &agent_dir);
    let mut client = Client::connect(&socket);
    client.send_command(
        "c1",
        &json!({
            "type": "create",
            "config": {
                "cwd": work.to_string_lossy(),
                "sessionDir": session_dir.to_string_lossy(),
                "script": script.to_string_lossy(),
            },
        }),
    );
    let created = client.request("c1");
    assert_eq!(created["success"], true, "create failed: {created}");
    let session_id = created["data"]["activeSessionId"]
        .as_str()
        .or_else(|| created["data"]["id"].as_str())
        .expect("active session id")
        .to_string();
    client.send_command(
        "a1",
        &json!({ "type": "attach", "activeSessionId": session_id }),
    );
    let attached = client.request("a1");
    assert_eq!(attached["success"], true, "attach failed: {attached}");
    Harness {
        dir,
        _supervisor: supervisor,
        client,
        session_id,
    }
}

impl Harness {
    /// Run one prompt to completion and drain its events.
    fn prompt(&mut self, id: &str, message: &str) {
        self.client.send_command(
            id,
            &json!({
                "type": "prompt_and_wait",
                "activeSessionId": self.session_id,
                "message": message,
            }),
        );
        let done = self.client.request(id);
        assert_eq!(done["success"], true, "prompt {id} failed: {done}");
        self.client.drain_events(Duration::from_secs(1));
    }

    /// The session's durable main transcript (the only session in the dir).
    fn transcript(&self) -> durable_store::Transcript {
        let session_dir = self.dir.path().join("agent").join("sessions");
        let dirs = durable_store::session_dirs(&session_dir);
        assert_eq!(dirs.len(), 1, "one session storage: {dirs:?}");
        durable_store::read_transcript(&dirs[0])
    }

    /// The wire events of one kind: `message_end` frames carrying the role.
    fn message_ends(&self, role: &str) -> Vec<Value> {
        self.client
            .events
            .iter()
            .filter(|event| {
                event.get("type").and_then(Value::as_str) == Some("message_end")
                    && event["message"]["role"] == role
            })
            .map(|event| event["message"].clone())
            .collect()
    }

    /// The texts of the durable `eukhe.custom` rows of one `customType`: a
    /// model-visible row carries its content as its model message, a
    /// display-only one in `data.content`.
    fn custom_texts(&self, custom_type: &str) -> Vec<String> {
        self.transcript()
            .of_kind("eukhe.custom")
            .into_iter()
            .filter(|entry| entry["data"]["customType"] == custom_type)
            .map(|entry| match entry["model"].get(0) {
                Some(message) => text_of(message),
                None => text_of(&entry["data"]),
            })
            .collect()
    }
}

/// The message's text: user/assistant rows carry content blocks, custom
/// rows a plain string.
fn text_of(message: &Value) -> String {
    match &message["content"] {
        Value::String(text) => text.clone(),
        content => content
            .as_array()
            .and_then(|blocks| blocks.first())
            .and_then(|block| block.get("text"))
            .and_then(Value::as_str)
            .unwrap_or_default()
            .to_string(),
    }
}

/// The durable message entries of one role (`pi.user`, `pi.assistant`), in
/// order.
fn durable_messages(harness: &Harness, role: &str) -> Vec<String> {
    harness
        .transcript()
        .of_kind(&format!("pi.{role}"))
        .into_iter()
        .filter_map(|entry| entry["model"].get(0).map(text_of))
        .collect()
}

/// The durable `autonomous_status` row texts that start with `prefix`.
fn durable_autonomous_rows(harness: &Harness, prefix: &str) -> Vec<String> {
    harness
        .custom_texts("autonomous_status")
        .into_iter()
        .filter(|text| text.starts_with(prefix))
        .collect()
}

#[test]
fn autonomous_gate_is_a_check_whose_end_stops_the_run() {
    let mut harness = setup(
        "gate",
        &json!([{ "text": "first attempt" }, { "text": "fixed it" }, { "text": "unused" }]),
    );
    // A gate that always fails, with one return: the claim goes back once,
    // then the checks end it failed. The intent check is off (no judge
    // model in the script).
    harness.prompt("enable", "/auto on --gate false --gate-retries 1");
    harness.prompt("intent", "/accept intent off");
    assert_eq!(harness.message_ends("assistant"), Vec::<Value>::new());
    assert_eq!(
        durable_autonomous_rows(&harness, "[autonomous-status: on]").len(),
        1,
        "enable row durable"
    );

    harness.prompt("go", "build the feature");

    let assistants: Vec<String> = harness
        .message_ends("assistant")
        .iter()
        .map(text_of)
        .collect();
    assert_eq!(
        assistants,
        vec!["first attempt".to_string(), "fixed it".to_string()],
        "events: {:?}",
        harness.client.events
    );
    // The return is the checks' (a Director input with the evidence), not
    // a continuation of the run's own.
    let durable_users = durable_messages(&harness, "user");
    assert_eq!(
        durable_users.len(),
        2,
        "durable user rows: {durable_users:?}"
    );
    assert!(
        durable_users[1].starts_with("[acceptance: not verified]")
            && durable_users[1].contains("(return 1 of 1)")
            && durable_users[1].contains("command `false` (expect exit 0): refuted"),
        "the checks' return: {}",
        durable_users[1]
    );
    assert!(
        harness
            .message_ends("custom")
            .iter()
            .all(|message| message["customType"] != "autonomous_continuation"),
        "no continuation of the run's own, events: {:?}",
        harness.client.events
    );
    assert!(
        durable_autonomous_rows(&harness, "[autonomous-stop:").is_empty(),
        "no durable stop row"
    );
}

#[test]
fn autonomous_runs_until_its_budget_stops_it() {
    let mut harness = setup(
        "limit",
        &json!([{ "text": "still working" }, { "text": "more work" }, { "text": "unused" }]),
    );
    // The removed `--max-turns 2` is the run's limit of two model
    // requests; no checks: the run is continued with its prompt.
    harness.prompt("enable", "/auto on --max-turns 2");
    harness.prompt("clear", "/accept clear");
    harness.prompt("go", "build the feature");

    // The first answer is continued; the second is the run's final answer
    // from the budget's reserve, and the budget stops the run.
    let assistants: Vec<String> = harness
        .message_ends("assistant")
        .iter()
        .map(text_of)
        .collect();
    assert_eq!(
        assistants,
        vec!["still working".to_string(), "more work".to_string()],
        "events: {:?}",
        harness.client.events
    );
    // The user sees their own prompt only: the continuation reaches the
    // wire as a hidden custom message, which no client shows.
    let user_texts: Vec<String> = harness.message_ends("user").iter().map(text_of).collect();
    assert_eq!(user_texts, vec!["build the feature".to_string()]);
    let hidden: Vec<Value> = harness
        .message_ends("custom")
        .into_iter()
        .filter(|message| message["customType"] == "autonomous_continuation")
        .collect();
    assert_eq!(hidden.len(), 1, "hidden continuations: {hidden:?}");
    assert_eq!(hidden[0]["display"], false);
    assert_eq!(
        hidden[0]["details"]["origin"],
        json!({ "kind": "autonomous", "nudge": "continuation" })
    );
    assert!(
        text_of(&hidden[0]).starts_with("[autonomous-continuation]\n\nNo human input is available"),
        "plain continuation: {}",
        text_of(&hidden[0])
    );
    // The model still reads the continuation: it is a durable user row.
    let durable_users = durable_messages(&harness, "user");
    assert!(
        durable_users
            .iter()
            .any(|text| text.starts_with("[autonomous-continuation]")),
        "durable user rows: {durable_users:?}"
    );
    // The in-run ordering, as pi-durable commits it: the `onYield`
    // continuation's user entry lands in the settled answer's own commit
    // (`generation/round.rs` `answer`), so its pair follows the answer's
    // `message_end` and precedes that turn's `turn_end`; the continuation
    // turn's `turn_start` follows with no run boundary between.
    let continuation_index = harness
        .client
        .events
        .iter()
        .position(|event| {
            event.get("type").and_then(Value::as_str) == Some("message_end")
                && event["message"]["customType"] == "autonomous_continuation"
        })
        .expect("the continuation's wire pair");
    let around: Vec<&str> = harness.client.events[continuation_index - 2..=continuation_index + 2]
        .iter()
        .filter_map(|event| event.get("type").and_then(Value::as_str))
        .collect();
    assert_eq!(
        around,
        vec![
            "message_end",
            "message_start",
            "message_end",
            "turn_end",
            "turn_start"
        ],
        "the answer -> the continuation row -> turn_end -> turn_start, events: {:?}",
        harness.client.events
    );
    assert_eq!(
        text_of(&harness.client.events[continuation_index - 2]["message"]),
        "still working",
        "the continuation follows the settled answer"
    );
    // The budget stop writes no row and no stream frame: the durable
    // autonomous_status rows are the command's alone.
    assert!(
        durable_autonomous_rows(&harness, "[autonomous-stop:").is_empty(),
        "no durable stop row"
    );
    assert!(
        harness
            .custom_texts("autonomous_status")
            .iter()
            .all(|text| text.starts_with("[autonomous-status:")),
        "the only autonomous_status rows are the command's, events: {:?}",
        harness.client.events
    );
}

/// `/goal` is removed: typed with a task it notes the removal, then does
/// what `/auto <task>` does — autonomous mode on and the task sent as the
/// user's message, whose answer the model gives first. The run then goes
/// on under its checks until they or its budget stop it (the intent check
/// a run gets when it turns on asks the scripted model too, so the later
/// answers are not pinned here).
#[test]
fn goal_notes_its_removal_then_runs_the_task_as_auto() {
    let mut harness = setup(
        "goal-alias",
        &json!([
            { "text": "step 1" },
            { "text": "step 2" },
            { "text": "step 3" },
            { "text": "step 4" },
        ]),
    );
    // The command answers once its task is submitted; the run goes on.
    harness.prompt("goal", "/goal build the feature");
    harness.client.send_command(
        "idle",
        &json!({ "type": "wait_for_idle", "activeSessionId": harness.session_id }),
    );
    let idle = harness.client.request("idle");
    assert_eq!(idle["success"], true, "never went idle: {idle}");
    harness.client.drain_events(Duration::from_secs(1));

    assert_eq!(
        harness.custom_texts("session_slash_command_result"),
        vec!["/goal is removed: use /auto".to_string()]
    );
    assert_eq!(
        durable_autonomous_rows(&harness, "[autonomous-status: on]").len(),
        1,
        "the run turned on once"
    );
    let user_texts: Vec<String> = harness.message_ends("user").iter().map(text_of).collect();
    assert_eq!(user_texts, ["build the feature"]);
    let assistants: Vec<String> = harness
        .message_ends("assistant")
        .iter()
        .map(text_of)
        .collect();
    assert_eq!(
        assistants.first().map(String::as_str),
        Some("step 1"),
        "events: {:?}",
        harness.client.events
    );
}
