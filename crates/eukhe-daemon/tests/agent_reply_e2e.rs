//! A family agent's answers end to end, against a real supervisor and
//! real scripted session workers.
//!
//! 1. A user's `@name` message (a prompt carrying `replyTo`) returns the
//!    agent's final answer to the user's session as ONE durable
//!    `agent_reply` row: the user's session never runs a turn for it, and
//!    a redelivered reply (a restarted agent re-sending) lands nowhere.
//! 2. A child that reported to its parent through an agent message exits
//!    passively: its settle queues no no-reply notice, so the parent runs
//!    no extra turn restating the report.
//!
//! The kernel Python is this checkout's runtime
//! (`eukhe-core/tests/support/kernel_runtime.rs`).

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_command;
use process::Daemon;

fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Daemon {
    Daemon::spawn_listening(
        supervisor_command(socket, agent_dir)
            // Hermetic agent dir: the ambient environment exports a real
            // agent dir; point every fallback at the test sandbox instead.
            .env("EUKHE_CODING_AGENT_DIR", agent_dir)
            .env_remove("PRIME_API_KEY")
            // A supervisor killed at teardown must not leak its session workers
            // into later test binaries: the worker's supervisor-lost exit (TS
            // `exitIfSupervisorOrphanedForTooLong`) runs on this short window
            // instead of the 5-minute default.
            .env(
                eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
                "15000",
            ),
        socket,
        Duration::from_secs(15),
    )
}

/// JSONL supervisor client (command envelopes, id-matched responses).
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> (Self, Value) {
        let stream = UnixStream::connect(socket).expect("connect supervisor");
        let write_stream = stream.try_clone().expect("clone socket");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer: write_stream,
        };
        let hello = client.read_line();
        (client, hello)
    }

    fn send_command(&mut self, id: &str, command: &Value) {
        let envelope = json!({
            "type": "command",
            "id": id,
            "protocol": { "name": "eukhe.daemon", "version": 7 },
            "command": command,
        });
        let mut line = serde_json::to_string(&envelope).expect("serialize command");
        line.push('\n');
        self.writer.write_all(line.as_bytes()).expect("send");
        self.writer.flush().expect("flush");
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        let deadline = Instant::now() + Duration::from_secs(120);
        self.reader
            .get_mut()
            .set_read_timeout(Some(Duration::from_millis(100)))
            .expect("set timeout");
        loop {
            match self.reader.read_line(&mut line) {
                Ok(0) => panic!("supervisor closed the connection"),
                Ok(_) if line.trim().is_empty() => line.clear(),
                Ok(_) => return serde_json::from_str(line.trim()).expect("parse response line"),
                Err(error) => {
                    assert!(
                        Instant::now() < deadline,
                        "timed out waiting for supervisor line: {error}"
                    );
                }
            }
        }
    }

    fn read_response(&mut self, id: &str) -> Value {
        let deadline = Instant::now() + Duration::from_secs(240);
        loop {
            assert!(Instant::now() < deadline, "no response for id {id}");
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                return line;
            }
        }
    }
}

/// Send one command and answer its successful response data.
fn request(client: &mut Client, id: &str, command: &Value) -> Value {
    client.send_command(id, command);
    let response = client.read_response(id);
    assert_eq!(response["success"], true, "{id} failed: {response}");
    response["data"].clone()
}

/// Create one scripted session through the supervisor; answers its live id.
fn create_session(
    client: &mut Client,
    dir: &Path,
    name: &str,
    script: &Value,
    child_script: Option<&Value>,
) -> String {
    let sessions_dir = dir.join("sessions");
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    let write = |file: &str, script: &Value| {
        let path = dir.join(file);
        std::fs::write(&path, script.to_string()).expect("write script");
        path.to_string_lossy().to_string()
    };
    let mut config = json!({
        "cwd": dir.to_string_lossy(),
        "sessionDir": sessions_dir.to_string_lossy(),
        "script": write(&format!("{name}.json"), script),
    });
    if let Some(child_script) = child_script {
        config["childScript"] = json!(write(&format!("{name}-child.json"), child_script));
    }
    let created = request(
        client,
        &format!("create-{name}"),
        &json!({ "type": "create", "name": name, "config": config }),
    );
    created["activeSessionId"]
        .as_str()
        .expect("active session id")
        .to_string()
}

/// The session's wire messages.
fn messages(client: &mut Client, id: &str, session: &str) -> Vec<Value> {
    request(
        client,
        id,
        &json!({ "type": "get_messages", "activeSessionId": session }),
    )["messages"]
        .as_array()
        .cloned()
        .expect("messages array")
}

/// The text of every assistant message that stopped (one per answered
/// turn), in order.
fn answers(messages: &[Value]) -> Vec<String> {
    messages
        .iter()
        .filter(|message| message["role"] == "assistant" && message["stopReason"] == "stop")
        .map(|message| {
            message["content"]
                .as_array()
                .into_iter()
                .flatten()
                .filter_map(|block| block["text"].as_str())
                .collect::<String>()
        })
        .collect()
}

/// Wait for the session to go idle.
fn wait_idle(client: &mut Client, id: &str, session: &str) {
    request(
        client,
        id,
        &json!({ "type": "wait_for_idle", "activeSessionId": session }),
    );
}

/// A user's `@alpha` message from `root` (the prompt's `replyTo`): alpha's
/// final answer returns to `root` as one `agent_reply` row, `root` runs no
/// turn for it, and a redelivery of the same reply is a no-op.
#[test]
fn a_user_message_reply_returns_once_to_the_users_session() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let socket = dir.path().join("supervisor.sock");
    let _daemon = spawn_supervisor(&socket, &agent_dir);
    let (mut client, hello) = Client::connect(&socket);
    assert_eq!(hello["type"], "daemon_hello");
    // The user's session would answer a turn it must never run.
    let root = create_session(
        &mut client,
        dir.path(),
        "root",
        &json!({ "engine": "faux", "responses": [{ "text": "root must not run" }] }),
        None,
    );
    let alpha = create_session(
        &mut client,
        dir.path(),
        "alpha",
        &json!({ "engine": "faux", "responses": [{ "text": "I reported 42.\nThe rest of it." }] }),
        None,
    );
    request(
        &mut client,
        "ask",
        &json!({
            "type": "prompt",
            "activeSessionId": alpha,
            "message": "what number did you report?",
            "replyTo": root,
        }),
    );
    wait_idle(&mut client, "alpha-idle", &alpha);

    let deadline = Instant::now() + Duration::from_secs(20);
    let rows = loop {
        let rows = messages(&mut client, "root-messages", &root);
        if !rows.is_empty() {
            break rows;
        }
        assert!(
            Instant::now() < deadline,
            "the reply never reached the user's session"
        );
        std::thread::sleep(Duration::from_millis(100));
    };
    let reply_id = rows[0]["details"]["id"]
        .as_str()
        .expect("reply id")
        .to_string();
    let expected = vec![json!({
        "role": "custom",
        "customType": "agent_reply",
        "content": [{ "type": "text", "text": "[agent-reply from alpha]\n\nI reported 42.\nThe rest of it." }],
        "display": true,
        "details": { "id": reply_id, "from": "alpha", "message": "I reported 42.\nThe rest of it." },
        "timestamp": rows[0]["timestamp"],
    })];
    assert_eq!(rows, expected, "one reply row and no root turn");

    // A redelivery (a restarted agent re-sending its latest reply) lands
    // nowhere: the row is keyed by the reply id.
    request(
        &mut client,
        "redeliver",
        &json!({
            "type": "agent_reply",
            "activeSessionId": root,
            "from": "alpha",
            "text": "I reported 42.\nThe rest of it.",
            "replyId": reply_id,
        }),
    );
    wait_idle(&mut client, "root-idle", &root);
    assert_eq!(messages(&mut client, "root-again", &root), expected);
    // Alpha's own transcript: its owed-reply bookkeeping row (hidden)
    // stands before the user's question; the answer follows.
    let alpha_rows = messages(&mut client, "alpha-messages", &alpha);
    assert_eq!(
        alpha_rows
            .iter()
            .map(|message| (
                message["role"].as_str().unwrap_or_default(),
                message["customType"].as_str(),
                message["display"].as_bool(),
            ))
            .collect::<Vec<_>>(),
        vec![
            ("custom", Some("agent_reply_owed"), Some(false)),
            ("user", None, None),
            ("custom", Some("harness_digest"), Some(false)),
            ("assistant", None, None),
        ]
    );
}

/// The kernel cell a child runs to report to its parent.
fn report_cell(receipt: &Path) -> String {
    format!(
        "from rlm import host_request\nimport json, traceback\ntry:\n    receipt = await host_request(\"agent_message.send\", {{\"message\": \"I found 42\", \"receiver_role\": \"parent\"}})\n    open({receipt:?}, \"w\").write(json.dumps(receipt))\nexcept Exception:\n    open({receipt:?}, \"w\").write(traceback.format_exc())\n    raise",
        receipt = receipt.display().to_string(),
    )
}

/// The kernel cell of the parent's spawn turn.
fn spawn_cell() -> &'static str {
    "handle = await rlm.spawn(\"find the number\", name=\"kid\", why=\"isolate\")\nprint(handle.rlm_child_id)"
}

/// A child that reported to its parent (an agent message) exits passively:
/// the parent answers the report once and never runs the no-reply notice
/// turn its settle would otherwise queue.
#[test]
fn a_child_that_reported_exits_without_waking_its_parent() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let socket = dir.path().join("supervisor.sock");
    let receipt = dir.path().join("report.json");
    let _daemon = spawn_supervisor(&socket, &agent_dir);
    let (mut client, hello) = Client::connect(&socket);
    assert_eq!(hello["type"], "daemon_hello");
    // The report waits out the parent's spawn turn, so it answers in a
    // turn of its own; a notice turn would consume "notice seen".
    let parent = create_session(
        &mut client,
        dir.path(),
        "parent",
        &json!({
            "engine": "faux",
            "responses": [
                { "content": [
                    { "type": "toolCall", "name": "ipython", "arguments": { "code": spawn_cell() } },
                ] },
                { "text": "spawn turn done" },
                { "text": "report seen" },
                { "text": "notice seen" },
            ],
        }),
        Some(&json!({
            "responses": [
                { "content": [
                    { "type": "toolCall", "name": "ipython",
                      "arguments": { "code": report_cell(&receipt) } },
                ], "delayMs": 1_500 },
                { "text": "kid done" },
            ],
        })),
    );
    request(
        &mut client,
        "spawn",
        &json!({ "type": "prompt", "activeSessionId": parent, "message": "spawn the kid" }),
    );
    request(
        &mut client,
        "quiet",
        &json!({
            "type": "wait_for_idle",
            "activeSessionId": parent,
            "waitForRlmQuiescence": true,
        }),
    );
    let report = std::fs::read_to_string(&receipt).expect("the child's report receipt");
    let report: Value = serde_json::from_str(&report)
        .unwrap_or_else(|_| panic!("the child's report failed: {report}"));
    assert_eq!(report["receiverRole"], "parent", "{report}");
    let children = request(
        &mut client,
        "children",
        &json!({ "type": "get_rlm_children", "activeSessionId": parent }),
    );
    assert_eq!(
        children["children"]
            .as_array()
            .expect("children")
            .iter()
            .map(|row| (row["sessionName"].clone(), row["status"].clone()))
            .collect::<Vec<_>>(),
        vec![(json!("kid"), json!("done"))]
    );
    let rows = messages(&mut client, "parent-messages", &parent);
    assert_eq!(
        answers(&rows),
        vec!["spawn turn done".to_string(), "report seen".to_string()],
        "one turn for the report, none for a notice: {rows:?}"
    );
    assert_eq!(
        rows.iter()
            .filter_map(|message| message["customType"].as_str())
            .collect::<Vec<_>>(),
        vec!["harness_digest", "agent_message"],
        "the report is the only delivered row (no notice): {rows:?}"
    );
}
