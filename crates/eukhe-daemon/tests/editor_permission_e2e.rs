//! The editor's say on an irreversible effect, end to end (spec I12): a
//! real supervisor and worker, the scripted faux model calling `bash`,
//! and a fake editor: a client that attached with the `editor_permission`
//! capability, as an ACP attach does. Each irreversible step (a `.git`
//! dir, a write into it) sends it one `editor_permission` frame before it
//! runs, and its `answer_editor_permission` decides: allow runs the step,
//! reject stops the script there (the model reads that the editor refused
//! it), `unsupported` runs it and nothing is asked again in the session.
//! An editor that detaches unanswered lets the step run. A reversible
//! step asks nothing.

use std::collections::VecDeque;
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

/// A write, then three irreversible steps: a `.git` dir, a write into it,
/// another write into it.
const SCRIPT: &str = "echo one > one.txt\nmkdir .git\necho two > .git/two\necho three > .git/three";

/// JSONL supervisor client that keeps the `editor_permission` frames it
/// reads while it waits for a response.
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
    questions: VecDeque<Value>,
}

impl Client {
    fn connect(socket: &Path) -> Self {
        let stream =
            eukhe_types::platform::transport::connect_std(socket).expect("connect supervisor");
        let writer = stream.try_clone().expect("clone socket");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
            questions: VecDeque::new(),
        };
        assert_eq!(client.read_line()["type"], "daemon_hello");
        client
    }

    /// Send `command` and read until its response.
    fn command(&mut self, id: &str, command: &Value) -> Value {
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
        let deadline = Instant::now() + Duration::from_mins(4);
        loop {
            assert!(Instant::now() < deadline, "no response for id {id}");
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                assert_eq!(line["success"], true, "{id} failed: {line}");
                return line;
            }
            self.keep(line);
        }
    }

    /// The next `editor_permission` frame.
    fn question(&mut self) -> Value {
        let deadline = Instant::now() + Duration::from_mins(2);
        loop {
            if let Some(frame) = self.questions.pop_front() {
                return frame;
            }
            assert!(Instant::now() < deadline, "no editor_permission frame came");
            let line = self.read_line();
            self.keep(line);
        }
    }

    fn keep(&mut self, line: Value) {
        if line["type"] == "editor_permission" {
            self.questions.push_back(line);
        }
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        let deadline = Instant::now() + Duration::from_mins(2);
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
}

/// A daemon over `dir` whose faux model calls `bash` with [`SCRIPT`], one
/// connected client attached to the session it created as an editor, and
/// the session id.
fn open_as_editor(dir: &Path) -> (Daemon, Client, String) {
    let agent_dir = dir.join("agent");
    let sessions_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    let faux = dir.join("faux.json");
    std::fs::write(
        &faux,
        json!({
            "engine": "faux",
            "responses": [
                { "content": [{ "type": "toolCall", "name": "bash", "arguments": { "script": SCRIPT } }] },
                { "text": "done" },
            ],
        })
        .to_string(),
    )
    .expect("write faux script");
    let socket = dir.join("editor.sock");
    let daemon = Daemon::spawn_listening(
        supervisor_command(&socket, &agent_dir)
            .env("EUKHE_CODING_AGENT_DIR", &agent_dir)
            .env(
                eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
                "15000",
            ),
        &socket,
        Duration::from_secs(15),
    );
    let mut client = Client::connect(&socket);
    let created = client.command(
        "c1",
        &json!({
            "type": "create",
            "config": {
                "cwd": dir.to_string_lossy(),
                "sessionDir": sessions_dir.to_string_lossy(),
                "script": faux.to_string_lossy(),
            },
        }),
    );
    let session = created["data"]["activeSessionId"]
        .as_str()
        .or_else(|| created["data"]["id"].as_str())
        .expect("active session id")
        .to_owned();
    let attached = client.command(
        "a1",
        &json!({
            "type": "attach",
            "activeSessionId": session,
            "clientId": "editor",
            "capabilities": ["attach_snapshot", "event_sequence", "editor_permission"],
        }),
    );
    assert_eq!(
        attached["data"]["client"]["capabilities"],
        json!(["attach_snapshot", "event_sequence", "editor_permission"])
    );
    client.command(
        "p1",
        &json!({ "type": "prompt", "activeSessionId": session, "message": "write the files" }),
    );
    (daemon, client, session)
}

/// Answer the next question with `verdict`: the question's command and
/// classes.
fn answer(client: &mut Client, session: &str, at: usize, verdict: &str) -> (Value, Value) {
    let frame = client.question();
    assert_eq!(frame["activeSessionId"], json!(session));
    let request = frame["request"].clone();
    client.command(
        &format!("v{at}"),
        &json!({
            "type": "answer_editor_permission",
            "activeSessionId": session,
            "requestId": request["requestId"],
            "verdict": verdict,
        }),
    );
    (request["command"].clone(), request["classes"].clone())
}

/// Wait until the session is idle and answer the text of its one tool
/// result.
fn tool_result(client: &mut Client, session: &str) -> String {
    client.command(
        "w1",
        &json!({ "type": "wait_for_idle", "activeSessionId": session }),
    );
    let messages = client.command(
        "m1",
        &json!({ "type": "get_messages", "activeSessionId": session }),
    );
    let results: Vec<String> = messages["data"]["messages"]
        .as_array()
        .expect("messages")
        .iter()
        .filter(|message| message["role"] == "toolResult")
        .map(|message| match &message["content"] {
            Value::String(text) => text.clone(),
            Value::Array(blocks) => blocks
                .iter()
                .filter_map(|block| block["text"].as_str())
                .collect::<Vec<_>>()
                .join("\n"),
            other => other.to_string(),
        })
        .collect();
    assert_eq!(results.len(), 1, "{results:#?}");
    results[0].clone()
}

fn read(dir: &Path, name: &str) -> Option<String> {
    std::fs::read_to_string(dir.join(name)).ok()
}

/// The editor allows the first irreversible step and rejects the second:
/// the script stops there, and the model reads that the editor refused it.
#[test]
fn the_editor_allows_one_irreversible_step_and_rejects_the_next() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let (_daemon, mut client, session) = open_as_editor(dir.path());
    let asked = vec![
        answer(&mut client, &session, 0, "allow"),
        answer(&mut client, &session, 1, "reject"),
    ];
    let result = tool_result(&mut client, &session);
    assert_eq!(
        (
            asked,
            result,
            read(dir.path(), "one.txt"),
            dir.path().join(".git").is_dir(),
            read(dir.path(), ".git/two"),
            read(dir.path(), ".git/three"),
        ),
        (
            vec![
                (json!("mkdir .git"), json!(["write", "protected"])),
                (json!("echo two >.git/two"), json!(["read", "write", "protected"])),
            ],
            "$ echo one >one.txt\n$ mkdir .git\n[stopped at step 2 (read+write+protected): `echo two >.git/two` and the steps after it did not run: the editor refused it.]\n"
                .to_owned(),
            Some("one\n".to_owned()),
            true,
            None,
            None,
        )
    );
}

/// An editor without the permission method answers `unsupported`: the
/// step runs, and nothing is asked again in the session.
#[test]
fn an_unsupported_editor_is_asked_once() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let (_daemon, mut client, session) = open_as_editor(dir.path());
    let asked = answer(&mut client, &session, 0, "unsupported");
    let result = tool_result(&mut client, &session);
    assert_eq!(
        (
            asked,
            client.questions.len(),
            result,
            read(dir.path(), ".git/two"),
            read(dir.path(), ".git/three"),
        ),
        (
            (json!("mkdir .git"), json!(["write", "protected"])),
            0,
            "$ echo one >one.txt\n$ mkdir .git\n$ echo two >.git/two\n$ echo three >.git/three\n"
                .to_owned(),
            Some("two\n".to_owned()),
            Some("three\n".to_owned()),
        )
    );
}

/// The editor detaches with a question open: no editor is left, so the
/// step runs, and so does every later one, unasked.
#[test]
fn an_editor_that_detaches_unanswered_lets_the_step_run() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let (_daemon, mut client, session) = open_as_editor(dir.path());
    let frame = client.question();
    client.command(
        "d1",
        &json!({ "type": "detach", "activeSessionId": session, "clientId": "editor" }),
    );
    let result = tool_result(&mut client, &session);
    assert_eq!(
        (
            frame["request"]["command"].clone(),
            result,
            read(dir.path(), ".git/two"),
            read(dir.path(), ".git/three"),
        ),
        (
            json!("mkdir .git"),
            "$ echo one >one.txt\n$ mkdir .git\n$ echo two >.git/two\n$ echo three >.git/three\n"
                .to_owned(),
            Some("two\n".to_owned()),
            Some("three\n".to_owned()),
        )
    );
}
