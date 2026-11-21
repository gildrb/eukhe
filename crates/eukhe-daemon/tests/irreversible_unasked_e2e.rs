//! Every step runs unasked, end to end (spec I2, I3): a real supervisor
//! and worker, the scripted faux model calling `bash`. An irreversible
//! step (a write into a `.git` dir) runs at once whichever client is
//! attached (a person's, the phone gateway's alone) and with none; a
//! write to eukhe's own config is refused for each of them, and so is a
//! write to a file a check under acceptance protects. A refused step and
//! the steps after it do not run, and the model reads the path and why.

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

/// A write, an irreversible step (a `.git` dir and a write into it), a
/// write of eukhe's own settings, a write.
const SCRIPT: &str = "echo one > one.txt\nmkdir .git\necho two > .git/note\necho three > agent/settings.json\necho four > never.txt";

/// A write of the file the check protects, then a write.
const PROTECTED_SCRIPT: &str = "echo changed > golden.txt\necho after > never.txt";

/// JSONL supervisor client.
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> Self {
        let stream =
            eukhe_types::platform::transport::connect_std(socket).expect("connect supervisor");
        let writer = stream.try_clone().expect("clone socket");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
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

/// A daemon over `dir` (the session's cwd, its agent dir `dir/agent`)
/// whose faux model calls `bash` with `script`, one connected client, and
/// the session it created.
fn open(dir: &Path, script: &str) -> (Daemon, Client, String) {
    let agent_dir = dir.join("agent");
    let sessions_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    let faux = dir.join("faux.json");
    std::fs::write(
        &faux,
        json!({
            "engine": "faux",
            "responses": [
                { "content": [{ "type": "toolCall", "name": "bash", "arguments": { "script": script } }] },
                { "text": "done" },
            ],
        })
        .to_string(),
    )
    .expect("write faux script");
    let socket = dir.join("shell.sock");
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
    (daemon, client, session)
}

/// Prompt the session, wait until it is idle, and answer the text of its
/// one tool result.
fn run(client: &mut Client, session: &str) -> String {
    client.command(
        "p1",
        &json!({ "type": "prompt", "activeSessionId": session, "message": "write the files" }),
    );
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

/// The script under one client kind (`None`: no client attached): its
/// tool result and what each of its writes left.
fn script_under(kind: Option<&str>) -> (String, [Option<String>; 4]) {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let (_daemon, mut client, session) = open(dir.path(), SCRIPT);
    let settings = dir.path().join("agent/settings.json");
    let settings_before = std::fs::read_to_string(&settings).ok();
    if let Some(kind) = kind {
        client.command(
            "a1",
            &json!({
                "type": "attach",
                "activeSessionId": session,
                "clientId": format!("{kind}-client"),
                "clientKind": kind,
            }),
        );
    }
    let result = run(&mut client, &session);
    let own = std::fs::canonicalize(dir.path().join("agent"))
        .expect("the agent dir")
        .join("settings.json");
    let read = |name: &str| std::fs::read_to_string(dir.path().join(name)).ok();
    let settings_after = std::fs::read_to_string(&settings).ok();
    assert_eq!(
        settings_after, settings_before,
        "the own write ran ({kind:?})"
    );
    (
        result.replace(&own.display().to_string(), "<agent>/settings.json"),
        [
            read("one.txt"),
            read(".git/note"),
            read("never.txt"),
            kind.map(str::to_owned),
        ],
    )
}

/// Regression (G5): a step that was not within the user's auto set
/// waited for a person's yes, and a session driven only from the phone
/// waited for an answer that never came. Now the irreversible step runs
/// unasked for every client kind and with none; the own write is refused
/// for each.
#[test]
fn an_irreversible_step_runs_unasked_and_an_own_write_is_refused_for_every_client() {
    let result = "$ echo one >one.txt\n$ mkdir .git\n$ echo two >.git/note\n[stopped at step 3 (read+write+protected): `echo three >agent/settings.json` and the steps after it did not run: <agent>/settings.json is part of eukhe's own config and credentials; no agent may write it.]\n";
    let got: Vec<_> = [None, Some("interactive"), Some("gateway"), Some("watch")]
        .into_iter()
        .map(script_under)
        .collect();
    let expected: Vec<_> = [None, Some("interactive"), Some("gateway"), Some("watch")]
        .into_iter()
        .map(|kind| {
            (
                result.to_owned(),
                [
                    Some("one\n".to_owned()),
                    Some("two\n".to_owned()),
                    None,
                    kind.map(str::to_owned),
                ],
            )
        })
        .collect();
    assert_eq!(got, expected);
}

/// A file a check under acceptance protects (`/accept … --protect`) is
/// own while the check is set: its write is refused, and the step after
/// it does not run.
#[test]
fn a_write_to_a_file_a_check_protects_is_refused() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    std::fs::write(dir.path().join("golden.txt"), "gold\n").expect("golden file");
    let (_daemon, mut client, session) = open(dir.path(), PROTECTED_SCRIPT);
    client.command(
        "s1",
        &json!({
            "type": "set_acceptance",
            "activeSessionId": session,
            "checks": [{ "kind": "command", "command": "true", "protect": ["golden.txt"] }],
            "intent": false,
        }),
    );
    let result = run(&mut client, &session);
    let golden = std::fs::canonicalize(dir.path())
        .expect("the work dir")
        .join("golden.txt");
    let read = |name: &str| std::fs::read_to_string(dir.path().join(name)).ok();
    assert_eq!(
        (result, read("golden.txt"), read("never.txt")),
        (
            format!(
                "[stopped at step 0 (read+write): `echo changed >golden.txt` and the steps after it did not run: {} is part of the protected files of a check under acceptance; no agent may write it.]\n",
                golden.display()
            ),
            Some("gold\n".to_owned()),
            None,
        )
    );
}
