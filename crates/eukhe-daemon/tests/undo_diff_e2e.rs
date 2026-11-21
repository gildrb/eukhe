//! `/undo` and `/diff` end to end: a real supervisor and worker, the
//! scripted faux model editing files of the workspace with `bash` over two
//! prompts of two model rounds each (a prompt is one snapshot, whatever
//! its rounds), each prompt also writing a file outside the workspace (an
//! irreversible effect the ledger records). `get_turn_diff` shows the
//! second prompt's change (and, with `all`, both); two `undo_turn` restore
//! the workspace as it was before the first prompt, each naming the
//! irreversible effect of the prompt it undid (printed under
//! `Not undone (irreversible):`) and leaving the outside
//! files; a third is refused with `nothing_to_undo`.

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

    /// Send `command` and read until its response, which it answers.
    fn answer(&mut self, id: &str, command: &Value) -> Value {
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
                return line;
            }
        }
    }

    /// Send `command`; its response's data, which must be a success.
    fn data(&mut self, id: &str, command: &Value) -> Value {
        let response = self.answer(id, command);
        assert_eq!(response["success"], true, "{id} failed: {response}");
        response["data"].clone()
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

fn bash(script: &str) -> Value {
    json!({ "content": [{ "type": "toolCall", "name": "bash", "arguments": { "script": script } }] })
}

/// One prompt, run to its end.
fn turn(client: &mut Client, session: &str, at: usize) {
    client.data(
        &format!("p{at}"),
        &json!({ "type": "prompt", "activeSessionId": session, "message": "edit" }),
    );
    client.data(
        &format!("w{at}"),
        &json!({ "type": "wait_for_idle", "activeSessionId": session }),
    );
}

fn read(path: &Path) -> Option<String> {
    std::fs::read_to_string(path).ok()
}

#[test]
// One scenario end to end (two prompts, the ledger, two diffs, three
// undos) checked by one whole-state assertion.
#[allow(clippy::too_many_lines)]
fn two_turns_diff_and_undo_back_to_the_start() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let sessions_dir = agent_dir.join("sessions");
    let workspace = dir.path().join("ws");
    // The OS temp dir is scratch (its writes count as inside), so the
    // outside files go under the target's temp dir.
    let outside_dir = tempfile::TempDir::new_in(env!("CARGO_TARGET_TMPDIR")).expect("outside dir");
    let outside = outside_dir.path();
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    std::fs::create_dir_all(&workspace).expect("workspace");
    std::fs::write(workspace.join("a.txt"), "one\n").expect("seed");
    let (out1, out2) = (outside.join("o1.txt"), outside.join("o2.txt"));
    let faux = dir.path().join("faux.json");
    std::fs::write(
        &faux,
        json!({
            "engine": "faux",
            "responses": [
                bash(&format!("echo two > a.txt; echo x > {}", out1.display())),
                { "text": "changed a" },
                bash(&format!("echo new > b.txt; echo y > {}", out2.display())),
                { "text": "added b" },
            ],
        })
        .to_string(),
    )
    .expect("write faux script");
    let socket = dir.path().join("undo.sock");
    let _daemon = Daemon::spawn_listening(
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
    let created = client.data(
        "c1",
        &json!({
            "type": "create",
            "config": {
                "cwd": workspace.to_string_lossy(),
                "sessionDir": sessions_dir.to_string_lossy(),
                "script": faux.to_string_lossy(),
            },
        }),
    );
    let session = created["activeSessionId"]
        .as_str()
        .or_else(|| created["id"].as_str())
        .expect("active session id")
        .to_owned();
    turn(&mut client, &session, 1);
    turn(&mut client, &session, 2);
    let after = (
        read(&workspace.join("a.txt")),
        read(&workspace.join("b.txt")),
    );
    let ledger = client.data(
        "l1",
        &json!({ "type": "get_ran_effects", "activeSessionId": session }),
    )["effects"]
        .clone();
    let diff = client.data(
        "d1",
        &json!({ "type": "get_turn_diff", "activeSessionId": session }),
    );
    let all = client.data(
        "d2",
        &json!({ "type": "get_turn_diff", "activeSessionId": session, "scope": "all" }),
    );
    let first = client.data(
        "u1",
        &json!({ "type": "undo_turn", "activeSessionId": session }),
    );
    // What every surface prints of it: the second prompt's outside write
    // under `Not undone (irreversible):`.
    let printed = eukhe_types::undo::undo_text(
        &serde_json::from_value(first.clone()).expect("an undo_turn reply"),
    );
    let middle = (
        read(&workspace.join("a.txt")),
        read(&workspace.join("b.txt")),
    );
    let second = client.data(
        "u2",
        &json!({ "type": "undo_turn", "activeSessionId": session }),
    );
    let third = client.answer(
        "u3",
        &json!({ "type": "undo_turn", "activeSessionId": session }),
    );
    // The ledger: one effect per prompt, the step writing outside, in runs
    // 1 and 2.
    let entry = |at: usize| ledger[at].clone();
    let names = |at: usize, path: &Path| {
        (
            entry(at)["run"].clone(),
            entry(at)["classes"].clone(),
            entry(at)["command"]
                .as_str()
                .is_some_and(|command| command.contains(&*path.to_string_lossy())),
        )
    };
    assert_eq!(
        (
            ledger.as_array().map(Vec::len),
            names(0, &out1),
            names(1, &out2)
        ),
        (
            Some(2),
            (json!(1), json!(["read", "write", "outside"]), true),
            (json!(2), json!(["read", "write", "outside"]), true)
        ),
        "{ledger}"
    );
    assert_eq!(
        (
            after,
            diff["paths"].clone(),
            diff["diff"]
                .as_str()
                .is_some_and(|text| text.contains("+new")),
            all["paths"].clone(),
            first,
            printed
                .split_once("Not undone (irreversible):\n")
                .map(|(_, effects)| effects.to_owned()),
            middle,
            second,
            (
                read(&workspace.join("a.txt")),
                read(&workspace.join("b.txt"))
            ),
            (third["success"].clone(), third["errorInfo"]["code"].clone()),
            (read(&out1), read(&out2)),
        ),
        (
            (Some("two\n".to_owned()), Some("new\n".to_owned())),
            json!(["b.txt"]),
            true,
            json!(["a.txt", "b.txt"]),
            json!({ "restored": ["b.txt"], "turn": 2, "left": 1, "notUndone": [entry(1)] }),
            Some(format!(
                "- e2 {} (read+write+outside)\n",
                entry(1)["command"].as_str().unwrap_or_default()
            )),
            (Some("two\n".to_owned()), None),
            json!({ "restored": ["a.txt"], "turn": 1, "left": 0, "notUndone": [entry(0)] }),
            (Some("one\n".to_owned()), None),
            (json!(false), json!("nothing_to_undo")),
            (Some("x\n".to_owned()), Some("y\n".to_owned())),
        )
    );
}
