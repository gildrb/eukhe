//! A daemon under an agent dir too deep for an endpoint name (107 bytes on
//! Linux, 103 on macOS): its socket, its workers' sockets and the chat lock
//! bind at short endpoints their paths link to, and a parent spawns a help
//! leaf and splits into two children that all start and settle.
//!
//! One real supervisor whose socket is the default `<agent dir>/run/
//! daemon.sock`, a real parent worker whose faux model drives the kernel
//! `rlm.*` surface, and real scripted child workers.

use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_command;
use process::Daemon;

/// One test's sandbox: a root whose agent dir, socket and workspace sit
/// past every endpoint name limit.
struct Lane {
    _dir: tempfile::TempDir,
    root: PathBuf,
}

impl Lane {
    fn new() -> Self {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let root = dir.path().join("d".repeat(60)).join("e".repeat(60));
        let lane = Self { _dir: dir, root };
        for dir in [lane.agent_dir(), lane.receipts(), lane.work()] {
            std::fs::create_dir_all(dir).expect("lane dir");
        }
        for file in ["left.txt", "right.txt"] {
            std::fs::write(lane.work().join(file), "").expect("scope file");
        }
        assert!(!eukhe_types::platform::transport::is_addressable(
            &lane.socket()
        ));
        lane
    }

    fn agent_dir(&self) -> PathBuf {
        self.root.join("agent")
    }

    /// The default supervisor socket of the agent dir.
    fn socket(&self) -> PathBuf {
        self.agent_dir().join("run").join("daemon.sock")
    }

    fn receipts(&self) -> PathBuf {
        self.root.join("receipts")
    }

    fn work(&self) -> PathBuf {
        self.root.join("work")
    }

    fn daemon_log(&self) -> PathBuf {
        self.root.join("daemon.log")
    }

    fn supervisor(&self) -> Daemon {
        let log = std::fs::File::create(self.daemon_log()).expect("daemon log");
        Daemon::spawn(
            supervisor_command(&self.socket(), &self.agent_dir())
                .env("EUKHE_CODING_AGENT_DIR", self.agent_dir())
                .env(
                    "EUKHE_PACKAGE_DIR",
                    Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."),
                )
                .stderr(Stdio::from(log)),
            &self.socket(),
        )
    }

    /// A faux script: the model's responses, one per model call.
    fn script(&self, name: &str, responses: &Value) -> PathBuf {
        let path = self.root.join(format!("{name}.json"));
        std::fs::write(
            &path,
            json!({ "engine": "faux", "responses": responses }).to_string(),
        )
        .expect("write script");
        path
    }

    /// A kernel cell running `body` with `record(value)` writing the
    /// receipt `name`; a failure writes `<name>.error` and re-raises.
    fn cell(&self, name: &str, body: &str) -> String {
        let receipt = self.receipts().join(format!("{name}.json"));
        let error = self.receipts().join(format!("{name}.error"));
        let body = body
            .lines()
            .map(|line| format!("    {line}"))
            .collect::<Vec<_>>()
            .join("\n");
        format!(
            "import asyncio, json, os, traceback\ndef record(value):\n    open({receipt:?} + \".tmp\", \"w\").write(json.dumps(value, default=str))\n    os.replace({receipt:?} + \".tmp\", {receipt:?})\ntry:\n{body}\nexcept BaseException:\n    open({error:?}, \"w\").write(traceback.format_exc())\n    raise",
            receipt = receipt.display().to_string(),
            error = error.display().to_string(),
        )
    }

    /// The recorded receipt `name`, waiting for the cell that writes it;
    /// a failed cell's traceback fails the test at once.
    fn receipt(&self, name: &str) -> Value {
        let receipt = self.receipts().join(format!("{name}.json"));
        let error = self.receipts().join(format!("{name}.error"));
        let deadline = Instant::now() + Duration::from_mins(3);
        loop {
            if let Ok(traceback) = std::fs::read_to_string(&error) {
                panic!("cell {name} failed: {traceback}");
            }
            if let Ok(text) = std::fs::read_to_string(&receipt) {
                return serde_json::from_str(&text).expect("receipt json");
            }
            assert!(Instant::now() < deadline, "timed out waiting for {name}");
            std::thread::sleep(Duration::from_millis(100));
        }
    }
}

/// Wait until the supervisor accepts connections; read its hello.
fn connect(socket: &Path) -> Client {
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        if let Ok(stream) = eukhe_types::platform::transport::connect_std(socket) {
            let writer = stream.try_clone().expect("clone socket");
            let mut client = Client {
                reader: BufReader::new(stream),
                writer,
            };
            let hello = client.read_line();
            assert_eq!(hello["type"], "daemon_hello", "{hello}");
            return client;
        }
        assert!(Instant::now() < deadline, "supervisor socket never came up");
        std::thread::sleep(Duration::from_millis(20));
    }
}

/// JSONL supervisor client (command envelopes, id-matched responses).
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
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

    /// One command's successful response data.
    fn request(&mut self, id: &str, command: &Value) -> Value {
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
        let deadline = Instant::now() + Duration::from_mins(4);
        loop {
            assert!(Instant::now() < deadline, "no response for id {id}");
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                assert_eq!(line["success"], true, "{command} failed: {line}");
                return line["data"].clone();
            }
        }
    }
}

fn tool_call(code: &str) -> Value {
    json!({ "content": [
        { "type": "toolCall", "name": "python", "arguments": { "code": code } },
    ] })
}

/// The body of the tree cell: a help leaf, then a split into two children;
/// wait until all three settle and record how each ended.
const TREE: &str = "helper = await rlm.spawn(\"look around\", name=\"helper\")\nleft, right = await rlm.split({\"scope\": [\"left.txt\"], \"task\": \"do the left half\", \"name\": \"left\"}, {\"scope\": [\"right.txt\"], \"task\": \"do the right half\", \"name\": \"right\"})\nwhile True:\n    results = await rlm.collect([helper, left, right], timeout_ms=60000)\n    if all(r.settled for r in results):\n        break\n    await asyncio.sleep(0.1)\nrecord(sorted([r.session_name, r.status, r.answer_preview] for r in results))";

/// Spawn and split under an agent dir past every endpoint name limit: the
/// supervisor, every child worker and the chat lock serve through links
/// to short endpoints, and every child starts and settles.
#[test]
fn spawn_and_split_under_an_agent_dir_past_the_name_limit() {
    let lane = Lane::new();
    let child_script = lane.script("child", &json!([{ "text": "child done" }]));
    let parent_script = lane.script(
        "parent",
        &json!([
            tool_call(&lane.cell("tree", TREE)),
            { "text": "tree turn done" },
            { "text": "noted" },
            { "text": "noted" },
            { "text": "noted" },
        ]),
    );
    let _daemon = lane.supervisor();
    let mut client = connect(&lane.socket());
    let created = client.request(
        "create",
        &json!({
            "type": "create",
            "name": "parent",
            "config": {
                "cwd": lane.work().to_string_lossy(),
                "script": parent_script.to_string_lossy(),
                "childScript": child_script.to_string_lossy(),
            },
        }),
    );
    let parent = created["activeSessionId"]
        .as_str()
        .expect("parent active session id")
        .to_owned();
    client.request(
        "prompt",
        &json!({ "type": "prompt", "activeSessionId": parent, "message": "build the tree" }),
    );

    assert_eq!(
        lane.receipt("tree"),
        json!([
            ["helper", "done", "child done"],
            ["left", "done", "child done"],
            ["right", "done", "child done"],
        ]),
    );
    // The supervisor's socket and its workers' sockets beside it are links
    // to short endpoints; so is the chat lock.
    let run = lane.socket().parent().expect("run dir").to_path_buf();
    assert!(std::fs::read_link(lane.socket()).is_ok());
    let worker_links = std::fs::read_dir(&run)
        .expect("run dir")
        .map(|entry| entry.expect("run dir entry").path())
        .filter(|path| {
            path.file_name()
                .is_some_and(|name| name.to_string_lossy().starts_with("worker-"))
                && std::fs::read_link(path).is_ok()
        })
        .count();
    assert!(worker_links >= 1, "the parent's worker socket is a link");
    assert!(std::fs::read_link(lane.agent_dir().join("chat").join("lock")).is_ok());
}
