//! Copy-on-write subagent workspaces (S3) e2e through the product surfaces.
//!
//! One real supervisor, a real parent worker whose faux model spawns an
//! `isolated` child through the kernel `rlm.spawn`, and a real scripted
//! child worker. The parent's workspace holds `a.txt`, `b.txt` and `c.txt`;
//! after the spawn the parent edits `b.txt` and `c.txt`, the child (in its
//! own copy) edits `a.txt` and `c.txt`. At the child's end its changes come
//! back into the parent's workspace: `a.txt` is taken, `b.txt` keeps the
//! parent's edit, and `c.txt` is a conflict that keeps the parent's content
//! while the child's version stays under the workspace's `conflicts/`.
//!
//! The kernel Python is this checkout's runtime
//! (`eukhe-core/tests/support/kernel_runtime.rs`).

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

fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Daemon {
    let log = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(socket.with_extension("daemon.log"))
        .expect("daemon log");
    Daemon::spawn(
        supervisor_command(socket, agent_dir)
            .env("EUKHE_CODING_AGENT_DIR", agent_dir)
            // The kernel's bundled skills: a binary built outside the
            // checkout (`CARGO_TARGET_DIR`) finds them through the package
            // dir.
            .env(
                "EUKHE_PACKAGE_DIR",
                Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."),
            )
            .env_remove("PRIME_API_KEY")
            .stderr(Stdio::from(log)),
        socket,
    )
}

/// Wait until the supervisor accepts connections.
fn connect(socket: &Path) -> Client {
    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        if let Ok(stream) = UnixStream::connect(socket) {
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

/// One test's sandbox: agent dir, socket, receipts, scripts, and the
/// parent's workspace (apart from them, so the child's copy holds only
/// the workspace files).
struct Lane {
    dir: tempfile::TempDir,
}

impl Lane {
    fn new() -> Self {
        let lane = Self {
            dir: tempfile::TempDir::new().expect("temp dir"),
        };
        for dir in [
            lane.agent_dir(),
            lane.receipts(),
            lane.sessions_dir(),
            lane.work(),
        ] {
            std::fs::create_dir_all(dir).expect("lane dir");
        }
        lane
    }

    fn path(&self) -> &Path {
        self.dir.path()
    }

    fn agent_dir(&self) -> PathBuf {
        self.path().join("agent")
    }

    fn sessions_dir(&self) -> PathBuf {
        self.path().join("sessions")
    }

    fn socket(&self) -> PathBuf {
        self.path().join("supervisor.sock")
    }

    fn receipts(&self) -> PathBuf {
        self.path().join("receipts")
    }

    /// The parent's workspace.
    fn work(&self) -> PathBuf {
        self.path().join("work")
    }

    /// A faux script: the model's responses, one per model call.
    fn script(&self, name: &str, responses: &Value) -> PathBuf {
        let path = self.path().join(format!("{name}.json"));
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
        let deadline = Instant::now() + Duration::from_mins(2);
        loop {
            if let Ok(traceback) = std::fs::read_to_string(&error) {
                panic!("cell {name} failed: {traceback}");
            }
            if let Ok(text) = std::fs::read_to_string(&receipt) {
                return serde_json::from_str(&text).expect("receipt json");
            }
            assert!(
                Instant::now() < deadline,
                "timed out waiting for receipt {name}"
            );
            std::thread::sleep(Duration::from_millis(100));
        }
    }
}

fn tool_call(code: &str) -> Value {
    json!({ "content": [
        { "type": "toolCall", "name": "ipython", "arguments": { "code": code } },
    ] })
}

/// An isolated child edits its copy while the parent edits the original;
/// the child's end takes its changes back and reports the conflict.
#[test]
fn an_isolated_subagent_hands_its_changes_back_with_conflicts() {
    let lane = Lane::new();
    for (name, body) in [("a.txt", "a0"), ("b.txt", "b0"), ("c.txt", "c0")] {
        std::fs::write(lane.work().join(name), body).expect("parent workspace file");
    }
    // The child edits only after the parent's edits (the parent's
    // workspace changed since the spawn, the copy's base).
    let marker = lane.path().join("parent-edited");
    let child_script = lane.script(
        "child",
        &json!([
            tool_call(&lane.cell(
                "child",
                &format!(
                    "deadline = asyncio.get_running_loop().time() + 60\nwhile not os.path.exists({marker:?}):\n    if asyncio.get_running_loop().time() > deadline:\n        raise TimeoutError(\"the parent never edited\")\n    await asyncio.sleep(0.05)\nfor name, body in [(\"a.txt\", \"a-child\"), (\"c.txt\", \"c-child\")]:\n    open(name, \"w\").write(body)\nrecord({{\"cwd\": os.getcwd()}})",
                    marker = marker.display().to_string(),
                ),
            )),
            { "text": "child edits done" },
        ]),
    );
    let parent_script = lane.script(
        "parent",
        &json!([
            tool_call(&lane.cell(
                "parent",
                &format!(
                    "handle = await rlm.spawn(\"edit the workspace\", name=\"iso\", why=\"isolate\", workspace=\"isolated\")\nfor name, body in [(\"b.txt\", \"b-parent\"), (\"c.txt\", \"c-parent\")]:\n    open(os.path.join({work:?}, name), \"w\").write(body)\nopen({marker:?}, \"w\").write(\"edited\")\nresults = await rlm.collect(handle, timeout_ms=60000)\nfiles = {{name: open(os.path.join({work:?}, name)).read() for name in sorted(os.listdir({work:?}))}}\nrecord({{\"id\": handle.rlm_child_id, \"results\": [{{\"status\": r.status, \"handback\": r.handback}} for r in results], \"files\": files}})",
                    work = lane.work().display().to_string(),
                    marker = marker.display().to_string(),
                ),
            )),
            { "text": "parent turn done" },
            { "text": "report noted" },
        ]),
    );
    let _daemon = spawn_supervisor(&lane.socket(), &lane.agent_dir());
    let mut client = connect(&lane.socket());
    let created = client.request(
        "create",
        &json!({
            "type": "create",
            "name": "parent",
            "config": {
                "cwd": lane.work().to_string_lossy(),
                "sessionDir": lane.sessions_dir().to_string_lossy(),
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
        &json!({ "type": "prompt", "activeSessionId": parent, "message": "spawn iso" }),
    );

    let receipt = lane.receipt("parent");
    let child_id = receipt["id"].as_str().expect("child id").to_owned();
    // `<agent dir>/workspaces/<parent session id>/<child id>`.
    let parents: Vec<PathBuf> = std::fs::read_dir(lane.agent_dir().join("workspaces"))
        .expect("workspaces dir")
        .map(|entry| entry.expect("workspaces entry").path())
        .collect();
    let [parent_workspaces] = parents.as_slice() else {
        panic!("one parent's workspaces: {parents:?}");
    };
    let root = parent_workspaces.join(&child_id);
    let conflicts = root.join("conflicts");
    assert_eq!(
        receipt,
        json!({
            "id": child_id,
            "results": [{
                "status": "done",
                "handback": format!(
                    "Workspace hand-back: took the child's changes to a.txt. Conflicts (both changed; the parent's content stays): c.txt. The child's versions are in {}.",
                    conflicts.display()
                ),
            }],
            "files": { "a.txt": "a-child", "b.txt": "b-parent", "c.txt": "c-parent" },
        }),
    );
    assert_eq!(
        lane.receipt("child"),
        json!({ "cwd": root.join("tree").to_string_lossy() }),
    );
    let kept: Vec<(String, String)> = std::fs::read_dir(&conflicts)
        .expect("conflicts dir")
        .map(|entry| {
            let path = entry.expect("conflicts entry").path();
            (
                path.file_name()
                    .expect("file name")
                    .to_string_lossy()
                    .into_owned(),
                std::fs::read_to_string(&path).expect("kept version"),
            )
        })
        .collect();
    assert_eq!(kept, [("c.txt".to_owned(), "c-child".to_owned())]);
}

/// An answered child whose kernel still writes (a thread of its kernel;
/// a client attached to the child keeps its settled kernel from the
/// release) is stopped before its hand-back: the parent's workspace takes
/// its last write and changes no more after the hand-back.
#[test]
fn a_child_still_writing_at_its_end_stops_before_its_hand_back() {
    let lane = Lane::new();
    let attached = lane.path().join("child-attached");
    let child_script = lane.script(
        "child",
        &json!([
            tool_call(&lane.cell(
                "child",
                &format!(
                    "import threading, time\ntree = os.getcwd()\ndef tick():\n    count = 0\n    while True:\n        count += 1\n        try:\n            open(os.path.join(tree, \"ticks.txt\"), \"w\").write(str(count))\n        except OSError:\n            pass\n        time.sleep(0.01)\nthreading.Thread(target=tick, daemon=True).start()\ndeadline = asyncio.get_running_loop().time() + 60\nwhile not os.path.exists({attached:?}):\n    if asyncio.get_running_loop().time() > deadline:\n        raise TimeoutError(\"no client attached\")\n    await asyncio.sleep(0.05)\nrecord({{\"cwd\": tree}})",
                    attached = attached.display().to_string(),
                ),
            )),
            { "text": "child ticking" },
        ]),
    );
    let parent_script = lane.script(
        "parent",
        &json!([
            tool_call(&lane.cell(
                "parent",
                &format!(
                    "handle = await rlm.spawn(\"tick\", name=\"ticker\", why=\"isolate\", workspace=\"isolated\")\nresults = await rlm.collect(handle, timeout_ms=60000)\nticks = os.path.join({work:?}, \"ticks.txt\")\nfirst = open(ticks).read()\nawait asyncio.sleep(1)\nrecord({{\"id\": handle.rlm_child_id, \"results\": [{{\"status\": r.status, \"handback\": r.handback}} for r in results], \"unchanged\": open(ticks).read() == first}})",
                    work = lane.work().display().to_string(),
                ),
            )),
            { "text": "parent turn done" },
            { "text": "report noted" },
        ]),
    );
    let _daemon = spawn_supervisor(&lane.socket(), &lane.agent_dir());
    let mut client = connect(&lane.socket());
    let created = client.request(
        "create",
        &json!({
            "type": "create",
            "name": "parent",
            "config": {
                "cwd": lane.work().to_string_lossy(),
                "sessionDir": lane.sessions_dir().to_string_lossy(),
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
        &json!({ "type": "prompt", "activeSessionId": parent, "message": "spawn ticker" }),
    );

    // A client attaches to the child while it runs.
    let deadline = Instant::now() + Duration::from_mins(1);
    let child = loop {
        assert!(Instant::now() < deadline, "the child never listed");
        let listed = client.request("list", &json!({ "type": "list" }));
        let found = listed["sessions"]
            .as_array()
            .expect("sessions array")
            .iter()
            .find(|row| row["sessionName"] == json!("ticker") && row["runtimeKind"] == "subagent")
            .map(|row| {
                row["activeSessionId"]
                    .as_str()
                    .expect("child active session id")
                    .to_owned()
            });
        if let Some(child) = found {
            break child;
        }
        std::thread::sleep(Duration::from_millis(100));
    };
    let mut watcher = connect(&lane.socket());
    watcher.request(
        "attach",
        &json!({ "type": "attach", "activeSessionId": child }),
    );
    std::fs::write(&attached, "attached").expect("attached marker");

    let receipt = lane.receipt("parent");
    let child_id = receipt["id"].as_str().expect("child id").to_owned();
    assert_eq!(
        receipt,
        json!({
            "id": child_id,
            "results": [{
                "status": "done",
                "handback": "Workspace hand-back: took the child's changes to ticks.txt.",
            }],
            "unchanged": true,
        }),
    );
}
