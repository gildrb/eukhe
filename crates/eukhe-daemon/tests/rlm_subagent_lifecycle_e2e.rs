//! RLM subagent lifecycle e2e through the product surfaces, and across a
//! daemon restart.
//!
//! One real supervisor, a real parent worker whose faux model drives the
//! kernel `rlm.*` / `agent_message` surfaces, and a real scripted child
//! worker spawned through `rlm.spawn`:
//!
//! 1. Spawn, wait (`rlm.collect` with a timeout), the child's report
//!    reaching the parent once, a parent `agent_message.send` and a user
//!    `@name` message (a prompt carrying `replyTo`) reaching the child, and
//!    a kill (`rlm.delete_subagent`) that drops the child worker.
//! 2. A daemon restart — a graceful `shutdown` (the parent reopens from its
//!    session file) or a supervisor `kill -9` (the workers survive and
//!    re-register) — while the child is (a) running or (b) settled with
//!    its report still queued behind a busy parent turn. After the
//!    restart the child is found again or reported closed, its report
//!    reaches the parent exactly once, a wait on it settles, and the kill
//!    works.
//!
//! The kernel Python is this checkout's runtime
//! (`eukhe-core/tests/support/kernel_runtime.rs`).

// The fn-length threshold is a style gate; each verifier reads as one
// scenario top to bottom.
#![allow(clippy::too_many_lines)]

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

impl Daemon {
    /// A graceful stop: the `shutdown` command, then the process exit.
    fn shutdown(mut self, client: &mut Client) {
        client.send_command("shutdown", &json!({ "type": "shutdown" }));
        let deadline = Instant::now() + Duration::from_secs(30);
        while self
            .child
            .try_wait()
            .expect("wait for the supervisor exit")
            .is_none()
        {
            assert!(Instant::now() < deadline, "the supervisor never exited");
            std::thread::sleep(Duration::from_millis(50));
        }
    }

    /// A crash: `SIGKILL` the supervisor alone (its workers live on).
    fn kill9(mut self) {
        self.child.kill().expect("kill -9 the supervisor");
        self.child.wait().expect("reap the supervisor");
    }
}

fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Daemon {
    let log = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(socket.with_extension("daemon.log"))
        .expect("daemon log");
    Daemon::spawn(
        supervisor_command(socket, agent_dir)
            .env("EUKHE_CODING_AGENT_DIR", agent_dir)
            // The kernel's `agent_message` global is the bundled
            // `agent-message` skill; a binary built outside the checkout
            // (`CARGO_TARGET_DIR`) finds it through the package dir.
            .env(
                "EUKHE_PACKAGE_DIR",
                Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."),
            )
            .env_remove("PRIME_API_KEY")
            // Workers orphaned by a supervisor `kill -9` must outlive the
            // restart window, yet never leak into later test binaries.
            .env(
                eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
                "20000",
            )
            .stderr(Stdio::from(log)),
        socket,
    )
}

/// Wait until the supervisor accepts connections (a restarted supervisor
/// replaces a stale socket file, so file existence is not readiness).
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
        self.send_command(id, command);
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

    fn wait_idle(&mut self, session: &str) {
        self.request(
            "idle",
            &json!({ "type": "wait_for_idle", "activeSessionId": session }),
        );
    }

    /// Run one prompted turn to idle.
    fn run_turn(&mut self, session: &str, message: &str) {
        self.request(
            "prompt",
            &json!({ "type": "prompt", "activeSessionId": session, "message": message }),
        );
        self.wait_idle(session);
    }

    fn messages(&mut self, session: &str) -> Vec<Value> {
        self.request(
            "messages",
            &json!({ "type": "get_messages", "activeSessionId": session }),
        )["messages"]
            .as_array()
            .cloned()
            .expect("messages array")
    }

    /// The live supervisor roster (the `list` wire surface).
    fn roster(&mut self) -> Vec<Value> {
        self.request("list", &json!({ "type": "list" }))["sessions"]
            .as_array()
            .cloned()
            .expect("sessions array")
    }

    /// The parent's tracked-children wire surface.
    fn rlm_children(&mut self, parent: &str) -> Vec<Value> {
        self.request(
            "children",
            &json!({ "type": "get_rlm_children", "activeSessionId": parent }),
        )["children"]
            .as_array()
            .cloned()
            .expect("children array")
    }
}

/// Poll `probe` until it yields a value; the panic names `what`.
fn wait_until<T>(budget: Duration, what: &str, mut probe: impl FnMut() -> Option<T>) -> T {
    let deadline = Instant::now() + budget;
    loop {
        if let Some(value) = probe() {
            return value;
        }
        assert!(Instant::now() < deadline, "timed out waiting for {what}");
        std::thread::sleep(Duration::from_millis(100));
    }
}

/// One test's sandbox: agent dir, socket, receipts, scripts.
struct Lane {
    dir: tempfile::TempDir,
}

impl Lane {
    fn new() -> Self {
        let lane = Self {
            dir: tempfile::TempDir::new().expect("temp dir"),
        };
        std::fs::create_dir_all(lane.agent_dir()).expect("agent dir");
        std::fs::create_dir_all(lane.receipts()).expect("receipts dir");
        std::fs::create_dir_all(lane.sessions_dir()).expect("sessions dir");
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

    fn gate(&self) -> PathBuf {
        self.path().join("gate")
    }

    fn supervisor(&self) -> Daemon {
        spawn_supervisor(&self.socket(), &self.agent_dir())
    }

    fn daemon_log(&self) -> String {
        std::fs::read_to_string(self.socket().with_extension("daemon.log")).unwrap_or_default()
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
            "import asyncio, json, os, traceback\nfrom dataclasses import asdict\ndef record(value):\n    open({receipt:?} + \".tmp\", \"w\").write(json.dumps(value, default=str))\n    os.replace({receipt:?} + \".tmp\", {receipt:?})\ntry:\n{body}\nexcept BaseException:\n    open({error:?}, \"w\").write(traceback.format_exc())\n    raise",
            receipt = receipt.display().to_string(),
            error = error.display().to_string(),
        )
    }

    /// The recorded receipt `name`, waiting for the cell that writes it;
    /// a failed cell's traceback fails the test at once.
    fn receipt(&self, name: &str) -> Value {
        let receipt = self.receipts().join(format!("{name}.json"));
        let error = self.receipts().join(format!("{name}.error"));
        wait_until(Duration::from_mins(2), &format!("receipt {name}"), || {
            if let Ok(traceback) = std::fs::read_to_string(&error) {
                panic!("cell {name} failed: {traceback}");
            }
            std::fs::read_to_string(&receipt)
                .ok()
                .map(|text| serde_json::from_str(&text).expect("receipt json"))
        })
    }

    /// Create the parent session (`resume` reopens a persisted one).
    fn create_parent(
        &self,
        client: &mut Client,
        script: &Path,
        child_script: &Path,
        resume: Option<&str>,
    ) -> Parent {
        let mut create = json!({
            "type": "create",
            "name": "parent",
            "config": {
                "cwd": self.path().to_string_lossy(),
                "sessionDir": self.sessions_dir().to_string_lossy(),
                "script": script.to_string_lossy(),
                "childScript": child_script.to_string_lossy(),
            },
        });
        if let Some(path) = resume {
            create["sessionPath"] = json!(path);
        }
        let created = client.request("create", &create);
        Parent {
            active: created["activeSessionId"]
                .as_str()
                .expect("parent active session id")
                .to_owned(),
            file: created["sessionFile"]
                .as_str()
                .expect("parent session file")
                .to_owned(),
        }
    }
}

struct Parent {
    active: String,
    file: String,
}

/// A message's text: a string content, or its text blocks joined.
fn message_text(message: &Value) -> String {
    match &message["content"] {
        Value::String(text) => text.clone(),
        Value::Array(blocks) => blocks
            .iter()
            .filter_map(|block| block["text"].as_str())
            .collect::<Vec<_>>()
            .join("\n"),
        other => other.to_string(),
    }
}

/// The parent's child reports about `kid`: the `[child-exited: …]` /
/// `[child-failed: …]` inputs the child task delivered.
fn kid_reports(messages: &[Value]) -> Vec<String> {
    messages
        .iter()
        .map(message_text)
        .filter(|text| text.starts_with("[child-") && text.contains("child:kid]"))
        .collect()
}

/// Wait until the parent rendered a report about `kid` and went idle;
/// return the reports.
fn await_report(client: &mut Client, parent: &str) -> Vec<String> {
    wait_until(Duration::from_mins(2), "the child report", || {
        client.wait_idle(parent);
        let reports = kid_reports(&client.messages(parent));
        (!reports.is_empty()).then_some(reports)
    })
}

/// Whether the live supervisor roster still runs the `kid` subagent.
fn kid_resident(client: &mut Client) -> bool {
    client
        .roster()
        .iter()
        .any(|row| row["sessionName"] == "kid" && row["runtimeKind"] == "subagent")
}

/// The body of the spawn cell: spawn `kid`, record its id.
const SPAWN: &str = "handle = await rlm.spawn(\"run the lane task\", name=\"kid\")\nrecord({\"id\": handle.rlm_child_id})";

/// The body of the busy-parent cell: spawn `kid`, wait for its run to
/// settle, record the result, then hold the turn until the gate opens.
fn spawn_wait_hold(gate: &Path) -> String {
    format!(
        "handle = await rlm.spawn(\"run the lane task\", name=\"kid\")\nresults = await rlm.collect(handle, timeout_ms=60000)\nrecord({{\"id\": handle.rlm_child_id, \"results\": [asdict(r) for r in results]}})\nwhile not os.path.exists({gate:?}):\n    await asyncio.sleep(0.05)",
        gate = gate.display().to_string(),
    )
}

/// The body of the wait-and-kill cell: wait for `kid` to settle, read the
/// roster, delete it, read the roster again.
const WAIT_AND_KILL: &str = "results = await rlm.collect(\"kid\", timeout_ms=60000)\nbefore = [[s.rlm_child_id, s.status] for s in await rlm.list_subagents()]\ndeleted = await rlm.delete_subagent(\"kid\")\nafter = [[s.rlm_child_id, s.status] for s in await rlm.list_subagents()]\nrecord({\"results\": [{\"status\": r.status, \"settled\": r.settled, \"answer\": r.answer_preview, \"error\": r.error} for r in results], \"before\": before, \"deleted\": deleted.rlm_child_id, \"after\": after})";

fn tool_call(code: &str) -> Value {
    json!({ "content": [
        { "type": "toolCall", "name": "ipython", "arguments": { "code": code } },
    ] })
}

/// Spawn, wait, report, message (kernel `agent_message` and a user's
/// `@name` prompt), and kill, all through the product surfaces.
#[test]
fn spawn_message_wait_and_kill_a_subagent() {
    let lane = Lane::new();
    let child_script = lane.script(
        "child",
        &json!([
            { "text": "kid report one", "delayMs": 500 },
            { "text": "kid got the ping" },
            { "text": "kid answers the user" },
        ]),
    );
    let parent_script = lane.script(
        "parent",
        &json!([
            tool_call(&lane.cell(
                "spawn",
                "handle = await rlm.spawn(\"run the lane task\", name=\"kid\")\nresults = await rlm.collect(handle, timeout_ms=60000)\nrecord({\"id\": handle.rlm_child_id, \"results\": [{\"status\": r.status, \"settled\": r.settled, \"answer\": r.answer_preview} for r in results]})",
            )),
            { "text": "spawn turn done" },
            { "text": "report noted" },
            tool_call(&lane.cell(
                "send",
                "receipt = await agent_message.send(\"ping from parent\", receiver_role=\"child\", receiver_name=\"kid\")\nrecord(receipt)",
            )),
            { "text": "send turn done" },
            tool_call(&lane.cell("kill", WAIT_AND_KILL)),
            { "text": "kill turn done" },
        ]),
    );
    let _daemon = lane.supervisor();
    let mut client = connect(&lane.socket());
    let parent = lane.create_parent(&mut client, &parent_script, &child_script, None);

    // Spawn + wait: `rlm.collect` with a timeout blocks the cell until the
    // child's run settles, and the settled result carries its answer.
    client.run_turn(&parent.active, "spawn the kid");
    let spawned = lane.receipt("spawn");
    assert_eq!(
        spawned["results"],
        json!([{ "status": "done", "settled": true, "answer": "kid report one" }]),
        "{spawned}"
    );
    // The child's report reaches the parent once (a follow-up turn).
    let reports = await_report(&mut client, &parent.active);
    assert_eq!(
        reports,
        vec![
            "[child-exited: no-reply child:kid]\n\nLast assistant text: kid report one".to_owned()
        ],
    );
    let kid = wait_until(Duration::from_secs(30), "the kid worker", || {
        client
            .roster()
            .into_iter()
            .find(|row| row["sessionName"] == "kid" && row["runtimeKind"] == "subagent")
    });
    let kid_active = kid["activeSessionId"].as_str().expect("kid id").to_owned();

    // Message by name through the parent's kernel `agent_message`.
    client.run_turn(&parent.active, "ping the kid");
    let receipt = lane.receipt("send");
    assert_eq!(receipt["receiverRole"], "child", "{receipt}");
    assert_eq!(receipt["target"]["activeSessionId"], json!(kid_active));
    let child_texts = wait_until(Duration::from_secs(60), "the kid's ping answer", || {
        client.wait_idle(&kid_active);
        let texts: Vec<String> = client
            .messages(&kid_active)
            .iter()
            .map(message_text)
            .collect();
        texts
            .iter()
            .any(|text| text == "kid got the ping")
            .then_some(texts)
    });
    assert!(
        child_texts
            .iter()
            .any(|text| text.contains("ping from parent")),
        "{child_texts:?}"
    );

    // A user's `@kid` message from the parent's session: the child's
    // answer comes back to the parent as one `agent_reply` row, no turn.
    client.request(
        "at-name",
        &json!({
            "type": "prompt",
            "activeSessionId": kid_active,
            "message": "what do you say?",
            "replyTo": parent.active,
        }),
    );
    let replies = wait_until(Duration::from_secs(60), "the @kid reply", || {
        let replies: Vec<Value> = client
            .messages(&parent.active)
            .into_iter()
            .filter(|message| message["customType"] == "agent_reply")
            .collect();
        (!replies.is_empty()).then_some(replies)
    });
    assert_eq!(replies.len(), 1, "{replies:?}");
    assert!(
        message_text(&replies[0]).contains("kid answers the user"),
        "{replies:?}"
    );

    // Kill: the delete drops the row and the child worker.
    client.run_turn(&parent.active, "kill the kid");
    let killed = lane.receipt("kill");
    let child_id = spawned["id"].clone();
    assert_eq!(
        killed,
        json!({
            "results": [{ "status": "done", "settled": true, "answer": "kid report one", "error": null }],
            "before": [[child_id, "completed"]],
            "deleted": child_id,
            "after": [],
        }),
    );
    wait_until(Duration::from_secs(30), "the kid worker exit", || {
        (!kid_resident(&mut client)).then_some(())
    });
    assert_eq!(kid_reports(&client.messages(&parent.active)).len(), 1);
}

/// How the daemon restarts.
#[derive(Clone, Copy)]
enum Restart {
    /// `shutdown`, a new supervisor, and the parent reopened from its
    /// session file.
    Graceful,
    /// `kill -9` of the supervisor alone; its workers re-register with the
    /// new one.
    Kill9,
}

/// What the child is doing when the daemon restarts.
#[derive(Clone, Copy)]
enum ChildAtRestart {
    /// Mid-run (a held model response).
    Running,
    /// Settled, its report queued behind the parent's held turn.
    ReportQueued,
}

/// Restart the daemon under `restart` with the child in `state`, then
/// assert the child's report reaches the parent exactly once, a wait on
/// it settles, and the kill works.
fn restart_lane(restart: Restart, state: ChildAtRestart) {
    let lane = Lane::new();
    let child_script = lane.script(
        "child",
        &json!([match state {
            // Held past the restart: a graceful stop interrupts it, a
            // surviving worker finishes it.
            ChildAtRestart::Running => json!({ "text": "kid done", "delayMs": match restart {
                Restart::Graceful => 60_000,
                Restart::Kill9 => 4_000,
            } }),
            ChildAtRestart::ReportQueued => json!({ "text": "kid done", "delayMs": 200 }),
        }]),
    );
    let first_cell = match state {
        ChildAtRestart::Running => lane.cell("spawn", SPAWN),
        ChildAtRestart::ReportQueued => lane.cell("spawn", &spawn_wait_hold(&lane.gate())),
    };
    // Kill9 keeps the parent worker (and its script cursor) across the
    // restart, so one script covers the whole lane; a graceful restart
    // reopens the parent on the `after` script.
    let wait_and_kill = [
        tool_call(&lane.cell("kill", WAIT_AND_KILL)),
        json!({ "text": "kill turn done" }),
    ];
    let before_responses = match restart {
        Restart::Graceful => json!([tool_call(&first_cell), { "text": "spawn turn done" }]),
        Restart::Kill9 => json!([
            tool_call(&first_cell),
            { "text": "spawn turn done" },
            { "text": "report noted" },
            wait_and_kill[0].clone(),
            wait_and_kill[1].clone(),
        ]),
    };
    let parent_script = lane.script("parent", &before_responses);
    let daemon = lane.supervisor();
    let mut client = connect(&lane.socket());
    let parent = lane.create_parent(&mut client, &parent_script, &child_script, None);
    client.request(
        "prompt",
        &json!({ "type": "prompt", "activeSessionId": parent.active, "message": "spawn the kid" }),
    );
    let spawned = lane.receipt("spawn");
    let child_id = spawned["id"].as_str().expect("child id").to_owned();
    match state {
        ChildAtRestart::Running => {
            client.wait_idle(&parent.active);
            wait_until(Duration::from_secs(30), "the running child", || {
                client
                    .rlm_children(&parent.active)
                    .iter()
                    .any(|row| row["id"] == json!(child_id) && row["status"] == "running")
                    .then_some(())
            });
        }
        ChildAtRestart::ReportQueued => {
            assert_eq!(spawned["results"][0]["status"], "done", "{spawned}");
            // The report is admitted to the parent's inbox (its keyed
            // submission is durable) while the held turn keeps it queued.
            wait_until(Duration::from_secs(30), "the queued report", || {
                storage_text(Path::new(&parent.file))
                    .contains(":report:")
                    .then_some(())
            });
        }
    }

    // The restarted supervisor lives until the lane ends.
    let (mut client, parent_active, _daemon) = match restart {
        Restart::Graceful => {
            daemon.shutdown(&mut client);
            let _ = std::fs::write(lane.gate(), "open");
            let daemon = lane.supervisor();
            let mut client = connect(&lane.socket());
            let after = lane.script(
                "parent-after",
                &json!([{ "text": "report noted" }, wait_and_kill[0].clone(), wait_and_kill[1].clone()]),
            );
            let reopened =
                lane.create_parent(&mut client, &after, &child_script, Some(&parent.file));
            (client, reopened.active, daemon)
        }
        Restart::Kill9 => {
            daemon.kill9();
            let daemon = lane.supervisor();
            let mut client = connect(&lane.socket());
            // The surviving parent worker re-registers under its id.
            let active = parent.active.clone();
            wait_until(
                Duration::from_secs(60),
                "the parent re-registration",
                || {
                    client
                        .roster()
                        .iter()
                        .any(|row| row["activeSessionId"] == json!(active))
                        .then_some(())
                },
            );
            let _ = std::fs::write(lane.gate(), "open");
            (client, parent.active.clone(), daemon)
        }
    };

    let reports = await_report(&mut client, &parent_active);
    let expected = match (restart, state) {
        (Restart::Graceful, ChildAtRestart::Running) => {
            "[child-failed: interrupted child:kid]\n\nRLM child run was interrupted: the child stopped mid-run while its parent session was down"
        }
        (Restart::Kill9, ChildAtRestart::Running) | (_, ChildAtRestart::ReportQueued) => {
            "[child-exited: no-reply child:kid]\n\nLast assistant text: kid done"
        }
    };
    assert_eq!(reports, vec![expected.to_owned()], "{}", lane.daemon_log());

    // Wait + kill after the restart.
    client.run_turn(&parent_active, "wait for and kill the kid");
    let killed = lane.receipt("kill");
    let (status, answer, error, row_status) = match (restart, state) {
        (Restart::Graceful, ChildAtRestart::Running) => (
            "error",
            Value::Null,
            json!("RLM child run was interrupted: the child stopped mid-run while its parent session was down"),
            "error",
        ),
        (Restart::Kill9, ChildAtRestart::Running) | (_, ChildAtRestart::ReportQueued) => {
            ("done", json!("kid done"), Value::Null, "completed")
        }
    };
    assert_eq!(
        killed,
        json!({
            "results": [{ "status": status, "settled": true, "answer": answer, "error": error }],
            "before": [[child_id, row_status]],
            "deleted": child_id,
            "after": [],
        }),
    );
    wait_until(Duration::from_secs(30), "the kid worker exit", || {
        (!kid_resident(&mut client)).then_some(())
    });
    // Still exactly one report once everything settled.
    client.wait_idle(&parent_active);
    assert_eq!(
        kid_reports(&client.messages(&parent_active)),
        vec![expected.to_owned()]
    );
}

/// A durable session's stored text: every file of its storage directory
/// (or the session file itself).
fn storage_text(dir: &Path) -> String {
    let mut text = std::fs::read_to_string(dir).unwrap_or_default();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(next) = pending.pop() {
        let Ok(entries) = std::fs::read_dir(&next) else {
            continue;
        };
        for entry in entries.filter_map(Result::ok) {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else if let Ok(content) = std::fs::read_to_string(&path) {
                text.push_str(&content);
            }
        }
    }
    text
}

#[test]
fn graceful_restart_with_a_running_child_reports_it_interrupted_once() {
    restart_lane(Restart::Graceful, ChildAtRestart::Running);
}

#[test]
fn graceful_restart_delivers_a_queued_child_report_once() {
    restart_lane(Restart::Graceful, ChildAtRestart::ReportQueued);
}

#[test]
fn kill9_restart_with_a_running_child_reports_its_answer_once() {
    restart_lane(Restart::Kill9, ChildAtRestart::Running);
}

#[test]
fn kill9_restart_delivers_a_queued_child_report_once() {
    restart_lane(Restart::Kill9, ChildAtRestart::ReportQueued);
}
