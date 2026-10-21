//! Dynamic workflows end to end: a real supervisor, a parent worker whose
//! faux model calls the `workflow` tool, and real faux child workers the
//! script's `agent()` calls spawn as silent RLM children.
//!
//! The `workflow` call returns at once and the run goes on in the
//! background. The run fans out three agents with `parallel`, pipes two
//! items through two stages with `pipeline` (the first stage asks for a
//! schema), and returns every answer in one `[job-settled job:workflow-N]`
//! report that starts a parent turn; the parent gets no child reports, and
//! the `workflow_activity` lane shows the finished run. A second run of
//! size small hits the agent budget: the calls past `max_agents` give
//! `null`.

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

const CHILD_ANSWER: &str = "agent says hi\n```json\n{\"ok\": true}\n```";

const SCRIPT: &str = r#"export const meta = { name: "e2e", description: "fan out and pipe", phases: [{ title: "Fan" }, { title: "Pipe" }] };
phase("Fan");
const fan = await parallel([1, 2, 3].map((n) => () => agent(`task ${n}`, { label: `fan ${n}` })));
phase("Pipe");
const piped = await pipeline(["a", "b"],
  (x) => agent(`stage one ${x}`, { label: `one ${x}`, schema: { type: "object", required: ["ok"] } }),
  (y, x) => agent(`stage two ${x} ${JSON.stringify(y)}`, { label: `two ${x}` }));
log("all stages ran");
return { fan, piped, spawned: budget.spawned(), request: args };"#;

const BUDGET_SCRIPT: &str = r#"export const meta = { name: "budget", description: "more agents than the size allows", phases: [] };
const all = await parallel([1, 2, 3, 4, 5, 6, 7].map((n) => () => agent(`job ${n}`)));
return all.map((answer) => answer !== null);"#;

fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Daemon {
    let log = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(socket.with_extension("daemon.log"))
        .expect("daemon log");
    Daemon::spawn(
        supervisor_command(socket, agent_dir)
            .env("EUKHE_CODING_AGENT_DIR", agent_dir)
            .env(
                "EUKHE_PACKAGE_DIR",
                Path::new(env!("CARGO_MANIFEST_DIR")).join("../.."),
            )
            .env_remove("PRIME_API_KEY")
            .stderr(Stdio::from(log)),
        socket,
    )
}

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

    fn request(&mut self, id: &str, command: &Value) -> Value {
        let line = self.try_request(id, command);
        assert_eq!(line["success"], true, "{command} failed: {line}");
        line["data"].clone()
    }

    /// The whole response line of `command`, success or not.
    fn try_request(&mut self, id: &str, command: &Value) -> Value {
        self.send_command(id, command);
        let deadline = Instant::now() + Duration::from_mins(4);
        loop {
            assert!(Instant::now() < deadline, "no response for id {id}");
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                return line;
            }
        }
    }

    fn run_turn(&mut self, session: &str, message: &str) {
        self.request(
            "prompt",
            &json!({ "type": "prompt", "activeSessionId": session, "message": message }),
        );
        self.request(
            "idle",
            &json!({ "type": "wait_for_idle", "activeSessionId": session }),
        );
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
}

struct Lane {
    dir: tempfile::TempDir,
}

impl Lane {
    fn new() -> Self {
        let lane = Self {
            dir: tempfile::TempDir::new().expect("temp dir"),
        };
        std::fs::create_dir_all(lane.agent_dir()).expect("agent dir");
        std::fs::create_dir_all(lane.sessions_dir()).expect("sessions dir");
        lane
    }

    fn agent_dir(&self) -> PathBuf {
        self.dir.path().join("agent")
    }

    fn sessions_dir(&self) -> PathBuf {
        self.dir.path().join("sessions")
    }

    fn socket(&self) -> PathBuf {
        self.dir.path().join("supervisor.sock")
    }

    fn script(&self, name: &str, responses: &Value) -> PathBuf {
        let path = self.dir.path().join(format!("{name}.json"));
        std::fs::write(
            &path,
            json!({ "engine": "faux", "responses": responses }).to_string(),
        )
        .expect("write script");
        path
    }

    fn create_parent(&self, client: &mut Client, script: &Path, child_script: &Path) -> String {
        let created = client.request(
            "create",
            &json!({
                "type": "create",
                "name": "parent",
                "config": {
                    "cwd": self.dir.path().to_string_lossy(),
                    "sessionDir": self.sessions_dir().to_string_lossy(),
                    "script": script.to_string_lossy(),
                    "childScript": child_script.to_string_lossy(),
                },
            }),
        );
        created["activeSessionId"]
            .as_str()
            .expect("parent active session id")
            .to_owned()
    }
}

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

fn workflow_call(script: &str, size: &str) -> Value {
    json!({ "content": [
        { "type": "toolCall", "name": "workflow", "arguments": { "script": script, "size": size, "args": "the request" } },
    ] })
}

/// The text of the `workflow` tool results, in order.
fn workflow_results(messages: &[Value]) -> Vec<String> {
    messages
        .iter()
        .filter(|message| message["role"] == "toolResult" && message["toolName"] == "workflow")
        .map(message_text)
        .collect()
}

/// The bodies of the workflow reports (`[job-settled job:workflow-N ...]`
/// inputs) that reached the transcript, in order.
fn workflow_reports(messages: &[Value]) -> Vec<String> {
    messages
        .iter()
        .map(message_text)
        .filter(|text| text.starts_with("[job-settled job:workflow-"))
        .collect()
}

/// The JSON value a workflow report returned (its text after `Output:`).
fn returned(report: &str) -> Value {
    let body = report.split_once("Output:").map_or("", |(_, body)| body);
    serde_json::from_str(body.trim()).unwrap_or_else(|_| panic!("report JSON: {report}"))
}

/// Wait until the parent and every background task it owns (workflow
/// runs and their reports' turns included) settled (`request` asserts the
/// barrier's success).
fn wait_quiescent(client: &mut Client, id: &str, session: &str) {
    client.request(
        id,
        &json!({ "type": "wait_for_idle", "activeSessionId": session, "waitForRlmQuiescence": true }),
    );
}

#[test]
fn a_workflow_fans_out_pipes_and_respects_the_budget() {
    let lane = Lane::new();
    let child_script = lane.script("child", &json!([{ "text": CHILD_ANSWER }]));
    let parent_script = lane.script(
        "parent",
        &json!([
            workflow_call(SCRIPT, "medium"),
            { "text": "workflow started" },
            { "text": "workflow done" },
            workflow_call(BUDGET_SCRIPT, "small"),
            { "text": "budget started" },
            { "text": "budget done" },
        ]),
    );
    let _daemon = spawn_supervisor(&lane.socket(), &lane.agent_dir());
    let mut client = connect(&lane.socket());
    let parent = lane.create_parent(&mut client, &parent_script, &child_script);

    // The call returns at once: the turn ends before the script does.
    client.run_turn(&parent, "run the workflow");
    let started = workflow_results(&client.messages(&parent));
    assert_eq!(started.len(), 1, "{started:?}");
    assert!(
        started[0].contains("(e2e): started in the background"),
        "{}",
        started[0]
    );
    // The run's report wakes the parent once the script ends.
    wait_quiescent(&mut client, "idle1", &parent);
    let messages = client.messages(&parent);
    let reports = workflow_reports(&messages);
    assert_eq!(reports.len(), 1, "{messages:?}");
    let header = reports[0].lines().next().unwrap();
    assert!(
        header.starts_with("[job-settled job:workflow-") && header.ends_with(" status:ok]"),
        "{}",
        reports[0]
    );
    assert!(reports[0].contains("(e2e): done"), "{}", reports[0]);
    assert_eq!(
        messages.last().map(message_text).as_deref(),
        Some("workflow done"),
        "the report did not start a turn: {messages:?}"
    );
    assert_eq!(
        returned(&reports[0]),
        json!({
            "fan": [CHILD_ANSWER, CHILD_ANSWER, CHILD_ANSWER],
            "piped": [CHILD_ANSWER, CHILD_ANSWER],
            "spawned": 7,
            "request": "the request",
        })
    );
    // Silent children: no report reached the parent.
    assert_eq!(
        messages
            .iter()
            .map(message_text)
            .filter(|text| text.starts_with("[child-"))
            .collect::<Vec<_>>(),
        Vec::<String>::new()
    );
    let runs = client.request(
        "activity",
        &json!({ "type": "workflow_activity", "activeSessionId": parent }),
    )["runs"]
        .clone();
    let run = &runs[0];
    assert_eq!(
        (
            run["name"].clone(),
            run["size"].clone(),
            run["state"].clone(),
            run["spawned"].clone(),
            run["done"].clone(),
            run["failed"].clone(),
            run["concurrency"].clone(),
            run["maxAgents"].clone(),
            run["logs"].clone(),
        ),
        (
            json!("e2e"),
            json!("medium"),
            json!({ "state": "done" }),
            json!(7),
            json!(7),
            json!(0),
            json!(6),
            json!(10),
            json!(["phase: Fan", "phase: Pipe", "all stages ran"]),
        )
    );
    let labels: Vec<(Value, Value)> = run["agents"]
        .as_array()
        .expect("agents")
        .iter()
        .map(|agent| (agent["label"].clone(), agent["phase"].clone()))
        .collect();
    assert_eq!(labels.len(), 7, "{run}");
    assert!(
        labels.contains(&(json!("fan 1"), json!("Fan"))),
        "{labels:?}"
    );
    assert!(
        labels.contains(&(json!("two b"), json!("Pipe"))),
        "{labels:?}"
    );

    // Size small: five agents run, the other two calls give null.
    client.run_turn(&parent, "run the budget workflow");
    wait_quiescent(&mut client, "idle2", &parent);
    let reports = workflow_reports(&client.messages(&parent));
    assert_eq!(reports.len(), 2, "{reports:?}");
    let ran = returned(&reports[1]);
    let answered = ran
        .as_array()
        .expect("answers")
        .iter()
        .filter(|answered| **answered == json!(true))
        .count();
    assert_eq!(
        (answered, ran.as_array().map(Vec::len)),
        (5, Some(7)),
        "{ran}"
    );
}

const HELD_SCRIPT: &str = r#"export const meta = { name: "held", description: "two held agents", phases: [] };
return await parallel([1, 2].map((n) => () => agent(`held ${n}`, { label: `held ${n}` })));"#;

/// Regression: a run outlives a crash of its parent's worker. The worker
/// dies while the run's agents still run; the relaunched worker resumes
/// the run task, reattaches the live agents instead of spawning new ones,
/// and the run reports exactly once.
#[test]
fn a_run_survives_a_parent_worker_crash_and_reports_once() {
    let lane = Lane::new();
    let child_script = lane.script(
        "child",
        &json!([{ "text": CHILD_ANSWER, "delayMs": 5_000 }]),
    );
    let parent_script = lane.script(
        "parent",
        &json!([workflow_call(HELD_SCRIPT, "small"), { "text": "workflow started" }]),
    );
    let _daemon = spawn_supervisor(&lane.socket(), &lane.agent_dir());
    let mut client = connect(&lane.socket());
    let parent = lane.create_parent(&mut client, &parent_script, &child_script);
    client.run_turn(&parent, "run the held workflow");
    let runs = client.request(
        "activity1",
        &json!({ "type": "workflow_activity", "activeSessionId": parent }),
    )["runs"]
        .clone();
    assert_eq!(runs[0]["state"], json!({ "state": "running" }), "{runs}");

    // The relaunched worker reads its faux script again from the start:
    // its one answer is the report's turn.
    lane.script("parent", &json!([{ "text": "workflow done" }]));
    let state = client.request(
        "state",
        &json!({ "type": "get_state", "activeSessionId": parent }),
    );
    let pid = state["workerPid"].as_u64().expect("the worker pid");
    let killed = std::process::Command::new("kill")
        .args(["-9", &pid.to_string()])
        .status()
        .expect("run kill");
    assert!(killed.success(), "kill -9 {pid}");

    // The supervisor relaunches the worker with backoff; the barrier
    // answers once the relaunched worker serves the session.
    let deadline = Instant::now() + Duration::from_mins(2);
    let mut attempt = 0;
    loop {
        attempt += 1;
        let idle = client.try_request(
            &format!("idle{attempt}"),
            &json!({ "type": "wait_for_idle", "activeSessionId": parent, "waitForRlmQuiescence": true }),
        );
        if idle["success"] == true {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "the session never came back: {idle}"
        );
        std::thread::sleep(Duration::from_millis(100));
    }

    let messages = client.messages(&parent);
    let reports = workflow_reports(&messages);
    assert_eq!(reports.len(), 1, "{messages:?}");
    assert!(reports[0].contains("(held): done"), "{}", reports[0]);
    assert_eq!(returned(&reports[0]), json!([CHILD_ANSWER, CHILD_ANSWER]));
    assert_eq!(
        messages.last().map(message_text).as_deref(),
        Some("workflow done"),
        "{messages:?}"
    );
    let runs = client.request(
        "activity2",
        &json!({ "type": "workflow_activity", "activeSessionId": parent }),
    )["runs"]
        .clone();
    assert_eq!(
        (runs[0]["state"].clone(), runs[0]["spawned"].clone()),
        (json!({ "state": "done" }), json!(2)),
        "{runs}"
    );
}
