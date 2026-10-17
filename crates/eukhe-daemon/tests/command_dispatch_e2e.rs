//! End-to-end verifier for client-command dispatch during a live turn:
//! the daemon-response timeout class from the 2026-09-22 dogfood
//! (`/system-prompt` timing out at the client's 10s cap) — a client
//! command (the TUI's `/system-prompt`, `/context`, `/usage`, `/session`
//! family) must answer fast while a turn streams, not wait for the turn
//! to settle (the TS bar: the TS daemon-mode `get_system_prompt` arm is
//! a synchronous `session.systemPrompt` read on the same event loop that
//! streams the turn; the provider awaits yield, so the read stays ms).
//!
//! The mock provider streams one chunk, then holds the turn open for
//! `TURN_HOLD_MS` before the finish chunk: every measurement below runs
//! while the turn is provably mid-flight (an assistant `message_start`
//! streamed but the run not settled).
// Pedantic-gate dispositions (fleet-uniform ruling; see this lane's PR for
// the full rationale).
// Stack-resident futures by design on the daemon's hot paths; boxing the
// call sites for a lint tick is a perf regression with zero correctness gain.
#![allow(clippy::large_futures)]
// 64-bit-only targets; the narrowing casts sit at OS boundaries
// (pid/fd/time/size) where the values are bounded by the kernel - the
// dead-guard expect()s would add panic paths where silent wrap was
// deliberate.
#![allow(
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_precision_loss
)]
// The fn-length threshold is a style gate, not correctness; the structure
// campaign owns the god-fn splits as a follow-up.
#![allow(clippy::too_many_lines)]
// API-shape opinions, not defects; the surfaces are deliberate.
#![allow(
    clippy::unnecessary_wraps,
    clippy::zero_sized_map_values,
    clippy::struct_excessive_bools,
    clippy::struct_field_names
)]
use std::fmt::Write as _;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::Path;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_command;
use process::Daemon;

/// How long the mock provider holds the turn open between its first
/// streamed chunk and the finish chunk. Must exceed the TUI's 10s
/// `UI_REQUEST_TIMEOUT_MS` so a serialized dispatch reproduces the exact
/// dogfood failure (a response that cannot arrive inside the client cap).
const TURN_HOLD_MS: u64 = 12_000;
/// The bar for "fast mid-turn" (the TS reference answers in single-digit
/// ms; this leaves generous CI margin for a cold first read).
const FAST_RESPONSE_MS: u64 = 2_000;

/// A mock OpenAI-completions provider that streams one content chunk,
/// sleeps `TURN_HOLD_MS`, then finishes: the client session is provably
/// mid-turn for the whole sleep window.
struct SlowMock {
    requests: Arc<Mutex<usize>>,
    port: u16,
}

impl SlowMock {
    fn start() -> SlowMock {
        let requests = Arc::new(Mutex::new(0usize));
        let listener = TcpListener::bind("127.0.0.1:0").expect("bind mock");
        let port = listener.local_addr().expect("mock addr").port();
        let requests_for_thread = Arc::clone(&requests);
        std::thread::spawn(move || {
            for stream in listener.incoming() {
                let Ok(stream) = stream else { continue };
                let requests = Arc::clone(&requests_for_thread);
                std::thread::spawn(move || {
                    let _ = serve(stream, &requests);
                });
            }
        });
        SlowMock { requests, port }
    }

    fn url(&self) -> String {
        format!("http://127.0.0.1:{}/v1", self.port)
    }

    fn count(&self) -> usize {
        *self.requests.lock().expect("mock lock")
    }
}

fn chunk(delta: &Value, finish_reason: Option<&str>) -> String {
    json!({
        "id": "chatcmpl-test",
        "object": "chat.completion.chunk",
        "created": 1_750_000_000,
        "model": "mock-1",
        "choices": [{"index": 0, "delta": delta, "finish_reason": finish_reason}],
    })
    .to_string()
}

fn serve(mut stream: TcpStream, requests: &Arc<Mutex<usize>>) -> std::io::Result<()> {
    let mut reader = BufReader::new(stream.try_clone()?);
    let mut head = String::new();
    loop {
        let mut line = String::new();
        if reader.read_line(&mut line)? == 0 {
            return Ok(());
        }
        head.push_str(&line);
        if line == "\r\n" {
            break;
        }
    }
    let mut content_length = 0usize;
    for line in head.lines() {
        let lower = line.to_ascii_lowercase();
        if let Some(value) = lower.strip_prefix("content-length:") {
            content_length = value.trim().parse().unwrap_or_default();
        }
    }
    let mut body_bytes = vec![0u8; content_length];
    if content_length > 0 {
        reader.read_exact(&mut body_bytes)?;
    }
    {
        let mut requests = requests.lock().expect("mock lock");
        *requests += 1;
    }
    // First chunk goes out immediately so the assistant `message_start`
    // streams; the sleep holds the turn open mid-stream.
    let mut payload = String::new();
    write!(
        payload,
        "data: {}\n\n",
        chunk(&json!({"role": "assistant", "content": "streaming"}), None)
    )
    .expect("write to String");
    stream.write_all(
        format!(
            "HTTP/1.1 200 OK\r\nContent-Type: text/event-stream\r\nConnection: close\r\n\r\n{payload}"
        )
        .as_bytes(),
    )?;
    std::thread::sleep(Duration::from_millis(TURN_HOLD_MS));
    let mut tail = String::new();
    write!(tail, "data: {}\n\n", chunk(&json!({}), Some("stop"))).expect("write to String");
    tail.push_str("data: [DONE]\n\n");
    stream.write_all(tail.as_bytes())
}

fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Daemon {
    std::fs::create_dir_all(agent_dir).expect("agent dir");
    Daemon::spawn_bound(
        supervisor_command(socket, agent_dir)
            .env_remove("PRIME_API_KEY")
            .env_remove("EUKHE_CODING_AGENT_DIR")
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
    /// The `state_tree_update` frames this connection got.
    tree_updates: Vec<Value>,
}

impl Client {
    fn connect(socket: &Path) -> Client {
        let stream = std::os::unix::net::UnixStream::connect(socket).expect("connect");
        let writer = stream.try_clone().expect("clone");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
            events: Vec::new(),
            tree_updates: Vec::new(),
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
                Err(_) => {
                    assert!(
                        Instant::now() < deadline,
                        "timed out waiting for supervisor line"
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

    /// Send a command and measure the time until its response arrives;
    /// session events observed along the way are collected like
    /// [`Self::request`].
    fn timed_request(&mut self, id: &str, command: &Value) -> (Value, Duration) {
        let started = Instant::now();
        self.send_command(id, command);
        let response = self.request(id);
        (response, started.elapsed())
    }

    fn request(&mut self, id: &str) -> Value {
        let deadline = Instant::now() + Duration::from_mins(2);
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
        match line.get("type").and_then(Value::as_str) {
            Some("session_event") => self.events.push(line["event"].clone()),
            Some("state_tree_update") => self.tree_updates.push(line.clone()),
            _ => {}
        }
    }

    /// Block until a `state_tree_update` frame reaches `cursor`.
    fn wait_for_tree_cursor(&mut self, cursor: u64) {
        let deadline = Instant::now() + Duration::from_secs(30);
        while !self
            .tree_updates
            .iter()
            .any(|frame| frame["update"]["cursor"].as_u64() >= Some(cursor))
        {
            assert!(
                Instant::now() < deadline,
                "no state tree frame reached {cursor}"
            );
            let line = self.read_line();
            self.collect_event(&line);
        }
    }

    /// Block until the live run settles (the `agent_end` frame), long
    /// after the mid-turn measurements: the mock's hold window outlasts
    /// them, so a quiet-drain would stop while the turn still streams.
    fn wait_for_settled(&mut self) {
        let deadline = Instant::now() + Duration::from_mins(1);
        loop {
            assert!(Instant::now() < deadline, "the turn never settled");
            let line = self.read_line();
            let settled = line.get("type").and_then(Value::as_str) == Some("session_event")
                && line["event"]["type"].as_str() == Some("agent_end");
            self.collect_event(&line);
            if settled {
                return;
            }
        }
    }

    /// Block until the stream shows the given event shape (a session event
    /// whose `message.role` matches), collecting everything on the way.
    fn wait_for_event(&mut self, role: &str) {
        let deadline = Instant::now() + Duration::from_secs(30);
        loop {
            assert!(Instant::now() < deadline, "no assistant start streamed");
            let line = self.read_line();
            let is_match = line.get("type").and_then(Value::as_str) == Some("session_event")
                && line["event"]["message"]["role"].as_str() == Some(role)
                && line["event"]["type"].as_str() == Some("message_start");
            self.collect_event(&line);
            if is_match {
                return;
            }
        }
    }
}

/// One measured command: name, wire command, and the response time.
struct Measurement {
    command: String,
    elapsed: Duration,
    success: bool,
}

fn info_command(name: &str, session_id: &str) -> Value {
    json!({
        "type": name,
        "activeSessionId": session_id,
    })
}

/// The client command family the TUI serves through its 10s
/// `UI_REQUEST_TIMEOUT_MS` bound: `/system-prompt`, `/session`,
/// `/context` (+ its `/usage` alias), plus the same-route getters the TUI
/// refreshes (`get_session_context`, `get_tool_definition`,
/// `get_resource_snapshot`).
const MATRIX: &[(&str, &str)] = &[
    ("get_session_stats", "/session"),
    ("get_context_tree", "/context, /usage"),
    ("get_session_context", "wire: get_session_context"),
    ("get_system_prompt", "/system-prompt"),
    ("get_chat_view", "the startup chat view block"),
    ("get_memory", "the status gauge"),
    ("get_memory_tree", "/memory and the dashboard's Memory view"),
    ("get_state_tree", "eukhe state"),
    ("get_tool_definition", "wire: get_tool_definition"),
    ("get_resource_snapshot", "wire: get_resource_snapshot"),
];

fn run_matrix(client: &mut Client, session_id: &str, phase: &str) -> Vec<Measurement> {
    let mut measurements = Vec::new();
    for (index, (command, surface)) in MATRIX.iter().enumerate() {
        let id = format!("matrix-{phase}-{index}");
        let mut command_value = info_command(command, session_id);
        if *command == "get_tool_definition" {
            command_value["name"] = json!("bash");
        }
        let (response, elapsed) = client.timed_request(&id, &command_value);
        measurements.push(Measurement {
            command: format!("{command} ({surface})"),
            elapsed,
            success: response["success"] == json!(true),
        });
    }
    measurements
}

fn print_table(phase: &str, measurements: &[Measurement]) {
    println!("== response-time table ({phase}) ==");
    for measurement in measurements {
        println!(
            "{:<40} {:>8.0} ms  {}",
            measurement.command,
            measurement.elapsed.as_millis(),
            if measurement.success { "ok" } else { "FAILED" }
        );
    }
}

/// One supervisor with one created, attached session over the mock
/// provider. Fields drop in order: the supervisor dies before its
/// directory goes.
struct OpenSession {
    _supervisor: Daemon,
    client: Client,
    session_id: String,
    mock: SlowMock,
    _dir: tempfile::TempDir,
}

fn open_session() -> OpenSession {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let agent_dir = dir.path().join("agent");
    let session_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&session_dir).expect("session dir");
    let mock = SlowMock::start();
    std::fs::write(
        agent_dir.join("models.json"),
        json!({
            "providers": {
                "prime-inference": {
                    "api": "openai-completions",
                    "baseUrl": mock.url(),
                    "apiKey": "sk-battery",
                    "models": [
                        {
                            "id": "mock-1",
                            "name": "Mock 1",
                            "api": "openai-completions",
                            "contextWindow": 128_000,
                            "maxTokens": 4096
                        }
                    ]
                }
            }
        })
        .to_string(),
    )
    .expect("write models.json");
    // No session title: its background request would add to the provider
    // request count the test asserts.
    std::fs::write(
        agent_dir.join("settings.json"),
        json!({ "onboardingCompleted": true, "titles": { "generate": false } }).to_string(),
    )
    .expect("write settings.json");
    let socket = dir.path().join("cmd-dispatch.sock");
    let supervisor = spawn_supervisor(&socket, &agent_dir);
    let mut client = Client::connect(&socket);
    client.send_command(
        "c1",
        &json!({
            "type": "create",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": session_dir.to_string_lossy(),
                "provider": "prime-inference",
                "model": "mock-1",
            },
        }),
    );
    let created = client.request("c1");
    assert_eq!(created["success"], true, "create failed: {created}");
    let session_id = created["data"]["id"]
        .as_str()
        .or_else(|| created["data"]["sessionId"].as_str())
        .expect("session id")
        .to_string();
    client.send_command(
        "a1",
        &json!({ "type": "attach", "activeSessionId": session_id }),
    );
    let attached = client.request("a1");
    assert_eq!(attached["success"], true, "attach failed: {attached}");
    OpenSession {
        _supervisor: supervisor,
        client,
        session_id,
        mock,
        _dir: dir,
    }
}

/// `get_chat_view` answers the root session's chat view — the block the
/// interactive client prints on open (`OptChat` spec §10) — read from the chat
/// memory without waiting on any turn. A fresh agent dir's chat is empty.
#[test]
fn get_chat_view_answers_the_root_sessions_view() {
    let mut session = open_session();
    let (response, _) = session
        .client
        .timed_request("v1", &info_command("get_chat_view", &session.session_id));
    assert_eq!(
        response["success"], true,
        "get_chat_view failed: {response}"
    );
    let reply: eukhe_types::daemon::ChatViewReply =
        serde_json::from_value(response["data"].clone()).expect("the reply decodes");
    assert_eq!(
        reply,
        eukhe_types::daemon::ChatViewReply {
            view: Some(eukhe_types::daemon::ChatViewSnapshot {
                text: "<chat>\n</chat>".to_string(),
                messages: 0,
                lines: 0,
                bytes: 14,
            }),
        }
    );
}

/// `get_memory` answers the root session's chat memory — the `/memory`
/// header and view, without the `<chat>` frame — without waiting on any
/// turn. A fresh agent dir's chat is empty and its compactor follows the
/// default model.
#[test]
fn get_memory_answers_the_root_sessions_memory() {
    let mut session = open_session();
    let (response, _) = session
        .client
        .timed_request("m1", &info_command("get_memory", &session.session_id));
    assert_eq!(response["success"], true, "get_memory failed: {response}");
    let reply: eukhe_types::daemon::MemoryReply =
        serde_json::from_value(response["data"].clone()).expect("the reply decodes");
    assert_eq!(
        reply,
        eukhe_types::daemon::MemoryReply {
            memory: Some(eukhe_types::daemon::MemorySnapshot {
                status: eukhe_types::daemon::MemoryStatusSnapshot {
                    messages: 0,
                    lines: 0,
                    view_bytes: 0,
                    unsummarized: 0,
                    running: 0,
                    model: None,
                    last_error: None,
                },
                text: String::new(),
            }),
        }
    );
}

/// `get_memory_tree` answers the root session's memory tree: a fresh
/// agent dir's chat has no view lines, and a line past its end opens into
/// nothing.
#[test]
fn get_memory_tree_answers_the_root_sessions_tree() {
    let mut session = open_session();
    let status = eukhe_types::daemon::MemoryStatusSnapshot {
        messages: 0,
        lines: 0,
        view_bytes: 0,
        unsummarized: 0,
        running: 0,
        model: None,
        last_error: None,
    };
    let (response, _) = session
        .client
        .timed_request("t1", &info_command("get_memory_tree", &session.session_id));
    assert_eq!(
        response["success"], true,
        "get_memory_tree failed: {response}"
    );
    let reply: eukhe_types::daemon::MemoryTreeReply =
        serde_json::from_value(response["data"].clone()).expect("the reply decodes");
    assert_eq!(
        reply,
        eukhe_types::daemon::MemoryTreeReply {
            tree: Some(eukhe_types::daemon::MemoryTree {
                status: status.clone(),
                node: None,
                level: eukhe_types::daemon::MemoryTreeLevel::Lines { nodes: Vec::new() },
            }),
        }
    );
    let mut opened = info_command("get_memory_tree", &session.session_id);
    opened["node"] = json!({ "id": 0, "count": 1 });
    let (response, _) = session.client.timed_request("t2", &opened);
    assert_eq!(
        response["success"], true,
        "get_memory_tree failed: {response}"
    );
    let reply: eukhe_types::daemon::MemoryTreeReply =
        serde_json::from_value(response["data"].clone()).expect("the reply decodes");
    assert_eq!(
        reply,
        eukhe_types::daemon::MemoryTreeReply {
            tree: Some(eukhe_types::daemon::MemoryTree {
                status,
                node: Some(eukhe_types::daemon::MemoryZoom { id: 0, count: 1 }),
                level: eukhe_types::daemon::MemoryTreeLevel::NoLine,
            }),
        }
    );
}

/// The nodes that the first `count` state tree records make, in id order:
/// a `put` sets its node; a `del` removes its node and the nodes below it.
fn replay_state_tree(
    records: &[eukhe_types::daemon::StateTreeRecord],
    count: usize,
) -> Vec<eukhe_types::daemon::StateTreeNode> {
    use eukhe_types::daemon::{StateTreeOp, StateTreeRecord};
    let mut nodes = std::collections::BTreeMap::new();
    for record in &records[..count] {
        match record {
            StateTreeRecord::Do(StateTreeOp::Put(node)) => {
                nodes.insert(node.id, node.clone());
            }
            StateTreeRecord::Do(StateTreeOp::Del { id }) => {
                let mut gone = std::collections::BTreeSet::from([*id]);
                nodes.retain(|key, node: &mut eukhe_types::daemon::StateTreeNode| {
                    let keep = !gone.contains(key) && !gone.contains(&node.parent);
                    if !keep {
                        gone.insert(*key);
                    }
                    keep
                });
            }
            StateTreeRecord::Rewind(_) => panic!("a derived tree records no rewind"),
        }
    }
    nodes.into_values().collect()
}

/// `get_state_tree` answers the session's state tree: the snapshot holds
/// the root conversation under the root, the records after cursor 0 make
/// the snapshot, and a rewind plan to cursor 0 stops every node.
#[test]
fn get_state_tree_answers_the_sessions_tree() {
    use eukhe_types::daemon::{
        StateRewindPlanReply, StateTreeEffect, StateTreeKind, StateTreeNode, StateTreeNodeRef,
        StateTreeReply,
    };
    let mut session = open_session();
    let request = |name: &str, extra: Value| {
        let mut command = info_command(name, &session.session_id);
        if let (Some(command), Value::Object(extra)) = (command.as_object_mut(), extra) {
            command.extend(extra);
        }
        command
    };
    let snapshot_command = request("get_state_tree", json!({}));
    let plan_command = request("get_state_rewind_plan", json!({ "cursor": 0 }));
    let records_command = request("get_state_tree", json!({ "since": 0 }));
    let mut data = |id: &str, command: &Value| {
        let (response, _) = session.client.timed_request(id, command);
        assert_eq!(response["success"], true, "{command} failed: {response}");
        response["data"].clone()
    };
    let snapshot = data("s1", &snapshot_command);
    let plan = data("s2", &plan_command);
    let records = data("s3", &records_command);
    let StateTreeReply::Snapshot(snapshot) =
        serde_json::from_value(snapshot).expect("the snapshot decodes")
    else {
        panic!("a snapshot without since");
    };
    let plan: StateRewindPlanReply = serde_json::from_value(plan).expect("the plan decodes");
    let StateTreeReply::Records(records) =
        serde_json::from_value(records).expect("the records decode")
    else {
        panic!("records with since");
    };
    let count = |cursor: u64| usize::try_from(cursor).expect("a cursor fits");
    assert_eq!(
        (
            snapshot.nodes.first().cloned(),
            replay_state_tree(&records.records, count(snapshot.cursor)),
            records.from,
            plan.target,
            plan.effects,
        ),
        (
            Some(StateTreeNode {
                id: 1,
                parent: 0,
                kind: StateTreeKind::Conversation,
                key: "1".to_owned(),
                value: json!({ "id": 1 }),
            }),
            snapshot.nodes.clone(),
            0,
            0,
            replay_state_tree(&records.records, count(plan.cursor))
                .into_iter()
                .map(|node| StateTreeEffect::Stop(StateTreeNodeRef {
                    id: node.id,
                    kind: node.kind,
                    key: node.key,
                }))
                .collect::<Vec<_>>(),
        )
    );
}

/// `subscribe_state_tree` answers the snapshot and then streams the new
/// records, from the snapshot's cursor on, to the subscribed connection
/// only: another connection attached to the same session never gets a
/// `state_tree_update` frame.
#[test]
fn subscribe_state_tree_streams_records_to_its_connection_only() {
    use eukhe_types::daemon::{StateTreeRecord, StateTreeRecords, StateTreeReply};
    let OpenSession {
        _supervisor,
        mut client,
        session_id,
        mock: _mock,
        _dir: dir,
    } = open_session();
    let socket = dir.path().join("cmd-dispatch.sock");
    let mut other = Client::connect(&socket);
    other.send_command(
        "o1",
        &json!({ "type": "attach", "activeSessionId": session_id }),
    );
    assert_eq!(other.request("o1")["success"], true);
    let mut subscribe = info_command("subscribe_state_tree", &session_id);
    let (response, _) = client.timed_request("s1", &subscribe);
    assert_eq!(response["success"], true, "subscribe failed: {response}");
    let StateTreeReply::Snapshot(snapshot) =
        serde_json::from_value(response["data"].clone()).expect("the snapshot decodes")
    else {
        panic!("a snapshot without since");
    };
    client.send_command(
        "p1",
        &json!({ "type": "prompt", "activeSessionId": session_id, "message": "hello" }),
    );
    assert_eq!(client.request("p1")["success"], true);
    client.wait_for_settled();
    // What the other connection reads after the turn, from the snapshot.
    let mut since = info_command("get_state_tree", &session_id);
    since["since"] = json!(snapshot.cursor);
    let (response, _) = other.timed_request("o2", &since);
    let StateTreeReply::Records(read) =
        serde_json::from_value(response["data"].clone()).expect("the records decode")
    else {
        panic!("records with since");
    };
    client.wait_for_tree_cursor(read.cursor);
    // The frames, applied from the snapshot's cursor as a client does.
    let mut have = snapshot.cursor;
    let mut streamed: Vec<StateTreeRecord> = Vec::new();
    for frame in &client.tree_updates {
        assert_eq!(frame["activeSessionId"], json!(session_id));
        let update: StateTreeRecords =
            serde_json::from_value(frame["update"].clone()).expect("the update decodes");
        if update.cursor <= have {
            continue;
        }
        assert!(
            update.from <= have,
            "a gap before {}: {update:?}",
            update.from
        );
        let skip = usize::try_from(have - update.from).expect("a cursor fits");
        streamed.extend(update.records[skip..].iter().cloned());
        have = update.cursor;
    }
    let count = usize::try_from(read.cursor - snapshot.cursor).expect("a cursor fits");
    // A round trip on the other connection: a frame routed to it would
    // be on its queue before this answer.
    let (response, _) = other.timed_request("o3", &info_command("get_state_tree", &session_id));
    assert_eq!(response["success"], true);
    subscribe["type"] = json!("unsubscribe_state_tree");
    let (unsubscribed, _) = client.timed_request("s2", &subscribe);
    assert_eq!(
        (
            streamed.get(..count).map(<[StateTreeRecord]>::to_vec),
            read.records.is_empty(),
            other.tree_updates.len(),
            unsubscribed["success"].clone(),
        ),
        (Some(read.records), false, 0, json!(true))
    );
}

#[test]
fn client_commands_answer_fast_while_a_turn_streams() {
    // Bound by name (not `..`), so the supervisor and its directory live
    // until the test ends.
    let OpenSession {
        _supervisor,
        mut client,
        session_id,
        mock,
        _dir,
    } = open_session();

    // Phase 1: idle measurements (the baseline every command must beat).
    let idle = run_matrix(&mut client, &session_id, "idle");
    print_table("idle", &idle);
    for measurement in &idle {
        assert!(measurement.success, "idle {} failed", measurement.command);
        assert!(
            measurement.elapsed < Duration::from_millis(FAST_RESPONSE_MS),
            "idle {} took {:?}",
            measurement.command,
            measurement.elapsed
        );
    }

    // Phase 2: a turn holds open mid-stream, then the same matrix runs
    // while the assistant message is streaming (the dogfood window).
    client.send_command(
        "p1",
        &json!({ "type": "prompt", "activeSessionId": session_id, "message": "hello" }),
    );
    let queued = client.request("p1");
    assert_eq!(queued["success"], true, "prompt rejected: {queued}");
    client.wait_for_event("assistant");
    assert_eq!(mock.count(), 1, "one provider request mid-turn");

    let mid_turn = run_matrix(&mut client, &session_id, "mid-turn");
    print_table("mid-turn", &mid_turn);
    for measurement in &mid_turn {
        assert!(
            measurement.success,
            "mid-turn {} failed",
            measurement.command
        );
        assert!(
            measurement.elapsed < Duration::from_millis(FAST_RESPONSE_MS),
            "mid-turn {} took {:?} — serialized behind the streaming turn              (the TS bar: commands interleave with the turn loop)",
            measurement.command,
            measurement.elapsed
        );
    }

    // The turn settles normally after the hold window.
    client.wait_for_settled();
    let types = client
        .events
        .iter()
        .filter_map(|event| event.get("type").and_then(Value::as_str))
        .map(str::to_string)
        .collect::<Vec<_>>();
    assert!(
        types.iter().any(|t| t == "agent_end"),
        "the turn never settled: {types:?}"
    );
    assert_eq!(mock.count(), 1, "still one provider request");
}
