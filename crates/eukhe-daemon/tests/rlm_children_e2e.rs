//! End-to-end RLM child machinery against the real `eukhe-daemon` supervisor:
//! supervisor-backed child sessions spawn through the supervisor link, run
//! in their own worker processes, appear in the supervisor roster, settle
//! with an answer, and die on delete (the durable `RlmSubagentHost`
//! primitives: spawn / prompt / `wait_settled` / delete / `create_session`).
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
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};

use eukhe_core::durable::children::{
    RlmChildDeleteRequest, RlmChildIdentity, RlmChildPromptRequest, RlmChildRunState,
    RlmChildSpawnRequest, RlmChildWaitRequest, RlmCreateSessionRequest, RlmSubagentHost,
};
use eukhe_daemon::rlm_children::{ParentIdentity, SupervisorChildSessions};
use eukhe_daemon::supervisor_link::SupervisorLink;
use serde_json::{json, Value};

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
use daemon::supervisor_command;
use process::Daemon;

fn spawn_daemon(socket: &Path, agent_dir: &Path) -> Daemon {
    Daemon::spawn_bound(
        supervisor_command(socket, agent_dir)
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

/// Minimal JSONL supervisor client (list / kill / `get_last_assistant_text`).
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> (Self, Value) {
        let deadline = Instant::now() + Duration::from_secs(5);
        let stream = loop {
            match UnixStream::connect(socket) {
                Ok(stream) => break stream,
                Err(_) if Instant::now() < deadline => {
                    std::thread::sleep(Duration::from_millis(20));
                }
                Err(error) => panic!("connect supervisor: {error}"),
            }
        };
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
        self.read_line_with_budget(Duration::from_secs(15))
    }

    /// `read_line` with a caller-chosen budget: a raw `create` that
    /// launches a worker answers after the worker's connect budget (TS
    /// `WORKER_CONNECT_TIMEOUT_MS`: up to 30s), which the shared 15s line
    /// budget turns into a false timeout under the binary's
    /// parallel-test load.
    fn read_line_with_budget(&mut self, budget: Duration) -> Value {
        let mut line = String::new();
        let deadline = Instant::now() + budget;
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
        let deadline = Instant::now() + Duration::from_secs(30);
        loop {
            assert!(Instant::now() < deadline, "no response for id {id}");
            let line = self.read_line();
            if line.get("id").and_then(|v| v.as_str()) == Some(id) {
                return line;
            }
        }
    }

    /// `read_response` with a worker-boot budget (the raw-create path's
    /// reader): every line waits on the remaining wall budget, so a
    /// worker-launching create answers inside the same window the host's
    /// `CREATE_TIMEOUT_MS` covers.
    fn read_response_slow(&mut self, id: &str) -> Value {
        let deadline = Instant::now() + Duration::from_secs(90);
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            assert!(!remaining.is_zero(), "no response for id {id}");
            let line = self.read_line_with_budget(remaining);
            if line.get("id").and_then(|v| v.as_str()) == Some(id) {
                return line;
            }
        }
    }
}

/// One scripted-response script file (the child worker's scripted engine).
fn write_script(dir: &Path, answer: &str) -> PathBuf {
    let script = dir.join("script.json");
    std::fs::write(
        &script,
        json!({ "responses": [ { "text": answer, "delayMs": 30 } ] }).to_string(),
    )
    .expect("write script");
    script
}

/// Children registry bound to the running supervisor, with a parent identity
/// rooted at `agent_dir`.
fn children(socket: &Path, agent_dir: &Path, script: &Path, depth: u32) -> SupervisorChildSessions {
    let sessions = SupervisorChildSessions::new(
        Arc::new(SupervisorLink::new(socket.to_path_buf())),
        agent_dir.to_path_buf(),
        "parent-active-id".to_string(),
    );
    sessions.set_identity(ParentIdentity {
        rlm_depth: depth,
        rlm_max_depth: 2,
        // Off-catalog on purpose: scripted children do not resolve models.
        model: Some("scripted/faux-1".to_string()),
        cwd: Some(agent_dir.to_string_lossy().to_string()),
        session_id: Some("parent-session-uuid".to_string()),
        session_file: Some(agent_dir.join("parent.jsonl").to_string_lossy().to_string()),
        thinking: None,
        child_script: Some(script.to_string_lossy().to_string()),
    });
    sessions
}

/// Poll a sync probe (JSONL supervisor client) until it yields a value.
fn wait_until<T>(deadline: Duration, mut probe: impl FnMut() -> Option<T>) -> T {
    let deadline = Instant::now() + deadline;
    loop {
        if let Some(value) = probe() {
            return value;
        }
        assert!(Instant::now() < deadline, "condition never became true");
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// A durable session's storage directory: it holds the store's
/// `main.jsonl` commit log.
fn is_durable_storage(path: &Path) -> bool {
    path.join("main.jsonl").is_file()
}

const CHILD_ID: &str = "sub-0000000a";
const CHILD_SESSION_ID: &str = "0a000000-0000-4000-8000-00000000000a";

fn spawn_request(name: &str, prompt: &str) -> RlmChildSpawnRequest {
    RlmChildSpawnRequest {
        idempotency_key: "rlm:1:spawn".to_string(),
        child: RlmChildIdentity {
            rlm_child_id: CHILD_ID.to_string(),
            session_id: CHILD_SESSION_ID.to_string(),
        },
        name: name.to_string(),
        prompt: prompt.to_string(),
        model: None,
        thinking: None,
        depth: 1,
        max_depth: 2,
        spawned_by_request_id: None,
        parent_task_id: "1".to_string(),
    }
}

/// The subagent rows of the supervisor roster.
fn subagent_rows(client: &mut Client, id: &str) -> Vec<Value> {
    client.send_command(id, &json!({ "type": "list" }));
    let list = client.read_response(id);
    list["data"]["sessions"]
        .as_array()
        .map(|sessions| {
            sessions
                .iter()
                .filter(|summary| summary["runtimeKind"] == "subagent")
                .cloned()
                .collect()
        })
        .unwrap_or_default()
}

/// Spawn a child through the supervisor, observe it in the supervisor
/// roster, prompt it and wait for its settled answer, then delete it and
/// watch the supervisor roster drop it. Every keyed call repeats as a no-op.
#[tokio::test]
async fn rlm_children_spawn_prompt_settle_delete_end_to_end() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let _daemon = spawn_daemon(&socket, &agent_dir);
    let (mut client, hello) = Client::connect(&socket);
    assert_eq!(hello["type"], "daemon_hello");
    let script = write_script(dir.path(), "child answer");
    let children = children(&socket, &agent_dir, &script, 0);

    // Spawn: one child worker session created through the supervisor.
    let child = children
        .spawn(spawn_request("worker-a", "ship the lane"))
        .await
        .expect("spawn");
    assert_eq!(child.session_name, "worker-a");
    assert_eq!(child.session_id, CHILD_SESSION_ID);
    assert_eq!(child.model, "scripted/faux-1");
    // TS child-session layout: the child persists inside its per-child
    // directory under the parent's session-artifacts tree.
    let expected_dir = agent_dir
        .join("session-artifacts")
        .join("parent-session-uuid")
        .join(CHILD_ID);
    assert_eq!(child.session_dir, expected_dir.to_string_lossy());
    // TS child-session layout: the child persists inside its per-child
    // directory under the parent's session-artifacts tree, alongside the
    // per-child display file the passive roster reads for hydration. On
    // the durable harness the session is its storage directory
    // (`<child-dir>/<session-id>/`, holding the store's `main.jsonl`)
    // instead of one `<session-id>.jsonl` file.
    let child_sessions: Vec<PathBuf> = std::fs::read_dir(&expected_dir)
        .expect("child session dir")
        .filter_map(std::result::Result::ok)
        .map(|entry| entry.path())
        .filter(|path| is_durable_storage(path))
        .collect();
    assert_eq!(child_sessions.len(), 1, "one session in the child dir");
    let display_file = expected_dir.join("rlm-subagent.json");
    let display: Value =
        serde_json::from_str(&std::fs::read_to_string(&display_file).expect("display file"))
            .expect("parse display file");
    assert_eq!(display["type"], "rlm_subagent");
    assert_eq!(display["childId"], CHILD_ID);
    assert_eq!(display["sessionName"], "worker-a");
    assert_eq!(display["status"], "running");
    assert_eq!(
        display["model"],
        json!({ "provider": "scripted", "modelId": "faux-1" })
    );
    assert_eq!(
        display["sessionFile"],
        child_sessions[0].to_string_lossy().to_string()
    );

    // The supervisor roster shows the child as a depth-1 subagent session.
    let roster_summary = wait_until(Duration::from_secs(10), || {
        subagent_rows(&mut client, "l1").into_iter().next()
    });
    assert_eq!(roster_summary["rlmDepth"], 1);
    assert_eq!(roster_summary["sessionName"], "worker-a");
    // The child records the recursion identity (TS parity: parentSession
    // + rlmDepth on child sessions; the durable storage has no header
    // line, so the child's summary carries them).
    assert_eq!(
        roster_summary["parentSessionPath"],
        agent_dir.join("parent.jsonl").to_string_lossy().to_string()
    );
    assert_eq!(
        roster_summary["sessionFile"],
        child_sessions[0].to_string_lossy().to_string()
    );

    // A repeated spawn key answers the first spawn's child: no second
    // worker is created.
    let again = children
        .spawn(spawn_request("worker-a", "ship the lane"))
        .await
        .expect("repeated spawn");
    assert_eq!(again, child);
    assert_eq!(subagent_rows(&mut client, "l2").len(), 1);

    // Prompt the task, then long-poll the child until it settles with
    // its answer preview.
    let prompt = RlmChildPromptRequest {
        idempotency_key: "rlm:1:prompt".to_string(),
        session_id: CHILD_SESSION_ID.to_string(),
        rlm_child_id: CHILD_ID.to_string(),
        prompt: "ship the lane".to_string(),
    };
    children.prompt(prompt.clone()).await.expect("prompt");
    children.prompt(prompt).await.expect("repeated prompt");
    let deadline = Instant::now() + Duration::from_secs(30);
    let settled = loop {
        let observation = children
            .wait_settled(RlmChildWaitRequest {
                session_id: CHILD_SESSION_ID.to_string(),
                rlm_child_id: CHILD_ID.to_string(),
                timeout_ms: 2_000,
            })
            .await
            .expect("wait settled");
        match observation.state {
            RlmChildRunState::Running | RlmChildRunState::Idle { .. } => {
                assert!(Instant::now() < deadline, "child never settled");
            }
            state @ (RlmChildRunState::Answered { .. } | RlmChildRunState::Failed { .. }) => {
                break state;
            }
        }
    };
    assert_eq!(
        settled,
        RlmChildRunState::Answered {
            answer_preview: Some("child answer".to_string()),
        }
    );
    // The settled run completes the child's display entry.
    let display: Value =
        serde_json::from_str(&std::fs::read_to_string(&display_file).expect("display file"))
            .expect("parse display file");
    assert_eq!(display["status"], "completed");

    // Delete: the child dies and leaves the supervisor roster; a repeated
    // delete key is a no-op.
    let delete = RlmChildDeleteRequest {
        idempotency_key: "rlm:1:delete".to_string(),
        session_id: CHILD_SESSION_ID.to_string(),
        rlm_child_id: CHILD_ID.to_string(),
    };
    children.delete(delete.clone()).await.expect("delete");
    wait_until(Duration::from_secs(10), || {
        client.send_command("l3", &json!({ "type": "list" }));
        let list = client.read_response("l3");
        list["data"]["sessions"]
            .as_array()
            .filter(|sessions| sessions.is_empty())
            .map(|_| ())
    });
    children.delete(delete).await.expect("repeated delete");
    assert!(children.list().await.expect("listings").is_empty());
}

/// `rlm.create_session`: a resident depth-0 daemon session over the link,
/// prompted, answering through its worker, and not part of the subagent
/// roster.
#[tokio::test]
async fn rlm_create_session_spawns_a_prompted_depth_zero_session() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let _daemon = spawn_daemon(&socket, &agent_dir);
    let (mut client, _hello) = Client::connect(&socket);
    let script = write_script(dir.path(), "root session answer");
    let children = children(&socket, &agent_dir, &script, 0);

    let handle = children
        .create_session(RlmCreateSessionRequest {
            idempotency_key: "rlm.create_session:call-1:0".to_string(),
            prompt: "start a root session".to_string(),
            name: Some("root-b".to_string()),
            model: None,
            thinking: None,
            cwd: Some(agent_dir.to_string_lossy().to_string()),
        })
        .await
        .expect("create session");
    assert_eq!(handle.name, "root-b");
    // The durable session is its storage directory (`<sessions>/<id>/`,
    // holding the store's `main.jsonl`), not a `<id>.jsonl` file.
    assert!(
        is_durable_storage(Path::new(&handle.session_file)),
        "{handle:?}"
    );
    assert_eq!(handle.model, "scripted/faux-1");

    // A depth-0 resident session, not a subagent roster row.
    client.send_command("l1", &json!({ "type": "list" }));
    let list = client.read_response("l1");
    let sessions = list["data"]["sessions"].as_array().expect("sessions");
    assert_eq!(sessions.len(), 1);
    assert_eq!(sessions[0]["rlmDepth"], 0);
    assert_eq!(sessions[0]["runtimeKind"], "top-level");
    let listings = children.list().await.expect("child listings");
    assert!(
        listings.is_empty(),
        "create_session children are not subagents"
    );

    // The session was prompted: its worker answered.
    let active_id = handle.active_session_id.clone();
    let answer = wait_until(Duration::from_secs(10), || {
        client.send_command(
            "g1",
            &json!({ "type": "get_last_assistant_text", "activeSessionId": active_id }),
        );
        let final_answer = client.read_response("g1");
        final_answer["data"]["text"]
            .as_str()
            .filter(|text| !text.is_empty())
            .map(str::to_string)
    });
    assert_eq!(answer, "root session answer");

    // Killing the session removes it from the supervisor roster.
    client.send_command(
        "k1",
        &json!({ "type": "kill", "activeSessionId": active_id }),
    );
    let killed = client.read_response("k1");
    assert_eq!(killed["success"], true, "kill failed: {killed}");
    wait_until(Duration::from_secs(10), || {
        client.send_command("l2", &json!({ "type": "list" }));
        let list = client.read_response("l2");
        list["data"]["sessions"]
            .as_array()
            .filter(|sessions| sessions.is_empty())
            .map(|_| ())
    });
}

/// `rlm.create_session` is depth-0 only: the host refuses it from a deeper
/// session with the TS error (the spawn depth bound lives in the durable
/// children extension).
#[tokio::test]
async fn rlm_create_session_refuses_from_a_nested_session() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let _daemon = spawn_daemon(&socket, &agent_dir);
    let script = write_script(dir.path(), "unreachable");
    let children = children(&socket, &agent_dir, &script, 2);
    let error = children
        .create_session(RlmCreateSessionRequest {
            idempotency_key: "rlm.create_session:call-1:0".to_string(),
            prompt: "nope".to_string(),
            name: None,
            model: None,
            thinking: None,
            cwd: None,
        })
        .await
        .expect_err("create_session from depth 2");
    assert_eq!(
        error.to_string(),
        "rlm.create_session is available only from a depth-0 session"
    );
}

/// TS #2396's daemon-wide half (`createRlmSubagentRuntime`): the
/// supervisor holds a subagent spawn's name under a reservation for the
/// whole fresh-launch admission, so parallel same-name same-parent creates
/// cannot both admit - exactly one create lands and the rest fail closed
/// with the TS unavailability error before the durable ledger edge is
/// appended. The reservation releases with the admission: once the winner
/// is gone, the same name admits again.
#[tokio::test]
async fn parallel_same_name_subagent_creates_admit_exactly_one() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    let _daemon = spawn_daemon(&socket, &agent_dir);
    let (mut client, _hello) = Client::connect(&socket);
    let script = write_script(dir.path(), "twin answer");
    let parent_file = agent_dir.join("parent.jsonl");
    let parent_file = parent_file.to_string_lossy().to_string();

    // The raw create a worker's `rlm.spawn` routes: a scripted subagent
    // child of one parent scope, with the name the reservations key on.
    let subagent_create = |child_id: &str| {
        let session_dir = agent_dir
            .join("session-artifacts")
            .join("parent-session-uuid")
            .join(child_id);
        std::fs::create_dir_all(&session_dir).expect("child session dir");
        json!({
            "type": "create",
            "name": "twin-worker",
            "config": {
                "cwd": agent_dir.to_string_lossy(),
                "sessionDir": session_dir.to_string_lossy(),
                "rlmDepth": 1,
                "rlmMaxDepth": 2,
                "provider": "scripted",
                "model": "faux-1",
                "script": script.to_string_lossy(),
                "childScript": script.to_string_lossy(),
                "parentSessionPath": parent_file,
            },
            "runtimeMetadata": {
                "kind": "subagent",
                "rlmChildId": child_id,
                "parentActiveSessionId": "parent-active-id",
                "parentSessionId": "parent-session-uuid",
                "parentSessionFile": parent_file,
                "rlmDepth": 1,
                "createdAt": 0,
            },
            "lifecycle": "resident",
        })
    };

    // Four parallel same-name creates of the same parent scope: commands
    // on one connection are dispatched concurrently, so their responses
    // arrive out of order (the losers fail at the reservation in
    // milliseconds, the winner answers after its worker launch) - drain
    // the connection until every id is answered instead of reading ids
    // in sequence.
    let ids = ["c1", "c2", "c3", "c4"];
    for id in ids {
        client.send_command(id, &subagent_create(&format!("sub-{id}")));
    }
    let deadline = Instant::now() + Duration::from_secs(90);
    let mut responses: std::collections::HashMap<String, Value> = std::collections::HashMap::new();
    while responses.len() < ids.len() {
        let remaining = deadline.saturating_duration_since(Instant::now());
        assert!(!remaining.is_zero(), "never answered: {ids:?}");
        let line = client.read_line_with_budget(remaining);
        if let Some(id) = line.get("id").and_then(Value::as_str).map(str::to_string) {
            responses.insert(id, line);
        }
    }
    let mut successes = Vec::new();
    let mut failures = 0;
    for id in ids {
        let response = &responses[id];
        if response["success"].as_bool().unwrap_or(false) {
            successes.push(response.clone());
        } else {
            failures += 1;
            assert_eq!(
                response["error"].as_str().expect("failure error"),
                "Agent name \"twin-worker\" is unavailable: an agent of that name already exists at depth 1 under this parent",
                "the losing create fails closed with the TS unavailability error"
            );
        }
    }
    assert_eq!(successes.len(), 1, "exactly one same-name create admits");
    assert_eq!(failures, 3, "every racing create fails closed");

    // The reservation released with the admission: once the winner is
    // gone, the same name admits again.
    let winner = &successes[0];
    let active_id = winner["data"]["activeSessionId"]
        .as_str()
        .expect("winner active id");
    client.send_command(
        "k1",
        &json!({ "type": "kill", "activeSessionId": active_id }),
    );
    let killed = client.read_response_slow("k1");
    assert!(
        killed["success"].as_bool().unwrap_or(false),
        "kill winner: {killed}"
    );
    wait_until(Duration::from_secs(10), || {
        client.send_command("l1", &json!({ "type": "list" }));
        let list = client.read_response("l1");
        list["data"]["sessions"]
            .as_array()
            .filter(|sessions| sessions.is_empty())
            .map(|_| ())
    });
    client.send_command("c5", &subagent_create("sub-c5"));
    let retry = client.read_response_slow("c5");
    assert!(
        retry["success"].as_bool().unwrap_or(false),
        "the freed name admits again: {retry}"
    );
}
