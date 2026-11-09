//! The whole-worker idle passivation e2e (TS `idleEvictionMinutes`):
//! a settled RLM child's supervisor stop leaves the session file and the
//! parent's roster row intact; the parent's `agent_message.send` to the
//! passivated child WAKES a fresh worker over the saved file and
//! delivers.
//!
//! The test drives the worker->supervisor passivation request directly
//! (the child worker's supervisor-link ask, replayed with the child's own
//! worker token from its persisted descriptor) so the e2e stays gate-fast:
//! the worker-side idle clock and park-arm gates are covered by the unit
//! battery (`idle_passivation_window_*`), and the timed path against the
//! real binary by the VM census (the settings-driven 1-minute threshold).

// Pedantic-gate disposition for THIS test root: the settled-child
// passivation flow is one intentionally linear harness script (the
// fn-length gate is style, not correctness).
#![allow(clippy::too_many_lines)]
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use serde_json::{json, Value};

use eukhe_core::agent_messaging::register_agent_message_host_handlers;
use eukhe_core::durable::children::{
    RlmChildIdentity, RlmChildPromptRequest, RlmChildRunState, RlmChildSession,
    RlmChildSpawnRequest, RlmChildWaitRequest, RlmRenameRequest, RlmRenameTarget, RlmSubagentHost,
};
use eukhe_core::kernel::shared::{HostRequestHandlers, HostRequestPayload};
use eukhe_daemon::agent_messaging::LinkAgentMessageController;
use eukhe_daemon::rlm_children::{
    ParentIdentity, RlmChildIdentity as FamilyChild, SupervisorChildSessions,
};
use eukhe_daemon::supervisor_link::SupervisorLink;

#[path = "support/daemon.rs"]
mod daemon;
#[path = "support/process.rs"]
mod process;
#[path = "support/process_table.rs"]
mod process_table;
use daemon::supervisor_command;
use process::Daemon;
use process_table::process_alive;

/// Whether `pid` still holds a process-table entry. On Linux that is its
/// `/proc` entry, which a zombie keeps until its parent reaps it, so a
/// supervisor that stops reaping the workers it retires fails the waits
/// below; elsewhere the zombie-blind liveness probe answers.
fn process_present(pid: u32) -> bool {
    if cfg!(target_os = "linux") {
        Path::new(&format!("/proc/{pid}")).exists()
    } else {
        process_alive(pid)
    }
}

fn spawn_supervisor(socket: &Path, agent_dir: &Path) -> Daemon {
    let log_file = std::fs::File::create(socket.with_extension("daemon.log")).expect("log file");
    let log_err = log_file.try_clone().expect("clone log file");
    Daemon::spawn_listening(
        supervisor_command(socket, agent_dir)
            .stderr(Stdio::from(log_err))
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
        let writer = UnixStream::connect(socket).expect("connect");
        let reader = BufReader::new(writer.try_clone().expect("clone"));
        let mut client = Self { reader, writer };
        let hello = client.read_line();
        (client, hello)
    }

    fn send_command(&mut self, id: &str, command: &Value) {
        let envelope = json!({
            "type": "command",
            "id": id,
            "protocol": {"name": "eukhe.daemon", "version": 7},
            "command": command,
        });
        let mut line = serde_json::to_string(&envelope).expect("serialize");
        line.push('\n');
        self.writer.write_all(line.as_bytes()).expect("write");
        self.writer.flush().expect("flush");
    }

    fn read_line(&mut self) -> Value {
        let mut line = String::new();
        match self.reader.read_line(&mut line) {
            Ok(0) => panic!("daemon closed the socket"),
            Ok(_) => serde_json::from_str(line.trim()).expect("line json"),
            Err(error) => panic!("read failed: {error}"),
        }
    }

    fn read_response(&mut self, id: &str) -> Value {
        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            let line = self.read_line();
            if line.get("id").and_then(Value::as_str) == Some(id) {
                return line;
            }
            assert!(Instant::now() < deadline, "no response for {id}");
        }
    }
}

/// The worker's token from its persisted descriptor (the same lookup the
/// family e2e uses for the parent's token).
fn worker_token(agent_dir: &Path, active_session_id: &str) -> Option<String> {
    let instances = std::fs::read_dir(agent_dir.join("daemon-workers")).ok()?;
    for instance in instances.flatten() {
        let descriptor_path = instance.path().join(format!("{active_session_id}.json"));
        let Ok(content) = std::fs::read_to_string(&descriptor_path) else {
            continue;
        };
        let Ok(descriptor) = serde_json::from_str::<Value>(&content) else {
            continue;
        };
        if let Some(token) = descriptor
            .get("authenticationToken")
            .and_then(Value::as_str)
            .filter(|token| !token.is_empty())
        {
            return Some(token.to_string());
        }
    }
    None
}

/// The worker's pid from its persisted descriptor (the process the
/// passivation must retire).
fn worker_pid(agent_dir: &Path, active_session_id: &str) -> Option<u32> {
    let instances = std::fs::read_dir(agent_dir.join("daemon-workers")).ok()?;
    for instance in instances.flatten() {
        let descriptor_path = instance.path().join(format!("{active_session_id}.json"));
        let Ok(content) = std::fs::read_to_string(&descriptor_path) else {
            continue;
        };
        if let Ok(descriptor) = serde_json::from_str::<Value>(&content) {
            if let Some(pid) = descriptor.get("pid").and_then(Value::as_u64) {
                return u32::try_from(pid).ok();
            }
        }
    }
    None
}

fn write_faux_script(dir: &Path, name: &str, responses: &Value) -> PathBuf {
    let path = dir.join(format!("{name}.json"));
    std::fs::write(
        &path,
        json!({ "engine": "faux", "responses": responses }).to_string(),
    )
    .expect("write faux script");
    path
}

const CHILD_ID: &str = "sub-0000000a";
const CHILD_SESSION_ID: &str = "0a000000-0000-4000-8000-00000000000a";

/// Spawn the `parked-kid` child through the durable host, admit its task,
/// and long-poll it until its run settles (the parent's `eukhe.rlm.child`
/// task drives exactly these keyed calls).
async fn spawn_settled_child(children: &SupervisorChildSessions) -> RlmChildSession {
    let child = children
        .spawn(RlmChildSpawnRequest {
            idempotency_key: "rlm:1:spawn".to_string(),
            child: RlmChildIdentity {
                rlm_child_id: CHILD_ID.to_string(),
                session_id: CHILD_SESSION_ID.to_string(),
            },
            name: "parked-kid".to_string(),
            prompt: "work on the lane".to_string(),
            model: None,
            thinking: None,
            depth: 1,
            max_depth: 2,
            spawned_by_request_id: None,
            parent_task_id: "1".to_string(),
            workspace: eukhe_core::child_workspace::WorkspaceMode::Shared,
            worker: false,
        })
        .await
        .expect("spawn the child");
    children
        .prompt(RlmChildPromptRequest::task(
            "rlm:1:prompt".to_string(),
            child.session_id.clone(),
            CHILD_ID.to_string(),
            "work on the lane".to_string(),
        ))
        .await
        .expect("prompt the child");
    // The child settles done with a resident worker.
    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        let observation = children
            .wait_settled(RlmChildWaitRequest {
                session_id: child.session_id.clone(),
                rlm_child_id: CHILD_ID.to_string(),
                timeout_ms: 2_000,
            })
            .await
            .expect("wait for the child");
        match observation.state {
            RlmChildRunState::Answered { .. } => return child,
            RlmChildRunState::Failed { failure, error } => {
                panic!("the child failed ({failure}): {error}")
            }
            RlmChildRunState::Running | RlmChildRunState::Idle { .. } => {
                assert!(Instant::now() < deadline, "the child never settled done");
            }
        }
    }
}

/// A settled RLM child's whole-worker idle passivation: the stop keeps
/// the parent's roster row (done — the POSITIVE verdict), and the
/// parent's `agent_message.send` passes the kin check, WAKES a fresh
/// worker over the child's session file and delivers it labeled as the
/// parent's.
#[tokio::test]
async fn a_settled_child_passivates_stays_listable_and_revives_by_agent_message() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    let sessions_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    // The idle-eviction threshold both sides read (the worker's park arm
    // and the supervisor's fence): the same settings-driven shape the VM
    // census measures.
    std::fs::write(
        agent_dir.join("settings.json"),
        json!({ "idleEvictionMinutes": 1 }).to_string(),
    )
    .expect("write settings");

    let parent_script = write_faux_script(
        dir.path(),
        "parent",
        &json!([
            { "text": "parent turn done" },
            { "text": "parent turn done" },
        ]),
    );
    let child_script = write_faux_script(
        dir.path(),
        "child",
        &json!([{ "text": "child done" }, { "text": "revived: the child answered again" }]),
    );

    let _daemon = spawn_supervisor(&socket, &agent_dir);
    let (mut client, hello) = Client::connect(&socket);
    assert_eq!(hello["type"], "daemon_hello");

    client.send_command(
        "create-parent",
        &json!({
            "type": "create",
            "name": "parent",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": sessions_dir.to_string_lossy(),
                "script": parent_script.to_string_lossy(),
            },
        }),
    );
    let created = client.read_response("create-parent");
    assert_eq!(created["success"], true, "create parent failed: {created}");
    let parent = &created["data"];
    let parent_active_session_id = parent["activeSessionId"]
        .as_str()
        .or_else(|| parent["id"].as_str())
        .expect("parent active session id")
        .to_string();
    let parent_session_id = parent["sessionId"].as_str().expect("parent session id");
    let parent_session_file = parent["sessionFile"]
        .as_str()
        .expect("parent session file")
        .to_string();

    let link = Arc::new(SupervisorLink::new(socket.clone()));
    let children = SupervisorChildSessions::new(
        Arc::clone(&link),
        agent_dir.clone(),
        parent_active_session_id.clone(),
    );
    children.set_identity(ParentIdentity {
        rlm_depth: 0,
        rlm_max_depth: 2,
        model: Some("faux/faux-1".to_string()),
        cwd: Some(dir.path().to_string_lossy().to_string()),
        session_id: Some(parent_session_id.to_string()),
        session_file: Some(parent_session_file),
        thinking: None,
        child_script: Some(child_script.to_string_lossy().to_string()),
    });
    let child = spawn_settled_child(&children).await;
    assert_eq!(child.session_name, "parked-kid");
    let child_active_session_id = child.active_session_id.clone();
    let child_token =
        worker_token(&agent_dir, &child_active_session_id).expect("the child worker's token");
    let child_pid =
        worker_pid(&agent_dir, &child_active_session_id).expect("the child worker's pid");
    assert!(process_alive(child_pid));
    let child_alive = || process_present(child_pid);

    // THE PASSIVATION ASK: the child worker's supervisor-link request
    // (the worker-side clock and gates are unit-covered; this drives the
    // supervisor's handler, the graceful stop, and the roster passive).
    client.send_command(
        "passivate",
        &json!({
            "type": "worker_idle_passivation",
            "workerToken": child_token,
            "idleMinutes": 1,
        }),
    );
    let passivated = client.read_response("passivate");
    assert_eq!(
        passivated["success"], true,
        "the idle passivation stop must succeed: {passivated}"
    );

    // The child worker's PROCESS is GONE (TS's whole-worker eviction
    // semantics: worker AND its kernel leave; the session file stays).
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        if !child_alive() {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "the child worker process survived the passivation; process: {:?} descriptor: {} stderr: {}",
            process_table::snapshot()
                .into_iter()
                .find(|row| row.pid == child_pid),
            {
                let mut found = std::path::PathBuf::new();
                if let Ok(entries) = std::fs::read_dir(agent_dir.join("daemon-workers")) {
                    for instance in entries.flatten() {
                        let p =
                            instance.path().join(format!("{child_active_session_id}.json"));
                        if p.exists() {
                            found = p;
                        }
                    }
                }
                std::fs::read_to_string(found).unwrap_or_default()
            },
            {
                let mut tails = Vec::new();
                if let Ok(entries) = std::fs::read_dir(agent_dir.join("logs")) {
                    for entry in entries.flatten() {
                        if let Ok(content) = std::fs::read_to_string(entry.path()) {
                            tails.push(format!(
                                "{}: {}",
                                entry.path().to_string_lossy(),
                                content
                            ));
                        }
                    }
                }
                tails.join(" --- ")
            }
        );
        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    // The child's passive representation survives the stop: its display
    // entry keeps the settled (completed) verdict the parent's roster
    // hydrates from.
    let display: Value = serde_json::from_str(
        &std::fs::read_to_string(Path::new(&child.session_dir).join("rlm-subagent.json"))
            .expect("the child's display entry"),
    )
    .expect("parse the display entry");
    assert_eq!(
        display["status"], "completed",
        "the settle verdict survives the stop: {display}"
    );

    // THE REVIVAL: the parent's real `agent_message.send` to the child,
    // through the same controller and handler the worker wires: the send
    // resolves the passivated child through the family view (the durable
    // children roster, keyed by its durable id) and wakes a fresh worker
    // over the saved file (the supervisor's ledger wake). The faux engine's
    // script is spawn-time config (not session-file state), so the replayed
    // worker's turn runs the default provider: the response's outcome
    // depends on the host's credentials and is not asserted — the WAKE
    // oracle is the delivered message's row in the child's session file
    // (only a woken worker writes it); the model-answer revival is the
    // VM census's leg (the real binary against the offline mock).
    let revive_prompt = "revive: answer again";
    let parent_token =
        worker_token(&agent_dir, &parent_active_session_id).expect("the parent worker's token");
    let own_summary = json!({
        "activeSessionId": parent_active_session_id,
        "sessionId": parent_session_id,
        "sessionName": "parent",
        "runtimeKind": "top-level",
    });
    let family_child = FamilyChild {
        rlm_child_id: CHILD_ID.to_string(),
        active_session_id: child_active_session_id.clone(),
        session_id: Some(child.session_id.clone()),
        session_name: child.session_name.clone(),
    };
    children.set_durable_children_source(Arc::new(move || {
        let family_child = family_child.clone();
        Box::pin(async move { Ok(vec![family_child]) })
    }));
    let children = Arc::new(children);
    let controller = Arc::new(LinkAgentMessageController::new(
        Arc::clone(&link),
        parent_active_session_id.clone(),
        parent_token,
        Arc::new(Mutex::new(Some(own_summary))),
        Some(Arc::clone(&children)),
    ));
    let mut handlers = HostRequestHandlers::default();
    register_agent_message_host_handlers(Arc::clone(&controller) as Arc<_>, &mut handlers);
    let send = handlers.get("agent_message.send").expect("send handler");
    let revived = send(HostRequestPayload {
        data: json!({
            "message": revive_prompt,
            "receiver_role": "child",
            "receiver_name": "parked-kid",
        }),
        cell_source_code: None,
    })
    .await
    .expect("the send must wake the passivated child and deliver");
    // The send woke a fresh worker for the child's session (a new pid
    // serves the replayed session); the delivery's receipt arrives before
    // the delivered turn writes its rows, so the wake's proof is the
    // message itself landing in the child's durable storage (the revived
    // worker serves the SAME storage — its fresh routing id differs, so
    // only a woken worker writes it). The durable child session is its
    // storage directory (`<child-dir>/<session-id>/`).
    let deadline = Instant::now() + Duration::from_secs(15);
    let child_storage = Path::new(&child.session_dir).join(&child.session_id);
    loop {
        let grown = storage_text(&child_storage);
        if grown.contains(revive_prompt) {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "the send never delivered the message into the child's session ({child_storage:?}, receipt: {revived:?})"
        );
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    let delivered = storage_text(&child_storage);
    assert!(
        delivered.contains("[agent-message from parent:"),
        "the woken child reads the message as its parent's: {delivered}"
    );
}

/// A durable session's stored text: every file of its storage directory
/// (the store's commit log and its document/entry sidecars), concatenated.
fn storage_text(dir: &Path) -> String {
    let mut text = String::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(next) = pending.pop() {
        let Ok(entries) = std::fs::read_dir(&next) else {
            continue;
        };
        for entry in entries.filter_map(std::result::Result::ok) {
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

/// The root active ids of the persisted worker descriptors (the
/// descriptor file's stem is the worker's active session id).
fn root_worker_ids(agent_dir: &Path) -> Vec<String> {
    let mut ids = Vec::new();
    let Ok(instances) = std::fs::read_dir(agent_dir.join("daemon-workers")) else {
        return ids;
    };
    for instance in instances.flatten() {
        let Ok(entries) = std::fs::read_dir(instance.path()) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|ext| ext.to_str()) != Some("json") {
                continue;
            }
            let Ok(content) = std::fs::read_to_string(&path) else {
                continue;
            };
            let Ok(descriptor) = serde_json::from_str::<Value>(&content) else {
                continue;
            };
            if let Some(id) = descriptor
                .get("rootActiveSessionId")
                .and_then(Value::as_str)
                .filter(|id| !id.is_empty())
            {
                ids.push(id.to_string());
            }
        }
    }
    ids.sort();
    ids
}

/// The rename arm of the passivation-aware wake (TS
/// `renameAgentFamilySession` resolving through the hydrated target): a
/// revival re-keys the supervisor roster's child row to the revived
/// worker's fresh id, and the revived worker's own idle passivation stops
/// it again — after which only the child's DURABLE id still names the
/// session. The parent's rename addresses that durable id; the host's
/// wake launches a fresh worker over the child's session file and the
/// rename lands there.
#[tokio::test]
async fn a_parent_rename_after_a_revival_and_second_passivation_reaches_the_child() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    let sessions_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    std::fs::write(
        agent_dir.join("settings.json"),
        json!({ "idleEvictionMinutes": 1 }).to_string(),
    )
    .expect("write settings");
    let parent_script = write_faux_script(
        dir.path(),
        "rename-parent",
        &json!([{ "text": "parent turn done" }]),
    );
    let child_script = write_faux_script(
        dir.path(),
        "rename-child",
        &json!([{ "text": "child done" }]),
    );

    let _daemon = spawn_supervisor(&socket, &agent_dir);
    let (mut client, hello) = Client::connect(&socket);
    assert_eq!(hello["type"], "daemon_hello");
    client.send_command(
        "create-parent",
        &json!({
            "type": "create",
            "name": "parent",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": sessions_dir.to_string_lossy(),
                "script": parent_script.to_string_lossy(),
            },
        }),
    );
    let created = client.read_response("create-parent");
    assert_eq!(created["success"], true, "create parent failed: {created}");
    let parent = &created["data"];
    let parent_active_session_id = parent["activeSessionId"]
        .as_str()
        .or_else(|| parent["id"].as_str())
        .expect("parent active session id")
        .to_string();
    let parent_session_id = parent["sessionId"].as_str().expect("parent session id");
    let parent_session_file = parent["sessionFile"]
        .as_str()
        .expect("parent session file")
        .to_string();

    let link = Arc::new(SupervisorLink::new(socket.clone()));
    let children = SupervisorChildSessions::new(
        Arc::clone(&link),
        agent_dir.clone(),
        parent_active_session_id.clone(),
    );
    children.set_identity(ParentIdentity {
        rlm_depth: 0,
        rlm_max_depth: 2,
        model: Some("faux/faux-1".to_string()),
        cwd: Some(dir.path().to_string_lossy().to_string()),
        session_id: Some(parent_session_id.to_string()),
        session_file: Some(parent_session_file),
        thinking: None,
        child_script: Some(child_script.to_string_lossy().to_string()),
    });
    let child = spawn_settled_child(&children).await;
    let child_active_session_id = child.active_session_id.clone();
    let child_session_id = child.session_id.clone();
    // The durable child session is its storage directory
    // (`<child-dir>/<session-id>/`).
    let child_storage = std::path::Path::new(&child.session_dir).join(&child_session_id);

    // THE FIRST PASSIVATION (same ask as the settled-child test).
    let child_token =
        worker_token(&agent_dir, &child_active_session_id).expect("the child worker's token");
    client.send_command(
        "passivate-1",
        &json!({
            "type": "worker_idle_passivation",
            "workerToken": child_token,
            "idleMinutes": 1,
        }),
    );
    let passivated = client.read_response("passivate-1");
    assert_eq!(
        passivated["success"], true,
        "the first idle passivation must succeed: {passivated}"
    );

    // THE REVIVAL: a fresh client attaches by the child's DURABLE session
    // id (the TUI resume selector): the route's wake arm resolves the
    // ledger edge and launches a fresh worker over the child's file, and
    // the fresh worker's registration re-keys the roster's child row to
    // its fresh active id — the spawn-time id the parent record keeps
    // stops resolving from here on.
    let (mut fresh, _hello) = Client::connect(&socket);
    fresh.send_command(
        "revive-attach",
        &json!({ "type": "attach", "activeSessionId": child_session_id }),
    );
    let revived = fresh.read_response("revive-attach");
    assert_eq!(
        revived["success"], true,
        "the attach by the durable id must wake the passivated child: {revived}"
    );

    // The fresh worker's identity (its descriptor's root active id is the
    // new routing id the roster row now carries).
    let deadline = Instant::now() + Duration::from_secs(30);
    let revived_active_session_id = loop {
        let ids = root_worker_ids(&agent_dir)
            .into_iter()
            .filter(|id| id != &child_active_session_id && id != &parent_active_session_id)
            .collect::<Vec<_>>();
        if let Some(id) = ids.first() {
            break id.clone();
        }
        assert!(
            Instant::now() < deadline,
            "the revival never wrote a fresh worker descriptor (ids so far: {:?})",
            root_worker_ids(&agent_dir)
        );
        tokio::time::sleep(Duration::from_millis(100)).await;
    };
    let revived_token =
        worker_token(&agent_dir, &revived_active_session_id).expect("the fresh worker's token");
    let revived_pid =
        worker_pid(&agent_dir, &revived_active_session_id).expect("the fresh worker's pid");

    // THE SECOND PASSIVATION: the revived worker stops the same way, so
    // the child is passive again — but its roster row is keyed by the
    // REVIVED id, and the parent record still holds the spawn-time id.
    client.send_command(
        "passivate-2",
        &json!({
            "type": "worker_idle_passivation",
            "workerToken": revived_token,
            "idleMinutes": 1,
        }),
    );
    let passivated = client.read_response("passivate-2");
    assert_eq!(
        passivated["success"], true,
        "the second idle passivation must succeed: {passivated}"
    );
    let deadline = Instant::now() + Duration::from_secs(60);
    while process_present(revived_pid) {
        assert!(
            Instant::now() < deadline,
            "the revived worker survived the second passivation"
        );
        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    // THE RENAME: the parent's rename addresses the child by its durable
    // session id while no worker hosts it; the host's durable-selector
    // wake must land the rename on a fresh worker over the child's
    // session file.
    children
        .rename(RlmRenameRequest {
            name: "renamed-lane".to_string(),
            target: RlmRenameTarget::Child {
                session_id: child_session_id.clone(),
            },
        })
        .await
        .unwrap_or_else(|error| {
            panic!(
                "the parent rename of the twice-passivated child must reach it through the durable wake: {error:#}"
            )
        });

    // The durable oracle: the child's session carries the new name (its
    // session document's `name`, written only by a woken worker).
    let entries = storage_text(&child_storage);
    assert!(
        entries.contains("\"renamed-lane\""),
        "the woken child must carry the renamed session name ({child_storage:?})"
    );
}

/// An idle unowned ROOT passivates through the same worker-driven ask
/// (TS `canEvictWorker` reaches roots and children alike) and resumes
/// by its durable session id: the attach wakes a fresh worker over the
/// saved file and the snapshot carries the pre-passivation transcript.
#[tokio::test]
async fn an_idle_root_passivates_and_resumes_by_its_durable_id_with_its_transcript() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    let sessions_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    std::fs::write(
        agent_dir.join("settings.json"),
        json!({ "idleEvictionMinutes": 1 }).to_string(),
    )
    .expect("write settings");
    let root_script = write_faux_script(dir.path(), "root", &json!([{ "text": "root turn done" }]));

    let _daemon = spawn_supervisor(&socket, &agent_dir);
    let (mut client, hello) = Client::connect(&socket);
    assert_eq!(hello["type"], "daemon_hello");

    client.send_command(
        "create-root",
        &json!({
            "type": "create",
            "name": "root",
            "config": {
                "cwd": dir.path().to_string_lossy(),
                "sessionDir": sessions_dir.to_string_lossy(),
                "script": root_script.to_string_lossy(),
            },
        }),
    );
    let created = client.read_response("create-root");
    assert_eq!(created["success"], true, "create root failed: {created}");
    let root_active_session_id = created["data"]["activeSessionId"]
        .as_str()
        .or_else(|| created["data"]["id"].as_str())
        .expect("root active session id")
        .to_string();
    let root_session_id = created["data"]["sessionId"]
        .as_str()
        .expect("root durable session id")
        .to_string();

    client.send_command(
        "first-turn",
        &json!({
            "type": "prompt_and_wait",
            "activeSessionId": root_active_session_id,
            "message": "first turn",
        }),
    );
    let first = client.read_response("first-turn");
    assert_eq!(first["success"], true, "the first turn failed: {first}");

    let root_token =
        worker_token(&agent_dir, &root_active_session_id).expect("the root worker's token");
    let root_pid = worker_pid(&agent_dir, &root_active_session_id).expect("the root worker's pid");
    assert!(process_alive(root_pid));

    // THE PASSIVATION ASK for a ROOT: the supervisor's handler accepts an
    // unowned worker regardless of depth (without the fix this answers
    // the child-worker-policy refusal).
    client.send_command(
        "passivate-root",
        &json!({
            "type": "worker_idle_passivation",
            "workerToken": root_token,
            "idleMinutes": 1,
        }),
    );
    let passivated = client.read_response("passivate-root");
    assert_eq!(
        passivated["success"], true,
        "the root's idle passivation must succeed: {passivated}"
    );

    // The root worker's process is gone (the whole-worker stop).
    let deadline = Instant::now() + Duration::from_secs(60);
    while process_present(root_pid) {
        assert!(
            Instant::now() < deadline,
            "the root worker process survived the passivation"
        );
        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    // THE RESUME: a fresh client attaches by the DURABLE session id (the
    // TUI reattach selector); the route's wake arm resolves the saved
    // session, launches a fresh worker over the file, and the snapshot
    // carries the pre-passivation transcript.
    let (mut fresh, _hello) = Client::connect(&socket);
    fresh.send_command(
        "re-attach",
        &json!({ "type": "attach", "activeSessionId": root_session_id }),
    );
    let attached = fresh.read_response("re-attach");
    assert_eq!(
        attached["success"], true,
        "the attach by the durable id must wake the passivated root: {attached}"
    );
    let messages = attached["data"]["snapshot"]["messages"].to_string();
    assert!(
        messages.contains("first turn"),
        "the snapshot must carry the first turn's user prompt: {messages}"
    );
    assert!(
        messages.contains("root turn done"),
        "the snapshot must carry the first turn's reply: {messages}"
    );
}

/// Create a root session over the faux `script` and attach `client` to
/// it; answers its active and durable ids.
fn create_attached(
    client: &mut Client,
    name: &str,
    dir: &Path,
    sessions_dir: &Path,
    script: &Path,
) -> (String, String) {
    let id = format!("create-{name}");
    client.send_command(
        &id,
        &json!({
            "type": "create",
            "name": name,
            "config": {
                "cwd": dir.to_string_lossy(),
                "sessionDir": sessions_dir.to_string_lossy(),
                "script": script.to_string_lossy(),
            },
        }),
    );
    let created = client.read_response(&id);
    assert_eq!(created["success"], true, "create {name} failed: {created}");
    let active = created["data"]["activeSessionId"]
        .as_str()
        .expect("active session id")
        .to_string();
    let durable = created["data"]["sessionId"]
        .as_str()
        .expect("durable session id")
        .to_string();
    let id = format!("attach-{name}");
    client.send_command(&id, &json!({ "type": "attach", "activeSessionId": active }));
    let attached = client.read_response(&id);
    assert_eq!(
        attached["success"], true,
        "attach {name} failed: {attached}"
    );
    (active, durable)
}

/// Wait until `pid` left the process table, at most `budget`.
async fn wait_gone(pid: u32, budget: Duration, what: &str) {
    let deadline = Instant::now() + budget;
    while process_present(pid) {
        assert!(Instant::now() < deadline, "{what}: worker {pid} still runs");
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
}

/// F5: a root its client left for another session (`/new`, `/resume`: a
/// `detach` with reason `switch`) releases its worker once idle after the
/// left grace, not after the 90-minute idle threshold (omp disposes the
/// session it leaves), and resumes by its durable id with its transcript.
/// A left root with a turn in flight keeps its worker until the turn ends.
#[tokio::test]
async fn a_root_left_for_another_session_releases_its_worker_once_idle() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    let sessions_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    let hold = dir.path().join("hold.sock");
    let listener = std::os::unix::net::UnixListener::bind(&hold).expect("bind the hold socket");
    let left_script = write_faux_script(dir.path(), "left", &json!([{ "text": "left turn done" }]));
    let busy_script = write_faux_script(
        dir.path(),
        "busy",
        &json!([{ "text": "busy turn done", "holdUntilReleased": hold.to_string_lossy() }]),
    );
    let next_script = write_faux_script(dir.path(), "next", &json!([{ "text": "next" }]));

    let _daemon = spawn_supervisor(&socket, &agent_dir);
    let (mut client, _hello) = Client::connect(&socket);
    let (left, left_durable) =
        create_attached(&mut client, "left", dir.path(), &sessions_dir, &left_script);
    client.send_command(
        "left-turn",
        &json!({ "type": "prompt_and_wait", "activeSessionId": left, "message": "first turn" }),
    );
    let turn = client.read_response("left-turn");
    assert_eq!(turn["success"], true, "the left session's turn: {turn}");
    let (busy, _) = create_attached(&mut client, "busy", dir.path(), &sessions_dir, &busy_script);
    client.send_command(
        "busy-turn",
        &json!({ "type": "prompt", "activeSessionId": busy, "message": "busy turn" }),
    );
    // The busy turn's model request holds until the test closes its
    // connection.
    let (release, released) = std::sync::mpsc::channel::<()>();
    let provider_peer = std::thread::spawn(move || {
        let (connection, _) = listener.accept().expect("the held request connects");
        let _ = released.recv();
        drop(connection);
    });
    // A session left before its first prompt (each `/new` of a `/new`
    // spam): its window armed at create, before the attach.
    let (draft, _) = create_attached(
        &mut client,
        "draft",
        dir.path(),
        &sessions_dir,
        &next_script,
    );
    let (next, _) = create_attached(&mut client, "next", dir.path(), &sessions_dir, &next_script);
    let left_pid = worker_pid(&agent_dir, &left).expect("the left worker's pid");
    let busy_pid = worker_pid(&agent_dir, &busy).expect("the busy worker's pid");
    let draft_pid = worker_pid(&agent_dir, &draft).expect("the draft worker's pid");
    let next_pid = worker_pid(&agent_dir, &next).expect("the next worker's pid");

    // The client moves on (the TUI's `/new`): the earlier sessions left.
    let left_at = Instant::now();
    for (id, session) in [
        ("leave-left", &left),
        ("leave-busy", &busy),
        ("leave-draft", &draft),
    ] {
        client.send_command(
            id,
            &json!({ "type": "detach", "activeSessionId": session, "reason": "switch" }),
        );
        let detached = client.read_response(id);
        assert_eq!(detached["success"], true, "{id}: {detached}");
    }
    wait_gone(left_pid, Duration::from_secs(120), "the idle left session").await;
    wait_gone(
        draft_pid,
        Duration::from_secs(120),
        "the left draft session",
    )
    .await;
    // Past the grace, the left session with a turn in flight keeps its
    // worker: an absence the test can only observe by waiting the grace
    // out (30 s) and a margin.
    tokio::time::sleep(
        (left_at + Duration::from_secs(35)).saturating_duration_since(Instant::now()),
    )
    .await;
    assert!(
        process_present(busy_pid),
        "a left session with work keeps its worker"
    );
    release.send(()).expect("release the held request");
    provider_peer.join().expect("the hold thread");
    wait_gone(
        busy_pid,
        Duration::from_secs(120),
        "the left session after its turn",
    )
    .await;
    assert!(
        process_present(next_pid),
        "the attached session keeps its worker"
    );

    // The left session resumes by its durable id with its transcript.
    let (mut fresh, _hello) = Client::connect(&socket);
    fresh.send_command(
        "resume-left",
        &json!({ "type": "attach", "activeSessionId": left_durable }),
    );
    let attached = fresh.read_response("resume-left");
    assert_eq!(
        attached["success"], true,
        "resume the left session: {attached}"
    );
    let messages = attached["data"]["snapshot"]["messages"].to_string();
    assert!(
        messages.contains("first turn") && messages.contains("left turn done"),
        "the resumed snapshot carries the left session's turn: {messages}"
    );
}
