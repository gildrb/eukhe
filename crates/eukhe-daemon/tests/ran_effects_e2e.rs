//! End-to-end: a subagent's irreversible effect lands in its root's
//! ledger, naming the subagent (spec I5). A subagent session has a ledger
//! of its own no one reads; its `bash` step that talks to a host runs
//! unasked and goes up to the root through the supervisor
//! (`relay_ran_effect`), and the root's `get_ran_effects` lists it.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Read, Write};
use std::net::TcpListener;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant};

use eukhe_core::durable::children::{
    RlmChildIdentity, RlmChildPromptRequest, RlmChildRunState, RlmChildSpawnRequest,
    RlmChildWaitRequest, RlmSubagentHost,
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

const CHILD_ID: &str = "sub-0000000c";
const CHILD_SESSION_ID: &str = "0c000000-0000-4000-8000-00000000000c";

/// A JSONL supervisor client: the user's client attached to the root.
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> Self {
        let stream =
            eukhe_types::platform::transport::connect_std(socket).expect("connect supervisor");
        stream
            .set_read_timeout(Some(Duration::from_millis(100)))
            .expect("set timeout");
        let writer = stream.try_clone().expect("clone socket");
        let mut client = Client {
            reader: BufReader::new(stream),
            writer,
        };
        let hello = client.next_line(Duration::from_secs(10));
        assert_eq!(hello["type"], "daemon_hello", "{hello}");
        client
    }

    /// The next line within `budget`.
    fn next_line(&mut self, budget: Duration) -> Value {
        let deadline = Instant::now() + budget;
        let mut line = String::new();
        loop {
            match self.reader.read_line(&mut line) {
                Ok(0) => panic!("the supervisor closed the connection"),
                Ok(_) if line.trim().is_empty() => line.clear(),
                Ok(_) => return serde_json::from_str(line.trim()).expect("a JSON line"),
                Err(error) => assert!(
                    Instant::now() < deadline,
                    "no line within {budget:?}: {error}"
                ),
            }
        }
    }

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
        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            assert!(!remaining.is_zero(), "no response to {id}");
            let line = self.next_line(remaining);
            if line["id"] == id {
                return line;
            }
        }
    }
}

/// A scripted-model script file.
fn script(path: &Path, responses: &Value) -> String {
    std::fs::write(path, json!({ "responses": responses }).to_string()).expect("write script");
    path.to_string_lossy().into_owned()
}

/// A host on a loopback port that answers every request `200 OK`.
fn host() -> u16 {
    let listener = TcpListener::bind("127.0.0.1:0").expect("the host");
    let port = listener.local_addr().expect("the host's port").port();
    std::thread::spawn(move || {
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { continue };
            let mut request = [0_u8; 4096];
            let _ = stream.read(&mut request);
            let _ = stream.write_all(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok");
        }
    });
    port
}

#[tokio::test(flavor = "multi_thread")]
// One end-to-end story (root, subagent, step, ledger) reads best as one
// body.
#[allow(clippy::too_many_lines)]
async fn a_subagent_effect_lands_in_the_root_ledger_naming_the_subagent() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    let work = dir.path().join("work");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    std::fs::create_dir_all(&work).expect("work dir");
    let port = host();
    let command = format!("curl -s http://127.0.0.1:{port}/sub");
    let _daemon = Daemon::spawn_bound(
        supervisor_command(&socket, &agent_dir).env(
            eukhe_daemon::worker::WORKER_SUPERVISOR_LOST_EXIT_MS_ENV,
            "15000",
        ),
        &socket,
        Duration::from_secs(10),
    );
    let link = Arc::new(SupervisorLink::new(socket.clone()));

    // The root: a top-level session the user's client attaches to.
    let sessions_dir = agent_dir.join("sessions");
    std::fs::create_dir_all(&sessions_dir).expect("sessions dir");
    let mut user = Client::connect(&socket);
    let created = user.request(
        "c1",
        &json!({
            "type": "create",
            "name": "root",
            "config": {
                "cwd": work.to_string_lossy(),
                "sessionDir": sessions_dir.to_string_lossy(),
                "script": script(&dir.path().join("root.json"), &json!(["root here"])),
            },
        }),
    );
    assert_eq!(created["success"], true, "create: {created}");
    let field = |key: &str| {
        created["data"][key]
            .as_str()
            .unwrap_or_else(|| panic!("create answers {key}: {created}"))
            .to_string()
    };
    let root_id = field("activeSessionId");
    let attached = user.request(
        "a1",
        &json!({ "type": "attach", "activeSessionId": root_id }),
    );
    assert_eq!(attached["success"], true, "attach: {attached}");

    // The root's subagent `scout`: its model runs one step that talks to
    // the host, then answers.
    let children =
        SupervisorChildSessions::new(Arc::clone(&link), agent_dir.clone(), root_id.clone());
    children.set_identity(ParentIdentity {
        rlm_depth: 0,
        rlm_max_depth: 2,
        model: Some("scripted/faux-1".to_string()),
        cwd: Some(work.to_string_lossy().into_owned()),
        session_id: Some(field("sessionId")),
        session_file: Some(field("sessionFile")),
        thinking: None,
        child_script: Some(script(
            &dir.path().join("child.json"),
            &json!([
                { "content": [{
                    "type": "toolCall",
                    "id": "call-1",
                    "name": "bash",
                    "arguments": { "script": command },
                }] },
                "done",
            ]),
        )),
    });
    children
        .spawn(RlmChildSpawnRequest {
            idempotency_key: "rlm:1:spawn".to_string(),
            child: RlmChildIdentity {
                rlm_child_id: CHILD_ID.to_string(),
                session_id: CHILD_SESSION_ID.to_string(),
            },
            name: "scout".to_string(),
            prompt: "ping the host".to_string(),
            model: None,
            thinking: None,
            depth: 1,
            max_depth: 2,
            spawned_by_request_id: None,
            parent_task_id: "1".to_string(),
            workspace: eukhe_core::child_workspace::WorkspaceMode::Shared,
            worker: false,
            acceptance: None,
            tree: None,
        })
        .await
        .expect("spawn the subagent");
    children
        .prompt(RlmChildPromptRequest::task(
            "rlm:1:prompt".to_string(),
            CHILD_SESSION_ID.to_string(),
            CHILD_ID.to_string(),
            "ping the host".to_string(),
        ))
        .await
        .expect("prompt the subagent");
    let deadline = Instant::now() + Duration::from_secs(90);
    let settled = loop {
        let observation = children
            .wait_settled(RlmChildWaitRequest {
                session_id: CHILD_SESSION_ID.to_string(),
                rlm_child_id: CHILD_ID.to_string(),
                timeout_ms: 2_000,
            })
            .await
            .expect("wait for the subagent");
        match observation.state {
            RlmChildRunState::Running | RlmChildRunState::Idle { .. } => {
                assert!(Instant::now() < deadline, "the subagent never settled");
            }
            state @ (RlmChildRunState::Answered { .. } | RlmChildRunState::Failed { .. }) => {
                break state;
            }
        }
    };

    // The step ran unasked; the root's ledger holds it once, naming the
    // subagent. The root is idle (no run yet): the effect goes to its next
    // run (1), whose report lists it.
    let listed = user.request(
        "l1",
        &json!({ "type": "get_ran_effects", "activeSessionId": root_id }),
    );
    assert_eq!(listed["success"], true, "get_ran_effects: {listed}");
    let mut effects = listed["data"]["effects"].clone();
    let at_ms = effects[0]["atMs"].take();
    assert!(at_ms.is_u64(), "{listed}");
    assert_eq!(
        (settled, effects),
        (
            RlmChildRunState::Answered {
                answer_preview: Some("done".to_string()),
            },
            json!([{
                "id": "e1",
                "key": format!("{CHILD_SESSION_ID}:call-1:0"),
                "run": 1,
                "kind": "shellStep",
                "command": command,
                "classes": ["net"],
                "agent": "scout",
                "sessionId": CHILD_SESSION_ID,
                "atMs": null,
            }]),
        )
    );
}
