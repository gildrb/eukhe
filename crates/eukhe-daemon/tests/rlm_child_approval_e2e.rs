//! End-to-end: a subagent's gated step asks the user of its root session. A subagent session has no client of its own; its
//! `bash` step that writes (outside the user's auto set, narrowed here to
//! `read`) hands the question up to its root through the supervisor, the
//! root's attached client gets the `shell_approval` frame naming the
//! subagent, and its approval lets the step run.
#![cfg(unix)]

use std::io::{BufRead, BufReader, Write};
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

const CHILD_ID: &str = "sub-0000000b";
const CHILD_SESSION_ID: &str = "0b000000-0000-4000-8000-00000000000b";

/// A JSONL supervisor client: the user's client attached to the root.
struct Client {
    reader: BufReader<UnixStream>,
    writer: UnixStream,
}

impl Client {
    fn connect(socket: &Path) -> Self {
        let stream = UnixStream::connect(socket).expect("connect supervisor");
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

    fn send(&mut self, id: &str, command: &Value) {
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

    /// The first line `wanted` accepts, within `budget`.
    fn until(&mut self, budget: Duration, wanted: impl Fn(&Value) -> bool) -> Value {
        let deadline = Instant::now() + budget;
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            assert!(!remaining.is_zero(), "the awaited line never came");
            let line = self.next_line(remaining);
            if wanted(&line) {
                return line;
            }
        }
    }

    fn request(&mut self, id: &str, command: &Value) -> Value {
        self.send(id, command);
        self.until(Duration::from_secs(60), |line| line["id"] == id)
    }
}

/// A scripted-model script file.
fn script(path: &Path, responses: &Value) -> String {
    std::fs::write(path, json!({ "responses": responses }).to_string()).expect("write script");
    path.to_string_lossy().into_owned()
}

/// Regression (G5): a subagent's gated step was denied unasked, since the
/// subagent's own session has no client; the root's user could not answer.
#[tokio::test(flavor = "multi_thread")]
// One end-to-end story (root, subagent, question, answer, settle) reads
// best as one body.
#[allow(clippy::too_many_lines)]
async fn a_subagent_step_runs_when_the_root_client_approves() {
    let dir = tempfile::TempDir::new().expect("temp dir");
    let socket = dir.path().join("daemon.sock");
    let agent_dir = dir.path().join("agent");
    let work = dir.path().join("work");
    std::fs::create_dir_all(&agent_dir).expect("agent dir");
    std::fs::create_dir_all(&work).expect("work dir");
    std::fs::write(
        agent_dir.join("settings.json"),
        json!({ "shell": { "autoEffects": ["read"] } }).to_string(),
    )
    .expect("write settings");
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
    let root_session_id = field("sessionId");
    let root_session_file = field("sessionFile");
    let attached = user.request(
        "a1",
        &json!({ "type": "attach", "activeSessionId": root_id }),
    );
    assert_eq!(attached["success"], true, "attach: {attached}");

    // The root's subagent `scout`: its model runs one bash step that
    // writes, then answers.
    let children =
        SupervisorChildSessions::new(Arc::clone(&link), agent_dir.clone(), root_id.clone());
    children.set_identity(ParentIdentity {
        rlm_depth: 0,
        rlm_max_depth: 2,
        model: Some("scripted/faux-1".to_string()),
        cwd: Some(work.to_string_lossy().into_owned()),
        session_id: Some(root_session_id),
        session_file: Some(root_session_file),
        thinking: None,
        child_script: Some(script(
            &dir.path().join("child.json"),
            &json!([
                { "content": [{
                    "type": "toolCall",
                    "id": "call-1",
                    "name": "bash",
                    "arguments": { "script": "touch marker.txt" },
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
            prompt: "make the marker".to_string(),
            model: None,
            thinking: None,
            depth: 1,
            max_depth: 2,
            spawned_by_request_id: None,
            parent_task_id: "1".to_string(),
            workspace: eukhe_core::child_workspace::WorkspaceMode::Shared,
        })
        .await
        .expect("spawn the subagent");
    children
        .prompt(RlmChildPromptRequest {
            idempotency_key: "rlm:1:prompt".to_string(),
            session_id: CHILD_SESSION_ID.to_string(),
            rlm_child_id: CHILD_ID.to_string(),
            prompt: "make the marker".to_string(),
        })
        .await
        .expect("prompt the subagent");

    // The question reaches the root's client, naming the subagent.
    let mut question = user.until(Duration::from_secs(90), |line| {
        line["type"] == "shell_approval"
    });
    let request_id = question["request"]["requestId"].clone();
    assert!(request_id.is_string(), "{question}");
    question["request"]["requestId"] = Value::Null;
    assert_eq!(
        question,
        json!({
            "type": "shell_approval",
            "activeSessionId": root_id,
            "request": {
                "requestId": null,
                "step": 0,
                "command": "touch marker.txt",
                "effects": ["write"],
            },
            "agent": "scout",
        })
    );
    let answered = user.request(
        "y1",
        &json!({
            "type": "answer_shell_approval",
            "activeSessionId": root_id,
            "requestId": request_id,
            "verdict": "approve",
        }),
    );
    assert_eq!(answered["success"], true, "answer: {answered}");

    // The approved step ran, and the subagent finished.
    let deadline = Instant::now() + Duration::from_secs(60);
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
    assert_eq!(
        settled,
        RlmChildRunState::Answered {
            answer_preview: Some("done".to_string()),
        }
    );
    assert!(work.join("marker.txt").is_file(), "the approved step ran");
}
