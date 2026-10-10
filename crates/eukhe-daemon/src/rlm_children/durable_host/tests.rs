//! The durable child host against a recording fake supervisor: keyed calls
//! run once, a spawn creates under the requested id and finds a resident
//! child again after a parent restart, a settled child reports its answer,
//! reply flag, and usage, the task prompt lands as the parent's spawn
//! kickoff row, and `rlm.rename` routes self and child renames.

use std::sync::{Arc, Mutex};

use eukhe_core::durable::children::{
    RlmChildCancelRequest, RlmChildDeleteRequest, RlmChildIdentity, RlmChildPromptRequest,
    RlmChildRunState, RlmChildSpawnRequest, RlmChildWaitRequest, RlmRenameRequest, RlmRenameTarget,
    RlmSubagentHost,
};
use eukhe_types::platform::transport::bind_transport;
use serde_json::{json, Value};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

use super::super::{ParentIdentity, SupervisorChildSessions};
use crate::protocol::{response_failure, response_success};

const CHILD_SESSION: &str = "0192a000-0000-7000-8000-00000000c001";

/// What the fake supervisor saw, and the resident sessions it lists.
#[derive(Default)]
struct Supervisor {
    commands: Vec<Value>,
    resident: Vec<Value>,
}

type Shared = Arc<Mutex<Supervisor>>;

fn lock(shared: &Shared) -> std::sync::MutexGuard<'_, Supervisor> {
    shared
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

fn answer(shared: &Shared, id: &str, command: &Value) -> crate::protocol::DaemonResponse {
    let command_type = command["type"].as_str().unwrap_or_default();
    lock(shared).commands.push(command.clone());
    match command_type {
        "list" => {
            let sessions = lock(shared).resident.clone();
            response_success(
                Some(id),
                command_type,
                Some(json!({ "sessions": sessions })),
            )
        }
        "create" => response_success(
            Some(id),
            command_type,
            Some(json!({
                "activeSessionId": "child-live",
                "sessionId": command["config"]["sessionId"],
                "sessionName": command["name"],
            })),
        ),
        "kill" if command["activeSessionId"] == "gone" => {
            response_failure(Some(id), command_type, "Unknown active session: gone", None)
        }
        // A passivated child's spawn-time routing id resolves nowhere; its
        // durable session id wakes it.
        "rename" if command["activeSessionId"] == "child-passivated" => response_failure(
            Some(id),
            command_type,
            "Unknown active session: child-passivated",
            None,
        ),
        "prompt" | "wait_for_idle" | "abort" | "kill" | "rename" => {
            response_success(Some(id), command_type, None)
        }
        "get_state" => response_success(
            Some(id),
            command_type,
            Some(json!({ "isStreaming": false, "sessionActions": { "queuedCount": 0 } })),
        ),
        "get_last_assistant_text" => response_success(
            Some(id),
            command_type,
            Some(json!({ "text": "the child final answer" })),
        ),
        "get_session_stats" => response_success(
            Some(id),
            command_type,
            Some(json!({
                "tokens": { "input": 10, "output": 5, "cacheRead": 0, "cacheWrite": 0, "total": 15 },
                "cost": 0.25,
            })),
        ),
        other => response_failure(Some(id), other, "unexpected command", None),
    }
}

async fn fake_supervisor(shared: Shared) -> std::path::PathBuf {
    let socket = std::env::temp_dir().join(format!(
        "eukhe-durable-host-{}.sock",
        uuid::Uuid::new_v4().simple()
    ));
    let listener = bind_transport(&socket).await.unwrap();
    tokio::spawn(async move {
        while let Ok(stream) = listener.accept().await {
            let shared = Arc::clone(&shared);
            tokio::spawn(async move {
                let (reader, mut writer) = stream.split();
                let mut reader = BufReader::new(reader);
                writer
                    .write_all(
                        b"{\"type\":\"daemon_hello\",\"protocol\":{\"name\":\"eukhe.daemon\",\"version\":7}}\n",
                    )
                    .await
                    .unwrap();
                loop {
                    let mut line = String::new();
                    if reader.read_line(&mut line).await.unwrap_or(0) == 0 {
                        return;
                    }
                    let value: Value = serde_json::from_str(line.trim()).unwrap();
                    let id = value["id"].as_str().unwrap_or_default().to_owned();
                    let response = answer(&shared, &id, &value["command"]);
                    let mut line = serde_json::to_string(&response).unwrap();
                    line.push('\n');
                    if writer.write_all(line.as_bytes()).await.is_err() {
                        return;
                    }
                }
            });
        }
    });
    socket
}

async fn host(shared: &Shared, agent_dir: &std::path::Path) -> SupervisorChildSessions {
    let socket = fake_supervisor(Arc::clone(shared)).await;
    let sessions = SupervisorChildSessions::new(
        Arc::new(crate::supervisor_link::SupervisorLink::new(socket)),
        agent_dir.to_path_buf(),
        "parent-live".to_owned(),
        Arc::new(crate::model_allowlist::ModelRefusalTelemetry::new(
            agent_dir.to_path_buf(),
            /*telemetry_disabled*/ true,
        )),
    );
    sessions.set_identity(ParentIdentity {
        model: Some("mock/mock-1".to_owned()),
        cwd: Some(agent_dir.to_string_lossy().into_owned()),
        session_id: Some("parent-session".to_owned()),
        ..ParentIdentity::with_default_depth()
    });
    sessions
}

fn spawn_request() -> RlmChildSpawnRequest {
    RlmChildSpawnRequest {
        idempotency_key: "rlm:7:spawn".to_owned(),
        child: RlmChildIdentity {
            rlm_child_id: "sub-0192a000".to_owned(),
            session_id: CHILD_SESSION.to_owned(),
        },
        name: "worker-a".to_owned(),
        prompt: "Investigate".to_owned(),
        model: None,
        thinking: None,
        depth: 1,
        max_depth: 3,
        spawned_by_request_id: Some("call-1".to_owned()),
        parent_task_id: "7".to_owned(),
    }
}

fn commands_of(shared: &Shared, command_type: &str) -> Vec<Value> {
    lock(shared)
        .commands
        .iter()
        .filter(|command| command["type"] == command_type)
        .cloned()
        .collect()
}

#[tokio::test]
async fn spawn_creates_once_under_the_requested_session_id() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    let sessions = host(&shared, dir.path()).await;
    let first = sessions.spawn(spawn_request()).await.unwrap();
    let again = sessions.spawn(spawn_request()).await.unwrap();
    assert_eq!(first, again);
    assert_eq!(first.active_session_id, "child-live");
    assert_eq!(first.session_id, CHILD_SESSION);
    assert_eq!(first.session_name, "worker-a");
    let creates = commands_of(&shared, "create");
    assert_eq!(creates.len(), 1);
    assert_eq!(creates[0]["config"]["sessionId"], CHILD_SESSION);
    assert_eq!(creates[0]["config"]["rlmDepth"], 1);
    assert_eq!(creates[0]["config"]["rlmMaxDepth"], 3);
    assert_eq!(creates[0]["config"]["spawnedByRequestId"], "call-1");
}

#[tokio::test]
async fn a_restarted_parent_finds_its_resident_child() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    lock(&shared).resident.push(json!({
        "activeSessionId": "child-still-live",
        "sessionId": CHILD_SESSION,
        "sessionName": "worker-a",
    }));
    let sessions = host(&shared, dir.path()).await;
    let child = sessions.spawn(spawn_request()).await.unwrap();
    assert_eq!(child.active_session_id, "child-still-live");
    assert!(commands_of(&shared, "create").is_empty());
}

#[tokio::test]
async fn keyed_calls_run_once_and_a_settled_child_reports() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    let sessions = host(&shared, dir.path()).await;
    sessions.spawn(spawn_request()).await.unwrap();

    let prompt = RlmChildPromptRequest {
        idempotency_key: "rlm:7:prompt".to_owned(),
        session_id: CHILD_SESSION.to_owned(),
        rlm_child_id: "sub-0192a000".to_owned(),
        prompt: "Investigate".to_owned(),
    };
    sessions.prompt(prompt.clone()).await.unwrap();
    sessions.prompt(prompt).await.unwrap();
    let prompts = commands_of(&shared, "prompt");
    assert_eq!(prompts.len(), 1);
    assert_eq!(prompts[0]["activeSessionId"], "child-live");
    assert_eq!(prompts[0]["admissionId"], "rlm:7:prompt");

    sessions.mark_durable_child_replied("child-live");
    let observed = sessions
        .wait_settled(RlmChildWaitRequest {
            session_id: CHILD_SESSION.to_owned(),
            timeout_ms: 10,
        })
        .await
        .unwrap();
    assert_eq!(
        observed.state,
        RlmChildRunState::Settled {
            answer_preview: Some("the child final answer".to_owned()),
            replied_since_task: true,
        }
    );
    let usage = observed.usage.unwrap();
    assert_eq!((usage.input, usage.output, usage.total_tokens), (10, 5, 15));
    assert!((usage.cost.total - 0.25).abs() < f64::EPSILON);

    let cancel = RlmChildCancelRequest {
        idempotency_key: "rlm:7:cancel".to_owned(),
        session_id: CHILD_SESSION.to_owned(),
    };
    sessions.cancel(cancel.clone()).await.unwrap();
    sessions.cancel(cancel).await.unwrap();
    assert_eq!(commands_of(&shared, "abort").len(), 1);

    let delete = RlmChildDeleteRequest {
        idempotency_key: "rlm:7:delete".to_owned(),
        session_id: CHILD_SESSION.to_owned(),
        rlm_child_id: "sub-0192a000".to_owned(),
    };
    sessions.delete(delete.clone()).await.unwrap();
    sessions.delete(delete).await.unwrap();
    let kills = commands_of(&shared, "kill");
    assert_eq!(kills.len(), 1);
    assert_eq!(kills[0]["rlmLedgerDelete"], "user");
    assert_eq!(kills[0]["rlmChildId"], "sub-0192a000");
}

#[tokio::test]
async fn deleting_a_child_no_worker_answers_is_a_no_op() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    let sessions = host(&shared, dir.path()).await;
    sessions
        .delete(RlmChildDeleteRequest {
            idempotency_key: "rlm:9:delete".to_owned(),
            session_id: "gone".to_owned(),
            rlm_child_id: "sub-gone".to_owned(),
        })
        .await
        .unwrap();
}

/// TS `spawnMessage`: the task prompt is admitted as the parent's
/// `agent_message` row (`details.id` `spawn:<child id>`, the raw prompt as
/// `details.message`, the parent endpoint with its live name, no `target`),
/// and the model context is the `[task from parent]`-labeled task.
#[tokio::test]
async fn the_task_prompt_lands_as_the_parents_spawn_kickoff() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    let sessions = host(&shared, dir.path()).await;
    sessions.set_parent_name_source(Arc::new(|| Some("orchestrator".to_owned())));
    sessions.spawn(spawn_request()).await.unwrap();
    sessions
        .prompt(RlmChildPromptRequest {
            idempotency_key: "rlm:7:prompt".to_owned(),
            session_id: CHILD_SESSION.to_owned(),
            rlm_child_id: "sub-0192a000".to_owned(),
            prompt: "Investigate".to_owned(),
        })
        .await
        .unwrap();
    let prompts = commands_of(&shared, "prompt");
    let [prompt] = prompts.as_slice() else {
        panic!("one prompt: {prompts:?}");
    };
    assert_eq!(prompt["message"], "[task from parent]\n\nInvestigate");
    let row = &prompt["customMessage"];
    assert_eq!(row["role"], "custom");
    assert_eq!(row["customType"], "agent_message");
    assert_eq!(row["content"], "[task from parent]\n\nInvestigate");
    assert_eq!(row["display"], true);
    assert_eq!(
        row["details"],
        json!({
            "id": "spawn:sub-0192a000",
            "message": "Investigate",
            "from": {
                "activeSessionId": "parent-live",
                "sessionId": "parent-session",
                "sessionName": "orchestrator",
            },
            "fromRelationship": "parent",
        })
    );
}

/// `rlm.rename` over the supervisor: a self rename addresses this worker's
/// own routing id (by an absent selector or the routing id itself) without
/// a parent marker, a foreign selector is refused, and a child rename
/// carries `renamedBy: "parent"`, waking a passivated child by its durable
/// session id.
#[tokio::test]
async fn rename_routes_self_and_child_renames_through_the_supervisor() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    lock(&shared).resident.push(json!({
        "activeSessionId": "child-passivated",
        "sessionId": CHILD_SESSION,
        "sessionName": "worker-a",
    }));
    let sessions = host(&shared, dir.path()).await;
    sessions.spawn(spawn_request()).await.unwrap();

    for selector in [None, Some("parent-live".to_owned())] {
        sessions
            .rename(RlmRenameRequest {
                name: "lead".to_owned(),
                target: RlmRenameTarget::Session { selector },
            })
            .await
            .unwrap();
    }
    let refused = sessions
        .rename(RlmRenameRequest {
            name: "lead".to_owned(),
            target: RlmRenameTarget::Session {
                selector: Some("someone-else".to_owned()),
            },
        })
        .await
        .unwrap_err();
    assert_eq!(
        refused.to_string(),
        "rlm.rename can only rename the current session or one of its direct children"
    );
    sessions
        .rename(RlmRenameRequest {
            name: "bench-runner".to_owned(),
            target: RlmRenameTarget::Child {
                session_id: CHILD_SESSION.to_owned(),
            },
        })
        .await
        .unwrap();

    let renames = commands_of(&shared, "rename");
    let routed: Vec<(&str, &str, Option<&str>)> = renames
        .iter()
        .map(|command| {
            (
                command["activeSessionId"].as_str().unwrap_or_default(),
                command["name"].as_str().unwrap_or_default(),
                command["renamedBy"].as_str(),
            )
        })
        .collect();
    assert_eq!(
        routed,
        [
            ("parent-live", "lead", None),
            ("parent-live", "lead", None),
            ("child-passivated", "bench-runner", Some("parent")),
            (CHILD_SESSION, "bench-runner", Some("parent")),
        ]
    );
}
