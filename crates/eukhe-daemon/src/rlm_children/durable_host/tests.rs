//! The durable child host against a recording fake supervisor: keyed calls
//! run once, a spawn creates under the requested id and finds a resident
//! child again after a parent restart, a settled child reports its answer,
//! reply flag, and usage, a restarted parent's resumed watch fails a child
//! whose run was interrupted (without waking one no worker hosts), the
//! task prompt lands as the parent's spawn kickoff row (waiting out a
//! supervisor restart), `rlm.rename` routes self and child renames, and an
//! isolated child works on a copy of the parent's workspace handed back at
//! its end.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::{Arc, Mutex};

use eukhe_core::child_workspace::{Handback, WorkspaceMode};
use eukhe_core::durable::children::{
    RlmChildCancelRequest, RlmChildDeleteRequest, RlmChildHandbackRequest, RlmChildIdentity,
    RlmChildOutcome, RlmChildPromptRequest, RlmChildRunState, RlmChildSpawnRequest,
    RlmChildWaitRequest, RlmRenameRequest, RlmRenameTarget, RlmSubagentHost,
};
use eukhe_types::daemon::WorkerLiveness;
use eukhe_types::input_origin::ChildFailure;
use eukhe_types::pi_ai::StreamFailureKind;
use eukhe_types::platform::transport::bind_transport;
use serde_json::{json, Value};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

use super::super::{ParentIdentity, SupervisorChildSessions};
use crate::protocol::{response_failure, response_success};

const CHILD_SESSION: &str = "0192a000-0000-7000-8000-00000000c001";

/// What the fake supervisor saw, the resident sessions it lists, whether
/// no worker hosts the child (its non-waking probes answer the
/// unknown-session error), and the run outcome the child answers (an
/// answered run when unset).
#[derive(Default)]
struct Supervisor {
    commands: Vec<Value>,
    resident: Vec<Value>,
    child_unhosted: bool,
    outcome: Option<RlmChildRunState>,
    overloaded_child: Option<WorkerLiveness>,
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
        "get_state" | "get_run_outcome" if lock(shared).overloaded_child.is_some() => {
            response_failure(
                Some(id),
                command_type,
                "Session worker child-live is overloaded; retry later",
                Some(eukhe_types::daemon::DaemonErrorInfo::WorkerOverloaded),
            )
        }
        "get_worker_liveness" => match lock(shared).overloaded_child {
            Some(liveness) => response_success(
                Some(id),
                command_type,
                Some(json!({ "liveness": liveness })),
            ),
            None => response_failure(Some(id), command_type, "unexpected liveness probe", None),
        },
        "get_state" | "get_session_stats" if lock(shared).child_unhosted => response_failure(
            Some(id),
            command_type,
            &format!(
                "Unknown active session: {}",
                command["activeSessionId"].as_str().unwrap_or_default()
            ),
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
        "get_run_outcome" => {
            let state =
                lock(shared)
                    .outcome
                    .clone()
                    .unwrap_or_else(|| RlmChildRunState::Answered {
                        answer_preview: Some("the child final answer".to_owned()),
                    });
            response_success(
                Some(id),
                command_type,
                Some(
                    serde_json::to_value(RlmChildOutcome {
                        state,
                        progress: Some(7),
                        answer: None,
                    })
                    .unwrap(),
                ),
            )
        }
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
    serve_fake_supervisor(shared, &socket).await;
    socket
}

/// Serve the fake supervisor on `socket`.
async fn serve_fake_supervisor(shared: Shared, socket: &Path) {
    let listener = bind_transport(socket, eukhe_bend::rules::fsmode::peer_verdict)
        .await
        .unwrap();
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
}

async fn host(shared: &Shared, agent_dir: &std::path::Path) -> SupervisorChildSessions {
    let socket = fake_supervisor(Arc::clone(shared)).await;
    let sessions = SupervisorChildSessions::new(
        Arc::new(crate::supervisor_link::SupervisorLink::new(socket)),
        agent_dir.to_path_buf(),
        "parent-live".to_owned(),
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
        workspace: WorkspaceMode::Shared,
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

/// A child create carries the family its parent has at spawn time
/// (`cvarFamily`, read from the parent's live source).
#[tokio::test]
async fn spawn_carries_the_parents_cvar_family() {
    use eukhe_core::settings::cvar::{AgentLayer, Set, Sets};
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    let sessions = host(&shared, dir.path()).await;
    let family = vec![AgentLayer {
        profile: Sets::default(),
        sets: Sets(vec![Set {
            id: "transport".to_owned(),
            value: json!("sse"),
        }]),
    }];
    let source = family.clone();
    sessions.set_parent_cvar_family_source(Arc::new(move || source.clone()));
    sessions.spawn(spawn_request()).await.unwrap();
    let creates = commands_of(&shared, "create");
    assert_eq!(
        creates[0]["config"]["cvarFamily"],
        serde_json::to_value(family).unwrap()
    );
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

    let observed = sessions
        .wait_settled(RlmChildWaitRequest {
            session_id: CHILD_SESSION.to_owned(),
            rlm_child_id: "sub-0192a000".to_owned(),
            timeout_ms: 10,
        })
        .await
        .unwrap();
    assert_eq!(
        observed.state,
        RlmChildRunState::Answered {
            answer_preview: Some("the child final answer".to_owned()),
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

/// Write the child's display entry (`rlm-subagent.json`) with `status`.
fn write_child_display(agent_dir: &std::path::Path, status: &str) {
    let child_dir = agent_dir
        .join("session-artifacts")
        .join("parent-session")
        .join("sub-0192a000");
    std::fs::create_dir_all(&child_dir).unwrap();
    std::fs::write(
        child_dir.join("rlm-subagent.json"),
        json!({
            "type": "rlm_subagent",
            "childId": "sub-0192a000",
            "sessionName": "worker-a",
            "sessionDir": child_dir.to_string_lossy(),
            "status": status,
        })
        .to_string(),
    )
    .unwrap();
}

fn resumed_wait() -> RlmChildWaitRequest {
    RlmChildWaitRequest {
        session_id: CHILD_SESSION.to_owned(),
        rlm_child_id: "sub-0192a000".to_owned(),
        timeout_ms: 10,
    }
}

/// A restarted parent's resumed watch (the host never spawned the child)
/// that finds the child idle while its display entry still says `running`
/// settles it as interrupted; the display stays `running`.
#[tokio::test]
async fn a_resumed_watch_fails_a_child_whose_run_was_interrupted() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    write_child_display(dir.path(), "running");
    let sessions = host(&shared, dir.path()).await;
    let observed = sessions.wait_settled(resumed_wait()).await.unwrap();
    assert_eq!(
        observed.state,
        RlmChildRunState::Failed {
            failure: ChildFailure::Interrupted,
            error: super::INTERRUPTED_ERROR.to_owned(),
        }
    );
    let display = crate::rlm_ledger::read_rlm_subagent_display(
        &dir.path()
            .join("session-artifacts")
            .join("parent-session")
            .join("sub-0192a000"),
    )
    .unwrap();
    assert_eq!(display.status, "running");
}

/// A resumed watch over an interrupted child no worker hosts (the parent's
/// death closed it) settles it as interrupted from the non-waking probe
/// alone: the idle wait, which would wake the passivated child, never runs.
#[tokio::test]
async fn a_resumed_watch_leaves_an_unhosted_interrupted_child_passive() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    lock(&shared).child_unhosted = true;
    write_child_display(dir.path(), "running");
    let sessions = host(&shared, dir.path()).await;
    let observed = sessions.wait_settled(resumed_wait()).await.unwrap();
    assert_eq!(
        observed.state,
        RlmChildRunState::Failed {
            failure: ChildFailure::Interrupted,
            error: super::INTERRUPTED_ERROR.to_owned(),
        }
    );
    assert_eq!(observed.usage, None);
    assert_eq!(commands_of(&shared, "get_state").len(), 1);
    assert!(
        commands_of(&shared, "wait_for_idle").is_empty(),
        "the resumed watch must not wake an unhosted child"
    );
}

/// A resumed watch over a child whose display a settle already completed
/// reports the settle (the run finished before the restart).
#[tokio::test]
async fn a_resumed_watch_settles_a_completed_child() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    write_child_display(dir.path(), "completed");
    let sessions = host(&shared, dir.path()).await;
    let observed = sessions.wait_settled(resumed_wait()).await.unwrap();
    assert_eq!(
        observed.state,
        RlmChildRunState::Answered {
            answer_preview: Some("the child final answer".to_owned()),
        }
    );
}

/// Regression (stuck.md cause 3): a child whose run ended while a
/// background job it started still runs is observed idle with that job,
/// not settled, and its display entry stays `running`. The old watch read
/// "idle twice" as settled and completed the child.
#[tokio::test]
async fn an_idle_child_with_a_pending_job_is_not_settled() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    lock(&shared).outcome = Some(RlmChildRunState::Idle { pending_jobs: 1 });
    let sessions = host(&shared, dir.path()).await;
    sessions.spawn(spawn_request()).await.unwrap();
    write_child_display(dir.path(), "running");
    let observed = sessions.wait_settled(resumed_wait()).await.unwrap();
    assert_eq!(observed.state, RlmChildRunState::Idle { pending_jobs: 1 });
    let display = crate::rlm_ledger::read_rlm_subagent_display(
        &dir.path()
            .join("session-artifacts")
            .join("parent-session")
            .join("sub-0192a000"),
    )
    .unwrap();
    assert_eq!(display.status, "running");
}

/// Regression (stuck.md causes 3 and 6): a child whose run ended on a
/// provider error settles failed with the provider's kind, never as a
/// completed run.
#[tokio::test]
async fn a_child_run_ended_by_a_provider_error_settles_failed() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    let failed = RlmChildRunState::Failed {
        failure: ChildFailure::Provider {
            kind: StreamFailureKind::Auth,
        },
        error: "401 OAuth access token has expired".to_owned(),
    };
    lock(&shared).outcome = Some(failed.clone());
    let sessions = host(&shared, dir.path()).await;
    sessions.spawn(spawn_request()).await.unwrap();
    write_child_display(dir.path(), "running");
    let observed = sessions.wait_settled(resumed_wait()).await.unwrap();
    assert_eq!(observed.state, failed);
    let display = crate::rlm_ledger::read_rlm_subagent_display(
        &dir.path()
            .join("session-artifacts")
            .join("parent-session")
            .join("sub-0192a000"),
    )
    .unwrap();
    assert_eq!(display.status, "running");
}

/// Regression (H5): a live child whose probes fail (refused as
/// overloaded) is a failed poll, which the parent's watch counts toward
/// unreachable. The old host answered `Running`, so a child that never
/// answered was watched forever.
#[tokio::test]
async fn a_live_child_whose_probes_fail_is_a_failed_poll() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    lock(&shared).overloaded_child = Some(WorkerLiveness::Live);
    let sessions = host(&shared, dir.path()).await;
    let failed = sessions
        .wait_settled(resumed_wait())
        .await
        .expect_err("a live child's failed probe fails the poll");
    assert!(format!("{failed:#}").contains("overloaded"), "{failed:#}");
    assert_eq!(commands_of(&shared, "get_worker_liveness").len(), 1);
}

/// A child whose probes fail and whose worker process is gone (no
/// resident, or one the supervisor stopped) settles as failed at once,
/// typed `WorkerExited` (its in-flight effects are unknown).
#[tokio::test]
async fn a_child_whose_worker_is_gone_settles_failed() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    lock(&shared).overloaded_child = Some(WorkerLiveness::Gone);
    let sessions = host(&shared, dir.path()).await;
    let observed = sessions.wait_settled(resumed_wait()).await.unwrap();
    assert_eq!(
        observed.state,
        RlmChildRunState::Failed {
            failure: ChildFailure::WorkerExited,
            error: super::WORKER_EXITED_ERROR.to_owned(),
        }
    );
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

/// H5: the watch stops a stuck child through the `rlm` kill path: a plain
/// kill of its worker (no ledger delete, so its session stays), once per
/// key; a child no worker hosts is already stopped.
#[tokio::test]
async fn stopping_a_child_kills_its_worker_once_and_keeps_its_session() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    let sessions = host(&shared, dir.path()).await;
    sessions.spawn(spawn_request()).await.unwrap();
    let stop = RlmChildCancelRequest {
        idempotency_key: "rlm:7:stop".to_owned(),
        session_id: CHILD_SESSION.to_owned(),
    };
    sessions.stop(stop.clone()).await.unwrap();
    sessions.stop(stop).await.unwrap();
    let kills = commands_of(&shared, "kill");
    assert_eq!(kills.len(), 1, "{kills:?}");
    assert_eq!(kills[0]["activeSessionId"], "child-live");
    assert_eq!(kills[0].get("rlmLedgerDelete"), None);
    sessions
        .stop(RlmChildCancelRequest {
            idempotency_key: "rlm:9:stop".to_owned(),
            session_id: "gone".to_owned(),
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

/// A child prompt sent while the supervisor is down (`kill -9`: its stale
/// socket refuses connects, and the workers live on for the restarted
/// supervisor) waits for the supervisor to accept again: the child gets
/// its prompt once, and the prompt never fails the child as undelivered.
#[tokio::test]
async fn a_prompt_waits_out_a_supervisor_restart() {
    let dir = tempfile::tempdir().unwrap();
    let shared = Shared::default();
    let socket = dir.path().join("supervisor.sock");
    // The killed supervisor's socket file stays behind, refusing connects
    // (never listening, so no concurrent fork's descriptor copy revives it).
    drop(crate::socket::bind_dead_socket(&socket));
    let sessions = SupervisorChildSessions::new(
        Arc::new(crate::supervisor_link::SupervisorLink::new(socket.clone())),
        dir.path().to_path_buf(),
        "parent-live".to_owned(),
    );
    sessions.set_identity(ParentIdentity {
        model: Some("mock/mock-1".to_owned()),
        cwd: Some(dir.path().to_string_lossy().into_owned()),
        session_id: Some("parent-session".to_owned()),
        ..ParentIdentity::with_default_depth()
    });
    let mut prompt = sessions.prompt(RlmChildPromptRequest {
        idempotency_key: "rlm:7:prompt".to_owned(),
        session_id: CHILD_SESSION.to_owned(),
        rlm_child_id: "sub-0192a000".to_owned(),
        prompt: "Investigate".to_owned(),
    });
    // The refused connect fails at once; the prompt stays pending, waiting
    // for the supervisor instead of failing.
    assert!(
        futures::poll!(prompt.as_mut()).is_pending(),
        "a prompt against a down supervisor waits for it"
    );
    assert!(commands_of(&shared, "prompt").is_empty());
    // The restarted supervisor binds the same path.
    std::fs::remove_file(&socket).unwrap();
    serve_fake_supervisor(Arc::clone(&shared), &socket).await;
    prompt.await.unwrap();
    let prompts = commands_of(&shared, "prompt");
    assert_eq!(prompts.len(), 1, "{prompts:?}");
    assert_eq!(prompts[0]["admissionId"], "rlm:7:prompt");
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

/// The files under `dir` (relative path → content).
fn files_under(dir: &Path) -> BTreeMap<String, String> {
    let mut files = BTreeMap::new();
    let mut pending = vec![dir.to_path_buf()];
    while let Some(next) = pending.pop() {
        for entry in std::fs::read_dir(&next).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                pending.push(path);
            } else {
                let relative = path
                    .strip_prefix(dir)
                    .unwrap()
                    .to_string_lossy()
                    .into_owned();
                files.insert(relative, std::fs::read_to_string(&path).unwrap());
            }
        }
    }
    files
}

fn file_map(entries: &[(&str, &str)]) -> BTreeMap<String, String> {
    entries
        .iter()
        .map(|(path, body)| ((*path).to_owned(), (*body).to_owned()))
        .collect()
}

/// Spawn `sub-0192a000` isolated in a parent whose workspace (`parent`)
/// holds `a.txt`, `b.txt`, `c.txt`, a `.gitignore` and an ignored
/// `target/x`; assert the child's create names its copy as its cwd and
/// the copy holds the files not ignored. Returns the host and the
/// workspace root.
async fn spawn_isolated(
    agent_dir: &Path,
    parent: &Path,
) -> (SupervisorChildSessions, std::path::PathBuf) {
    let parent_files = file_map(&[
        (".gitignore", "target/\n"),
        ("a.txt", "a0"),
        ("b.txt", "b0"),
        ("c.txt", "c0"),
        ("target/x", "build output"),
    ]);
    for (path, body) in &parent_files {
        let path = parent.join(path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, body).unwrap();
    }
    let shared = Shared::default();
    let sessions = host(&shared, agent_dir).await;
    sessions.set_identity(ParentIdentity {
        model: Some("mock/mock-1".to_owned()),
        cwd: Some(parent.to_string_lossy().into_owned()),
        session_id: Some("parent-session".to_owned()),
        ..ParentIdentity::with_default_depth()
    });
    sessions
        .spawn(RlmChildSpawnRequest {
            workspace: WorkspaceMode::Isolated,
            ..spawn_request()
        })
        .await
        .unwrap();
    let root = agent_dir
        .join("workspaces")
        .join("parent-session")
        .join("sub-0192a000");
    let tree = root.join("tree");
    let cwds: Vec<Value> = commands_of(&shared, "create")
        .iter()
        .map(|create| create["config"]["cwd"].clone())
        .collect();
    assert_eq!(cwds, [json!(tree.to_string_lossy())]);
    assert_eq!(
        files_under(&tree),
        file_map(&[
            (".gitignore", "target/\n"),
            ("a.txt", "a0"),
            ("b.txt", "b0"),
            ("c.txt", "c0"),
        ])
    );
    (sessions, root)
}

fn handback_request() -> RlmChildHandbackRequest {
    RlmChildHandbackRequest {
        session_id: CHILD_SESSION.to_owned(),
        rlm_child_id: "sub-0192a000".to_owned(),
    }
}

/// S3: an isolated child works in its own copy of the parent's workspace
/// (the files its `.gitignore` does not ignore). Its hand-back takes what
/// only the child changed, keeps the parent's content where both changed
/// (the child's version kept aside), and repeats as the same record. A
/// child without a workspace hands back nothing.
#[tokio::test]
async fn an_isolated_child_works_on_a_copy_handed_back_at_its_end() {
    let dir = tempfile::tempdir().unwrap();
    let parent = tempfile::tempdir().unwrap();
    let (sessions, root) = spawn_isolated(dir.path(), parent.path()).await;
    let tree = root.join("tree");
    std::fs::write(tree.join("a.txt"), "a-child").unwrap();
    std::fs::write(tree.join("c.txt"), "c-child").unwrap();
    std::fs::write(parent.path().join("b.txt"), "b-parent").unwrap();
    std::fs::write(parent.path().join("c.txt"), "c-parent").unwrap();
    let handback = sessions.hand_back(handback_request()).await.unwrap();
    let conflicts = root.join("conflicts");
    assert_eq!(
        handback,
        Some(Handback {
            taken: vec!["a.txt".to_owned()],
            conflicts: vec!["c.txt".to_owned()],
            kept: Some(conflicts.to_string_lossy().into_owned()),
        })
    );
    assert_eq!(
        sessions.hand_back(handback_request()).await.unwrap(),
        handback
    );
    assert_eq!(
        files_under(parent.path()),
        file_map(&[
            (".gitignore", "target/\n"),
            ("a.txt", "a-child"),
            ("b.txt", "b-parent"),
            ("c.txt", "c-parent"),
            ("target/x", "build output"),
        ])
    );
    assert_eq!(files_under(&conflicts), file_map(&[("c.txt", "c-child")]));
    assert_eq!(
        sessions
            .hand_back(RlmChildHandbackRequest {
                session_id: "shared-child".to_owned(),
                rlm_child_id: "sub-shared".to_owned(),
            })
            .await
            .unwrap(),
        None
    );
}

/// `rlm.delete_subagent` deletes before the task's hand-back: the delete
/// takes the isolated child's changes back first, and the later hand-back
/// returns that record.
#[tokio::test]
async fn deleting_an_isolated_child_hands_its_workspace_back_first() {
    let dir = tempfile::tempdir().unwrap();
    let parent = tempfile::tempdir().unwrap();
    let (sessions, root) = spawn_isolated(dir.path(), parent.path()).await;
    std::fs::write(root.join("tree").join("a.txt"), "a-child").unwrap();
    sessions
        .delete(RlmChildDeleteRequest {
            idempotency_key: "rlm:7:delete".to_owned(),
            session_id: CHILD_SESSION.to_owned(),
            rlm_child_id: "sub-0192a000".to_owned(),
        })
        .await
        .unwrap();
    std::fs::write(parent.path().join("a.txt"), "a-parent-after").unwrap();
    assert_eq!(
        sessions.hand_back(handback_request()).await.unwrap(),
        Some(Handback {
            taken: vec!["a.txt".to_owned()],
            conflicts: Vec::new(),
            kept: None,
        })
    );
    assert_eq!(
        files_under(parent.path()),
        file_map(&[
            (".gitignore", "target/\n"),
            ("a.txt", "a-parent-after"),
            ("b.txt", "b0"),
            ("c.txt", "c0"),
            ("target/x", "build output"),
        ])
    );
}
