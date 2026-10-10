//! The durable child-session host: [`SupervisorChildSessions`] as the
//! [`durable::RlmSubagentHost`] an `eukhe.rlm.child` task drives. The child
//! lifecycle (spawn, prompt, settle watch, report) lives in the parent's
//! durable task; this side only runs keyed supervisor primitives.
//!
//! Idempotency: a key this process already served answers from
//! [`DurableCalls`]; after a parent restart the supervisor is the record —
//! a spawn finds the child by its derived session id (resident, or reopened
//! by a `create` naming that id), a prompt rides the child's submission
//! dedupe (`admissionId` = the key), and cancel/delete of a child that is
//! already gone are no-ops.

use std::collections::{HashMap, HashSet};
use std::sync::PoisonError;

use eukhe_core::durable::children as durable;
use eukhe_core::session_engine::agent_messaging::{
    create_agent_session_message_row, AgentFamilyRelationship, AgentSessionMessageRowPayload,
};
use eukhe_types::daemon::{DaemonCommand, PromptInput};
use eukhe_types::pi_ai::{Usage, UsageCost};

use super::host::resolve_child_model_allowlisted;
use super::{
    assert_thinking_supported, json, now_ms, Arc, Duration, Map, Path, PathBuf, Result,
    SupervisorChildSessions, SupervisorChildSessionsInner, Value, KILL_TIMEOUT_MS,
    PROMPT_TIMEOUT_MS, RENAME_TIMEOUT_MS, STATE_TIMEOUT_MS, WATCH_SETTLE_GRACE_MS,
};

/// The supervisor's error for a selector no resident worker answers.
const UNKNOWN_SESSION: &str = "Unknown active session:";

/// The `rlm.rename` refusal for a selector outside this session's family.
const NOT_OWN_FAMILY: &str =
    "rlm.rename can only rename the current session or one of its direct children";

/// The settle error of a child whose run ended while its parent was down.
const INTERRUPTED_ERROR: &str =
    "RLM child run was interrupted: the child stopped mid-run while its parent session was down";

/// Whether `child_dir`'s display entry names `child_id` and still says
/// `running` (no settle completed it); a missing entry reads `false`.
async fn display_running(child_dir: &Path, child_id: &str) -> Result<bool> {
    let child_dir = child_dir.to_path_buf();
    let child_id = child_id.to_owned();
    let display = tokio::task::spawn_blocking(move || {
        crate::rlm_ledger::read_rlm_subagent_display(&child_dir)
            .is_some_and(|display| display.child_id == child_id && display.status == "running")
    })
    .await?;
    Ok(display)
}

/// Keyed calls this process already served, and the children it spawned.
#[derive(Default)]
pub(super) struct DurableCalls {
    /// Spawned children by durable session id.
    spawned: HashMap<String, durable::RlmChildSession>,
    /// `rlm.create_session` handles by idempotency key.
    created: HashMap<String, durable::RlmCreateSessionHandle>,
    /// Served prompt/cancel/delete keys.
    done: HashSet<String>,
    /// Routing or durable ids of children that messaged this parent since
    /// their task was admitted (TS `_parentReplyCount`).
    replied: HashSet<String>,
    /// Durable ids of children whose run this process saw in flight: a
    /// resumed watch that later finds such a child idle saw it settle.
    seen_running: HashSet<String>,
}

impl SupervisorChildSessionsInner {
    fn durable_calls(&self) -> std::sync::MutexGuard<'_, DurableCalls> {
        self.durable_calls
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    /// Refresh the inherited model from the parent's live model reader (a
    /// parent that switched models since `create` spawns on the new one).
    async fn refresh_parent_model(&self) {
        let source = self
            .parent_model
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        let Some(source) = source else {
            return;
        };
        if let Some(model) = source().await {
            self.identity
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .model = Some(model);
        }
    }

    /// The selector that reaches child `session_id`: its routing id when
    /// this process spawned it, else the durable session id (the supervisor
    /// wakes a passivated child by it).
    fn durable_selector(&self, session_id: &str) -> String {
        self.durable_calls().spawned.get(session_id).map_or_else(
            || session_id.to_owned(),
            |child| child.active_session_id.clone(),
        )
    }

    /// Send `make(selector)`; an unknown routing id retries once by the
    /// durable session id.
    async fn durable_command(
        &self,
        session_id: &str,
        timeout_ms: u64,
        make: impl Fn(&str) -> DaemonCommand,
    ) -> Result<Value> {
        let selector = self.durable_selector(session_id);
        match self.command(&make(&selector), timeout_ms).await {
            Err(error)
                if selector != session_id && format!("{error:#}").starts_with(UNKNOWN_SESSION) =>
            {
                self.command(&make(session_id), timeout_ms).await
            }
            other => other,
        }
    }

    /// The resident session persisted under `session_id`, if any.
    async fn resident_child(&self, session_id: &str) -> Result<Option<Value>> {
        let listed = self
            .command(
                &DaemonCommand::List {
                    id: None,
                    all: Some(true),
                    cwd: None,
                    session_dir: None,
                    include_client_owned: Some(true),
                    rest: Map::default(),
                },
                STATE_TIMEOUT_MS,
            )
            .await?;
        let sessions = listed
            .get("sessions")
            .and_then(Value::as_array)
            .or_else(|| listed.as_array());
        Ok(sessions.and_then(|sessions| {
            sessions
                .iter()
                .find(|summary| {
                    summary.get("sessionId").and_then(Value::as_str) == Some(session_id)
                })
                .cloned()
        }))
    }

    /// The child's cumulative usage from its `get_session_stats` (`tokens`
    /// and `cost`); `None` when the child reports none.
    async fn child_usage(&self, session_id: &str) -> Option<Usage> {
        let stats = self
            .durable_command(session_id, STATE_TIMEOUT_MS, |selector| {
                DaemonCommand::GetSessionStats {
                    id: None,
                    active_session_id: selector.to_owned(),
                    rest: Map::default(),
                }
            })
            .await
            .ok()?;
        stats_usage(&stats)
    }

    /// The spawn kickoff (TS `spawnMessage`): the task text labeled
    /// `[task from parent]` (the model context, the label the child system
    /// prompt promises) and the parent's `agent_message` row carrying it
    /// (`details.id` `spawn:<child id>`, the raw task as `details.message`,
    /// the parent endpoint as `from`, no `target`), so the child renders a
    /// parent message instead of an unlabeled user row.
    fn spawn_kickoff(&self, rlm_child_id: &str, prompt: &str) -> (String, Value) {
        let content = format!("[task from parent]\n\n{prompt}");
        let mut from = json!({ "activeSessionId": self.parent_active_session_id });
        let session_id = self
            .identity
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .session_id
            .clone();
        if let Some(session_id) = session_id {
            from["sessionId"] = json!(session_id);
        }
        let name_source = self
            .parent_name
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        if let Some(name) = name_source.and_then(|source| source()) {
            from["sessionName"] = json!(name);
        }
        let row = create_agent_session_message_row(&AgentSessionMessageRowPayload {
            id: &format!("spawn:{rlm_child_id}"),
            prompt: &content,
            message: prompt,
            from: &from,
            from_relationship: Some(AgentFamilyRelationship::Parent),
            target: None,
            timestamp: now_ms(),
        });
        (content, row)
    }
}

/// A `get_session_stats` reply's usage (TS `SessionStats.tokens` + `cost`).
pub(super) fn stats_usage(stats: &Value) -> Option<Usage> {
    let tokens = stats.get("tokens")?;
    let count = |key: &str| tokens.get(key).and_then(Value::as_u64).unwrap_or(0);
    let usage = Usage {
        input: count("input"),
        output: count("output"),
        cache_read: count("cacheRead"),
        cache_write: count("cacheWrite"),
        cache_write_1h: None,
        reasoning: None,
        total_tokens: count("total"),
        cost: UsageCost {
            total: stats.get("cost").and_then(Value::as_f64).unwrap_or(0.0),
            ..UsageCost::default()
        },
    };
    (usage != Usage::default()).then_some(usage)
}

fn summary_str(summary: &Value, key: &str) -> Option<String> {
    summary
        .get(key)
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
        .map(str::to_owned)
}

impl SupervisorChildSessions {
    /// Record that the child `child_id` (routing or durable id) sent an agent
    /// message to this parent: its settle owes no no-reply notice.
    pub fn mark_durable_child_replied(&self, child_id: &str) {
        self.inner
            .durable_calls()
            .replied
            .insert(child_id.to_owned());
    }
}

impl durable::RlmSubagentHost for SupervisorChildSessions {
    fn spawn(
        &self,
        request: durable::RlmChildSpawnRequest,
    ) -> durable::RlmHostFuture<'_, durable::RlmChildSession> {
        let this = Arc::clone(&self.inner);
        Box::pin(async move {
            let session_id = request.child.session_id.clone();
            if let Some(child) = this.durable_calls().spawned.get(&session_id) {
                return Ok(child.clone());
            }
            this.refresh_parent_model().await;
            let model = resolve_child_model_allowlisted(
                &this,
                request.model.as_deref(),
                "spawn",
                "subagent",
            )
            .await?;
            assert_thinking_supported(&this.agent_dir, request.thinking.as_deref(), &model)?;
            let mut identity = this.identity.lock().expect("identity lock").clone();
            identity.rlm_max_depth = request.max_depth;
            let child_dir = this.child_session_dir(&request.child.rlm_child_id, &identity)?;
            let child = if let Some(summary) = this.resident_child(&session_id).await? {
                // A rerun after a parent restart: the child is still resident.
                durable::RlmChildSession {
                    active_session_id: summary_str(&summary, "activeSessionId")
                        .unwrap_or_else(|| session_id.clone()),
                    session_id: session_id.clone(),
                    session_name: summary_str(&summary, "sessionName")
                        .unwrap_or_else(|| request.name.clone()),
                    session_dir: child_dir.to_string_lossy().into_owned(),
                    model,
                }
            } else {
                let thinking = request.thinking.as_deref().or(identity.thinking.as_deref());
                let cwd = identity.cwd.clone().unwrap_or_else(|| "/".to_owned());
                let runtime_metadata = json!({
                    "kind": "subagent",
                    "rlmChildId": request.child.rlm_child_id,
                    "parentActiveSessionId": this.parent_active_session_id,
                    "rlmDepth": request.depth,
                    "createdAt": now_ms(),
                });
                // A create naming an existing storage reopens it, so a
                // passivated child is found again by the same id.
                let created = this
                    .create_child(
                        &request.child.rlm_child_id,
                        Some(&request.name),
                        Some(&request.prompt),
                        request.depth,
                        &model,
                        thinking,
                        &cwd,
                        &child_dir,
                        request.spawned_by_request_id.as_deref(),
                        Some(runtime_metadata),
                        &identity,
                        Some(&session_id),
                    )
                    .await?;
                durable::RlmChildSession {
                    active_session_id: created.active_session_id,
                    session_id: session_id.clone(),
                    session_name: created.session_name.unwrap_or_else(|| request.name.clone()),
                    session_dir: created.session_dir,
                    model,
                }
            };
            this.durable_calls()
                .spawned
                .insert(session_id, child.clone());
            Ok(child)
        })
    }

    fn create_session(
        &self,
        request: durable::RlmCreateSessionRequest,
    ) -> durable::RlmHostFuture<'_, durable::RlmCreateSessionHandle> {
        let this = Arc::clone(&self.inner);
        Box::pin(async move {
            if let Some(handle) = this.durable_calls().created.get(&request.idempotency_key) {
                return Ok(handle.clone());
            }
            this.refresh_parent_model().await;
            let identity = this.identity.lock().expect("identity lock").clone();
            if identity.rlm_depth != 0 {
                anyhow::bail!("rlm.create_session is available only from a depth-0 session");
            }
            let model = resolve_child_model_allowlisted(
                &this,
                request.model.as_deref(),
                "create_session",
                "top-level session",
            )
            .await?;
            assert_thinking_supported(&this.agent_dir, request.thinking.as_deref(), &model)?;
            let cwd = match &request.cwd {
                Some(cwd) if Path::new(cwd).is_absolute() => PathBuf::from(cwd),
                Some(cwd) => Path::new(identity.cwd.as_deref().unwrap_or("/")).join(cwd),
                None => PathBuf::from(identity.cwd.clone().unwrap_or_else(|| "/".to_owned())),
            };
            let sessions_dir = crate::paths::sessions_dir(&this.agent_dir)?;
            std::fs::create_dir_all(&sessions_dir)?;
            let thinking = request.thinking.as_deref().or(identity.thinking.as_deref());
            let created = this
                .launch_child(
                    "root",
                    request.name.as_deref(),
                    &request.prompt,
                    0,
                    &model,
                    thinking,
                    &cwd.to_string_lossy(),
                    &sessions_dir,
                    None,
                    &identity,
                )
                .await?;
            if created.summary_rlm_depth.is_some_and(|depth| depth != 0) {
                anyhow::bail!("Daemon supervisor returned an invalid depth-0 session summary");
            }
            let handle = durable::RlmCreateSessionHandle {
                active_session_id: created.active_session_id.clone(),
                session_id: created
                    .session_id
                    .clone()
                    .unwrap_or_else(|| created.active_session_id.clone()),
                name: created
                    .session_name
                    .clone()
                    .unwrap_or_else(|| created.active_session_id.clone()),
                session_file: created.session_file.unwrap_or_default(),
                model,
            };
            this.durable_calls()
                .created
                .insert(request.idempotency_key, handle.clone());
            Ok(handle)
        })
    }

    fn prompt(&self, request: durable::RlmChildPromptRequest) -> durable::RlmHostFuture<'_, ()> {
        let this = Arc::clone(&self.inner);
        Box::pin(async move {
            if this.durable_calls().done.contains(&request.idempotency_key) {
                return Ok(());
            }
            let key = request.idempotency_key.clone();
            // The kickoff rides prompt admission as the parent's
            // `agent_message` row; its content (the labeled task) is the
            // model context.
            let (content, kickoff) = this.spawn_kickoff(&request.rlm_child_id, &request.prompt);
            this.durable_command(&request.session_id, PROMPT_TIMEOUT_MS, |selector| {
                DaemonCommand::Prompt {
                    id: None,
                    active_session_id: selector.to_owned(),
                    message: content.clone(),
                    input: PromptInput {
                        content: None,
                        images: None,
                        streaming_behavior: None,
                        queue_if_busy: None,
                        expand_prompt_templates: None,
                        source: Some(json!("rpc")),
                        agent_message_id: None,
                        custom_message: Some(kickoff.clone()),
                        queue_key: None,
                        prefix_messages: None,
                        // The child's submission dedupes by it: a rerun
                        // after a parent crash admits nothing twice.
                        admission_id: Some(key.clone()),
                        rlm_notice_nonce: None,
                    },
                    rest: Map::default(),
                }
            })
            .await
            .map_err(|error| {
                error.context(format!("prompt RLM child session {}", request.session_id))
            })?;
            this.durable_calls().done.insert(key);
            Ok(())
        })
    }

    fn wait_settled(
        &self,
        request: durable::RlmChildWaitRequest,
    ) -> durable::RlmHostFuture<'_, durable::RlmChildObservation> {
        let this = Arc::clone(&self.inner);
        Box::pin(async move {
            let selector = this.durable_selector(&request.session_id);
            this.wait_for_child(&selector, Duration::from_millis(request.timeout_ms))
                .await;
            let running = || async {
                this.durable_calls()
                    .seen_running
                    .insert(request.session_id.clone());
                durable::RlmChildObservation {
                    state: durable::RlmChildRunState::Running,
                    usage: this.child_usage(&request.session_id).await,
                }
            };
            if this.child_busy(&selector).await? {
                return Ok(running().await);
            }
            // Stability re-check: a prompt admitted to an idle worker can
            // read idle once before its run starts.
            tokio::time::sleep(Duration::from_millis(WATCH_SETTLE_GRACE_MS)).await;
            if this.child_busy(&selector).await? {
                return Ok(running().await);
            }
            let child_dir = {
                let identity = this.identity.lock().unwrap_or_else(PoisonError::into_inner);
                this.child_session_path(&request.rlm_child_id, &identity)
            };
            // A watch this process did not start (the parent restarted
            // mid-run: its death or the daemon's restart closed the child)
            // that never saw the run in flight and finds the child idle
            // while its display entry still says `running` saw the run end
            // with no settle anyone observed: the run was interrupted, so
            // the child settles as an error (TS relists such a child as
            // `error`, never as completed).
            let resumed = {
                let calls = this.durable_calls();
                !calls.spawned.contains_key(&request.session_id)
                    && !calls.seen_running.contains(&request.session_id)
            };
            if resumed && display_running(&child_dir, &request.rlm_child_id).await? {
                return Ok(durable::RlmChildObservation {
                    state: durable::RlmChildRunState::Failed {
                        error: INTERRUPTED_ERROR.to_owned(),
                    },
                    usage: this.child_usage(&request.session_id).await,
                });
            }
            let answer = this.child_answer(&selector).await.ok().flatten();
            let replied_since_task = {
                let calls = this.durable_calls();
                calls.replied.contains(&selector) || calls.replied.contains(&request.session_id)
            };
            // The settled run completes the child's display entry, so a
            // restarted parent relists it as completed.
            super::lifecycle::complete_child_display(child_dir, request.rlm_child_id.clone()).await;
            Ok(durable::RlmChildObservation {
                state: durable::RlmChildRunState::Settled {
                    // `child_answer` already compacts it for the roster.
                    answer_preview: answer,
                    replied_since_task,
                },
                usage: this.child_usage(&request.session_id).await,
            })
        })
    }

    fn cancel(&self, request: durable::RlmChildCancelRequest) -> durable::RlmHostFuture<'_, ()> {
        let this = Arc::clone(&self.inner);
        Box::pin(async move {
            if this.durable_calls().done.contains(&request.idempotency_key) {
                return Ok(());
            }
            let aborted = this
                .durable_command(&request.session_id, KILL_TIMEOUT_MS, |selector| {
                    DaemonCommand::Abort {
                        id: None,
                        active_session_id: selector.to_owned(),
                        rest: Map::default(),
                    }
                })
                .await;
            match aborted {
                // A child no worker answers has no run to abort.
                Err(error) if !format!("{error:#}").starts_with(UNKNOWN_SESSION) => {
                    return Err(
                        error.context(format!("cancel RLM child session {}", request.session_id))
                    );
                }
                Ok(_) | Err(_) => {}
            }
            this.durable_calls().done.insert(request.idempotency_key);
            Ok(())
        })
    }

    fn delete(&self, request: durable::RlmChildDeleteRequest) -> durable::RlmHostFuture<'_, ()> {
        let this = Arc::clone(&self.inner);
        Box::pin(async move {
            if this.durable_calls().done.contains(&request.idempotency_key) {
                return Ok(());
            }
            // The `rlmLedgerDelete` marker tells the supervisor this kill is
            // a delete (a plain stop must not tombstone the child).
            let killed = this
                .durable_command(&request.session_id, KILL_TIMEOUT_MS, |selector| {
                    DaemonCommand::Kill {
                        id: None,
                        active_session_id: selector.to_owned(),
                        rest: Map::from_iter([
                            ("rlmLedgerDelete".to_owned(), json!("user")),
                            ("rlmChildId".to_owned(), json!(request.rlm_child_id)),
                        ]),
                    }
                })
                .await;
            match killed {
                // Already gone: a rerun of a delete that completed.
                Err(error) if !format!("{error:#}").starts_with(UNKNOWN_SESSION) => {
                    return Err(error);
                }
                Ok(_) | Err(_) => {}
            }
            {
                let mut calls = this.durable_calls();
                calls.done.insert(request.idempotency_key);
                calls.spawned.remove(&request.session_id);
            }
            let notifier = this
                .delete_notifier
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .clone();
            if let Some(notify) = notifier {
                notify(&request.rlm_child_id);
            }
            Ok(())
        })
    }

    fn list(&self) -> durable::RlmHostFuture<'_, Vec<durable::RlmChildListing>> {
        let this = Arc::clone(&self.inner);
        Box::pin(async move {
            let children: Vec<String> = this.durable_calls().spawned.keys().cloned().collect();
            let mut listings = Vec::with_capacity(children.len());
            for session_id in children {
                let selector = this.durable_selector(&session_id);
                // A roster read is a snapshot: an unreachable child keeps
                // its durable row without live facts.
                let activity = match this.child_busy(&selector).await {
                    Ok(true) => Some(durable::RlmChildActivityKind::Executing),
                    Ok(false) => Some(durable::RlmChildActivityKind::Waiting),
                    Err(_) => None,
                };
                listings.push(durable::RlmChildListing {
                    session_id,
                    activity,
                    tool_name: None,
                    tool_use_count: None,
                    progress_note: None,
                    last_activity_at: None,
                });
            }
            Ok(listings)
        })
    }

    /// The rename is daemon-owned: the supervisor's live rename route
    /// reserves the name across the agent family, wakes a passivated
    /// target, and appends a child's RLM ledger rename. A parent-directed
    /// rename carries `renamedBy: "parent"` so the child's transcript
    /// notice names it; a self rename routes through the supervisor to this
    /// very worker.
    fn rename(&self, request: durable::RlmRenameRequest) -> durable::RlmHostFuture<'_, ()> {
        let this = Arc::clone(&self.inner);
        Box::pin(async move {
            let rename = |selector: &str, renamed_by: Option<&str>| DaemonCommand::Rename {
                id: None,
                active_session_id: selector.to_owned(),
                name: request.name.clone(),
                renamed_by: renamed_by.map(str::to_owned),
                rest: Map::default(),
            };
            match &request.target {
                durable::RlmRenameTarget::Session { selector } => {
                    if let Some(selector) = selector {
                        let own_session_id = this
                            .identity
                            .lock()
                            .unwrap_or_else(PoisonError::into_inner)
                            .session_id
                            .clone();
                        if *selector != this.parent_active_session_id
                            && own_session_id.as_deref() != Some(selector.as_str())
                        {
                            anyhow::bail!("{NOT_OWN_FAMILY}");
                        }
                    }
                    let own = this.parent_active_session_id.clone();
                    this.command(&rename(&own, None), RENAME_TIMEOUT_MS)
                        .await
                        .map_err(|error| error.context(format!("rename session \"{own}\"")))?;
                }
                durable::RlmRenameTarget::Child { session_id } => {
                    let parent = AgentFamilyRelationship::Parent.as_str();
                    this.durable_command(session_id, RENAME_TIMEOUT_MS, |selector| {
                        rename(selector, Some(parent))
                    })
                    .await
                    .map_err(|error| {
                        error.context(format!("rename RLM child session {session_id}"))
                    })?;
                }
            }
            Ok(())
        })
    }
}

// The kill cascade (TS `closeSessionOnce(reason)` closes the session's
// resident children with the same reason before the session's own close).
impl SupervisorChildSessions {
    /// Close the durable child sessions `session_ids` names with `reason`
    /// (the `rlmCloseReason` marker rides the `kill`). A child no worker
    /// answers is already closed; the first other failure is returned after
    /// every child was tried.
    ///
    /// # Errors
    ///
    /// A child's `kill` failed.
    pub(crate) async fn close_durable_children(
        &self,
        session_ids: &[String],
        reason: super::ChildCloseReason,
    ) -> Result<()> {
        let mut first_error = None;
        for session_id in session_ids {
            let killed = self
                .inner
                .durable_command(session_id, KILL_TIMEOUT_MS, |selector| {
                    let mut rest = Map::new();
                    if let Some(marker) = reason.wire_marker() {
                        rest.insert("rlmCloseReason".to_owned(), json!(marker));
                    }
                    DaemonCommand::Kill {
                        id: None,
                        active_session_id: selector.to_owned(),
                        rest,
                    }
                })
                .await;
            match killed {
                Err(error) if !format!("{error:#}").starts_with(UNKNOWN_SESSION) => {
                    first_error.get_or_insert(
                        error.context(format!("close RLM child session {session_id}")),
                    );
                }
                Ok(_) | Err(_) => {
                    self.inner.durable_calls().spawned.remove(session_id);
                }
            }
        }
        first_error.map_or(Ok(()), Err)
    }
}

impl crate::worker::Worker {
    /// The kill cascade of the hosted session: close every live child of
    /// its main conversation (spawned ones, by their durable session id)
    /// with `reason`. Best-effort like the TS kill handler's
    /// `.catch(() => undefined)`: failures are logged, never fail the close.
    pub(crate) async fn close_rlm_children(
        &self,
        hosted: &crate::worker::HostedSession,
        reason: super::ChildCloseReason,
    ) {
        let Some(host) = self.rlm_children.get() else {
            return;
        };
        let listed = async {
            let main = hosted.main()?;
            let records = durable::list_children(
                hosted.harness(),
                main.id(),
                &eukhe_chord::context::BACKGROUND_CONTEXT,
            )
            .await?;
            anyhow::Ok(
                records
                    .into_iter()
                    .filter_map(|record| record.entry.session_id)
                    .collect::<Vec<_>>(),
            )
        }
        .await;
        let session_ids = match listed {
            Ok(session_ids) => session_ids,
            Err(error) => {
                eprintln!("eukhe-daemon: listing RLM children at close failed: {error:#}");
                return;
            }
        };
        if let Err(error) = host.close_durable_children(&session_ids, reason).await {
            eprintln!("eukhe-daemon: RLM child close failed: {error:#}");
        }
    }
}

#[cfg(test)]
mod tests;
