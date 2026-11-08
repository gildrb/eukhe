//! The child-lifecycle concern: session creation, the busy/outcome reads
//! and the settle wait, and the spawn-admission outbox type
//! (`CreatedChild`).
use eukhe_core::durable::children as durable;

use super::{
    anyhow, json, Context, DaemonCommand, DaemonSessionLifecycle, Duration, Map, ParentIdentity,
    Path, PathBuf, Result, SupervisorChildSessionsInner, Value, CREATE_TIMEOUT_MS,
    IDLE_WAIT_GRACE_MS, RUNTIME_METADATA_PROMPT_MAX, STATE_TIMEOUT_MS,
};

pub(super) struct CreatedChild {
    pub(super) active_session_id: String,
    pub(super) session_name: Option<String>,
    pub(super) session_dir: String,
}

impl CreatedChild {
    /// The created session's live id (`activeSessionId`, the supervisor
    /// rows' `id` fallback) and name, from its summary.
    fn from_summary(summary: &Value, session_dir: &Path) -> Result<Self> {
        let active_session_id = summary
            .get("activeSessionId")
            .or_else(|| summary.get("id"))
            .and_then(Value::as_str)
            .filter(|id| !id.is_empty())
            .ok_or_else(|| anyhow!("supervisor returned a session summary without an id"))?;
        Ok(Self {
            active_session_id: active_session_id.to_string(),
            session_name: summary
                .get("sessionName")
                .and_then(Value::as_str)
                .map(str::to_string),
            session_dir: session_dir.to_string_lossy().to_string(),
        })
    }
}

/// A child's live facts from its `get_state`.
pub(super) struct ChildFacts {
    /// Work in flight: a run, queued input, or running descendants.
    pub(super) busy: bool,
    /// Its tree is paused.
    pub(super) paused: bool,
}

impl SupervisorChildSessionsInner {
    /// Create one child session over the supervisor link (no prompt yet).
    /// `depth` is the child's recursion depth; `session_dir` holds its
    /// persisted session; `model` is the resolved `provider/id` selector.
    #[allow(clippy::too_many_arguments)]
    pub(super) async fn create_child(
        &self,
        child_id: &str,
        name: Option<&str>,
        // The spawned task's prompt, mirrored into the create runtime
        // metadata.
        prompt: Option<&str>,
        depth: u32,
        model: &str,
        thinking: Option<&str>,
        cwd: &str,
        session_dir: &Path,
        // The parent's in-flight turn request the child anchors to (TS
        // `spawnedByRequestId` rides the child's session options, never
        // the runtime metadata).
        spawned_by_request_id: Option<&str>,
        runtime_metadata: Option<Value>,
        identity: &ParentIdentity,
        // The session id the child must persist under (the durable child
        // task derives it, so a rerun finds the same child); `None` lets
        // the worker mint one.
        requested_session_id: Option<&str>,
    ) -> Result<CreatedChild> {
        let mut config = json!({
            "cwd": cwd,
            "sessionDir": session_dir.to_string_lossy(),
            "rlmDepth": depth,
            "rlmMaxDepth": identity.rlm_max_depth,
        });
        if let Some(session_id) = requested_session_id {
            config["sessionId"] = json!(session_id);
        }
        if let Some((provider, id)) = model.split_once('/') {
            config["provider"] = json!(provider);
            config["model"] = json!(id);
        } else {
            config["model"] = json!(model);
        }
        if let Some(thinking) = thinking {
            config["thinking"] = json!(thinking);
        }
        if let Some(parent_file) = &identity.session_file {
            config["parentSessionPath"] = json!(parent_file);
        }
        if let Some(request_id) = spawned_by_request_id {
            config["spawnedByRequestId"] = json!(request_id);
        }
        if let Some(script) = &identity.child_script {
            config["script"] = json!(script);
            // The scripted engine rides the identity down the recursion
            // (the TS child runtime inherits the parent's sessionConfig, so
            // a harness child spawns harness grandchildren the same way).
            config["childScript"] = json!(script);
        }
        // The child starts from the family its parent has now (its
        // inherited layers, under its own profile and sets).
        let family = self
            .parent_cvar_family
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        if let Some(family) = family {
            config["cvarFamily"] = serde_json::to_value(family())?;
        }
        // Runtime metadata mirrors the TS subagent runtime identity.
        let runtime_metadata = runtime_metadata.map(|mut metadata| {
            if let Some(session_id) = &identity.session_id {
                metadata["parentSessionId"] = json!(session_id);
            }
            if let Some(parent_file) = &identity.session_file {
                metadata["parentSessionFile"] = json!(parent_file);
            }
            if let Some(prompt) =
                prompt.filter(|prompt| prompt.len() <= RUNTIME_METADATA_PROMPT_MAX)
            {
                metadata["prompt"] = json!(prompt);
            }
            // The resolved model rides the metadata so the supervisor's
            // display entry carries it for passive hydration.
            if let Some((provider, model_id)) = model.split_once('/') {
                metadata["model"] = json!({ "provider": provider, "modelId": model_id });
            }
            metadata
        });
        let create = DaemonCommand::Create {
            id: None,
            session_path: None,
            continue_recent: None,
            no_session: None,
            name: name.map(str::to_string),
            config: Some(config),
            runtime_metadata,
            lifecycle: Some(DaemonSessionLifecycle::Resident),
            env: None,
            launch_env: None,
            rest: Map::default(),
        };
        let summary = self
            .command(&create, CREATE_TIMEOUT_MS)
            .await
            .with_context(|| format!("spawn RLM child session {child_id}"))?;
        CreatedChild::from_summary(&summary, session_dir)
    }

    /// Whether the child worker still has work in flight (streaming,
    /// queued, or its own children still running - so a child stays
    /// running while any descendant does). `Err` means the child cannot be
    /// reached right now.
    pub(super) async fn child_busy(&self, active_session_id: &str) -> Result<bool> {
        Ok(self.child_facts(active_session_id).await?.busy)
    }

    /// The child's live facts from its `get_state`: busy (see
    /// [`Self::child_busy`]) and paused (its tree is paused). `Err` means
    /// the child cannot be reached right now.
    pub(super) async fn child_facts(&self, active_session_id: &str) -> Result<ChildFacts> {
        let command = DaemonCommand::GetState {
            id: None,
            active_session_id: active_session_id.to_string(),
            rest: Map::default(),
        };
        let state = self.command(&command, STATE_TIMEOUT_MS).await?;
        let flag = |name: &str| state.get(name).and_then(Value::as_bool).unwrap_or(false);
        Ok(ChildFacts {
            busy: flag("isStreaming")
                || flag("hasRunningSubagents")
                || state
                    .get("sessionActions")
                    .and_then(|actions| actions.get("queuedCount"))
                    .and_then(Value::as_u64)
                    .unwrap_or(0)
                    > 0,
            paused: flag("isPaused"),
        })
    }

    /// The child's run outcome (`get_run_outcome`), read from its own
    /// durable state: its run in flight, its last run's terminal, the
    /// background jobs it still owns, and its progress token. `Err` means
    /// the child cannot be reached right now.
    pub(super) async fn child_outcome(
        &self,
        active_session_id: &str,
    ) -> Result<durable::RlmChildOutcome> {
        let command = DaemonCommand::GetRunOutcome {
            id: None,
            active_session_id: active_session_id.to_string(),
            rest: Map::default(),
        };
        let outcome = self.command(&command, STATE_TIMEOUT_MS).await?;
        serde_json::from_value(outcome)
            .with_context(|| format!("read RLM child {active_session_id}'s run outcome"))
    }

    /// Best-effort bounded wait for one child, its descendants, and its
    /// background jobs to settle. The wait is a
    /// snapshot helper, not a gate: its timeout is not an error, and the
    /// caller re-reads the child's state afterwards (TS collect: "a
    /// timeout returns current snapshots, never an error").
    pub(super) async fn wait_for_child(&self, active_session_id: &str, budget: Duration) {
        if budget.is_zero() {
            return;
        }
        // The child's own descendants and background jobs keep it unsettled
        // (`child_outcome`), so the wait holds until they settle too.
        let command = DaemonCommand::WaitForIdle {
            id: None,
            active_session_id: active_session_id.to_string(),
            wait_for_rlm_quiescence: Some(true),
            rest: Map::from_iter([("waitForBackgroundJobs".to_owned(), json!(true))]),
        };
        let _ = self
            .command(&command, budget.as_millis() as u64 + IDLE_WAIT_GRACE_MS)
            .await;
    }
}

/// Complete a settled child's display entry (TS
/// `completeRlmSubagentRuntime`): `rlm-subagent.json` in the per-child
/// `session_dir` flips from `running` to `completed`, so a restarted parent
/// relists the child as completed rather than interrupted. Only a
/// successful run completes it; an entry naming another child or already
/// past `running` is left alone. Failures are logged, never the settle's.
pub(super) async fn complete_child_display(session_dir: PathBuf, child_id: String) {
    let completed = tokio::task::spawn_blocking(move || {
        let Some(mut display) = crate::rlm_ledger::read_rlm_subagent_display(&session_dir) else {
            return Ok(());
        };
        if display.child_id != child_id || display.status != "running" {
            return Ok(());
        }
        display.status = "completed".to_string();
        crate::rlm_ledger::write_rlm_subagent_display(&display).map(|_| ())
    })
    .await
    .unwrap_or_else(|error| Err(anyhow!(error)));
    if let Err(error) = completed {
        eprintln!("eukhe-daemon: RLM child display completion failed: {error:#}");
    }
}
