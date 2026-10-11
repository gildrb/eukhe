//! The child-lifecycle concern: session creation (create/launch), the
//! prompt/kill/close routing, the record refresh, and the
//! spawn-admission outbox types (`CreatedSessionIds`, `CreatedChild`).
use super::{
    anyhow, compact_rlm_text, json, ChildCloseReason, Context, DaemonCommand,
    DaemonSessionLifecycle, Duration, Map, ParentIdentity, Path, PathBuf, PromptInput, Result,
    SupervisorChildSessionsInner, Value, CREATE_TIMEOUT_MS, IDLE_WAIT_GRACE_MS, KILL_TIMEOUT_MS,
    PROMPT_TIMEOUT_MS, RUNTIME_METADATA_PROMPT_MAX, STATE_TIMEOUT_MS,
};

/// Parsed ids of one created child session.
struct CreatedSessionIds {
    active_session_id: String,
    session_id: Option<String>,
    session_file: Option<String>,
    session_name: Option<String>,
}

pub(super) struct CreatedChild {
    pub(super) active_session_id: String,
    pub(super) session_id: Option<String>,
    pub(super) session_file: Option<String>,
    pub(super) session_name: Option<String>,
    pub(super) session_dir: String,
    pub(super) summary_rlm_depth: Option<u64>,
}

impl CreatedChild {
    fn from_summary(summary: &Value, session_dir: &Path) -> Result<Self> {
        let ids = SupervisorChildSessionsInner::created_summary_ids(summary)?;
        Ok(Self {
            active_session_id: ids.active_session_id,
            session_id: ids.session_id,
            session_file: ids.session_file,
            session_name: ids.session_name,
            session_dir: session_dir.to_string_lossy().to_string(),
            summary_rlm_depth: summary.get("rlmDepth").and_then(Value::as_u64),
        })
    }
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
        // metadata (`None` for a depth-0 resident session).
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
        // Runtime metadata mirrors the TS subagent runtime identity; a
        // depth-0 resident session carries none (it is a plain root session).
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
        let created = CreatedChild::from_summary(&summary, session_dir)?;
        Ok(created)
    }

    /// Create and promptly admit one child's task (the depth-0 resident
    /// session path: the prompt is part of the awaited admission).
    #[allow(clippy::too_many_arguments)]
    pub(super) async fn launch_child(
        &self,
        child_id: &str,
        name: Option<&str>,
        prompt: &str,
        depth: u32,
        model: &str,
        thinking: Option<&str>,
        cwd: &str,
        session_dir: &Path,
        runtime_metadata: Option<Value>,
        identity: &ParentIdentity,
    ) -> Result<CreatedChild> {
        let created = self
            .create_child(
                child_id,
                name,
                None,
                depth,
                model,
                thinking,
                cwd,
                session_dir,
                /*spawned_by_request_id*/ None,
                runtime_metadata,
                identity,
                /*requested_session_id*/ None,
            )
            .await?;
        // A failed prompt tears the just-created session down (TS kills the
        // created session in the create-path catch block).
        if let Err(error) = self.prompt_child(&created.active_session_id, prompt).await {
            let _ = self
                .kill_child(&created.active_session_id, ChildCloseReason::Killed)
                .await;
            return Err(error);
        }
        Ok(created)
    }

    /// Parse a created-session summary into its ids (TS `createRlmRootSession`
    /// reads `activeSessionId`/`sessionId`/`sessionFile`/`sessionName`).
    fn created_summary_ids(summary: &Value) -> Result<CreatedSessionIds> {
        let active_session_id = summary
            .get("activeSessionId")
            .or_else(|| summary.get("id"))
            .and_then(Value::as_str)
            .filter(|id| !id.is_empty())
            .ok_or_else(|| anyhow!("supervisor returned a session summary without an id"))?;
        Ok(CreatedSessionIds {
            active_session_id: active_session_id.to_string(),
            session_id: summary
                .get("sessionId")
                .and_then(Value::as_str)
                .map(str::to_string),
            session_file: summary
                .get("sessionFile")
                .and_then(Value::as_str)
                .map(str::to_string),
            session_name: summary
                .get("sessionName")
                .and_then(Value::as_str)
                .map(str::to_string),
        })
    }

    pub(super) async fn prompt_child(&self, active_session_id: &str, prompt: &str) -> Result<()> {
        let command = DaemonCommand::Prompt {
            id: None,
            active_session_id: active_session_id.to_string(),
            message: prompt.to_string(),
            input: PromptInput {
                content: None,
                images: None,
                streaming_behavior: None,
                queue_if_busy: None,
                expand_prompt_templates: None,
                source: Some(json!("rpc")),
                agent_message_id: None,
                custom_message: None,
                queue_key: None,
                prefix_messages: None,
                admission_id: None,
                rlm_notice_nonce: None,
            },
            rest: Map::default(),
        };
        self.command(&command, PROMPT_TIMEOUT_MS)
            .await
            .with_context(|| format!("prompt RLM child session {active_session_id}"))?;
        Ok(())
    }

    pub(super) async fn kill_child(
        &self,
        active_session_id: &str,
        reason: ChildCloseReason,
    ) -> Result<()> {
        let mut rest = serde_json::Map::new();
        if let Some(marker) = reason.wire_marker() {
            rest.insert("rlmCloseReason".to_string(), json!(marker));
        }
        let command = DaemonCommand::Kill {
            id: None,
            active_session_id: active_session_id.to_string(),
            rest,
        };
        self.command(&command, KILL_TIMEOUT_MS)
            .await
            .with_context(|| format!("kill RLM child session {active_session_id}"))?;
        Ok(())
    }

    /// Whether the child worker still has work in flight (streaming,
    /// queued, or its own children still running - so a child stays
    /// running while any descendant does). `Err` means the child cannot be
    /// reached right now.
    pub(super) async fn child_busy(&self, active_session_id: &str) -> Result<bool> {
        let command = DaemonCommand::GetState {
            id: None,
            active_session_id: active_session_id.to_string(),
            rest: Map::default(),
        };
        let state = self.command(&command, STATE_TIMEOUT_MS).await?;
        let flag = |name: &str| state.get(name).and_then(Value::as_bool).unwrap_or(false);
        Ok(flag("isStreaming")
            || flag("hasRunningSubagents")
            || state
                .get("sessionActions")
                .and_then(|actions| actions.get("queuedCount"))
                .and_then(Value::as_u64)
                .unwrap_or(0)
                > 0)
    }

    /// The child's final answer text, compacted for the roster preview.
    pub(super) async fn child_answer(&self, active_session_id: &str) -> Result<Option<String>> {
        let command = DaemonCommand::GetLastAssistantText {
            id: None,
            active_session_id: active_session_id.to_string(),
            rest: Map::default(),
        };
        let answer = self.command(&command, STATE_TIMEOUT_MS).await?;
        Ok(answer
            .get("text")
            .and_then(Value::as_str)
            .filter(|text| !text.is_empty())
            .map(compact_rlm_text))
    }

    /// Best-effort bounded wait for one child and its descendants to go
    /// idle. The wait is a
    /// snapshot helper, not a gate: its timeout is not an error, and the
    /// caller re-reads the child's state afterwards (TS collect: "a
    /// timeout returns current snapshots, never an error").
    pub(super) async fn wait_for_child(&self, active_session_id: &str, budget: Duration) {
        if budget.is_zero() {
            return;
        }
        // The child's own descendants keep it busy (`child_busy`), so the
        // wait holds until they settle too.
        let command = DaemonCommand::WaitForIdle {
            id: None,
            active_session_id: active_session_id.to_string(),
            wait_for_rlm_quiescence: Some(true),
            rest: Map::default(),
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
