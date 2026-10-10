//! The dispatch surface: command routing, the getters, the queue and abort
//! family, and the session close (`kill`, `rename`).

use std::sync::Arc;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::session_engine::agent_messaging::AgentFamilyRelationship;
use eukhe_core::session_engine::messages::SESSION_RENAMED_CUSTOM_TYPE;
use eukhe_durable::harness::types::{ConversationAbortOptions, InputSubmissionDraft, WhenBusy};
use serde_json::{json, Value};

use super::durable_host::bridge::{QueuedInput, QueuedMode};
use super::durable_host::meta;
use super::durable_host::suspended::{write_suspended, SuspendedState, WithdrawnInput};
use super::durable_host::wire_messages::{entry_wire_message, transcript_messages};
use super::{response_failure, response_success, HostedSession, KillCloseReason, Worker};
use crate::protocol::DaemonResponse;

impl Worker {
    pub(crate) async fn dispatch(&self, command_type: &str, payload: &Value) -> DaemonResponse {
        match command_type {
            "create" => self.handle_create(payload).await,
            "attach" => self.handle_attach(payload),
            "detach" => self.handle_detach(payload),
            "prompt" => self.handle_prompt(payload, false).await,
            "prompt_and_wait" => self.handle_prompt(payload, true).await,
            "steer" => self.handle_queue(payload, WhenBusy::Steer).await,
            "follow_up" => self.handle_queue(payload, WhenBusy::FollowUp).await,
            "abort" => self.handle_abort(AbortQueue::Suspend).await,
            "abort_and_send_queued" => self.handle_abort(AbortQueue::Send).await,
            "abort_and_clear_queue" => self.handle_abort(AbortQueue::Clear).await,
            "start_side_question" => {
                if let Err(response) = self.require_created("start_side_question") {
                    return response;
                }
                self.side_questions.start(payload)
            }
            "abort_side_question" => {
                if let Err(response) = self.require_created("abort_side_question") {
                    return response;
                }
                self.side_questions.abort(payload)
            }
            "compact" => self.handle_compaction(payload).await,
            "abort_compaction" => self.handle_abort_compaction().await,
            "set_auto_compaction" => self.handle_set_auto_compaction(payload),
            "wait_for_idle" => self.handle_wait_for_idle(payload).await,
            "wait_for_headless_completion" => {
                self.handle_wait_for_headless_completion(payload).await
            }
            "get_state" => self.handle_get_state(),
            "get_messages" => self.handle_get_messages(),
            "get_session_header" => self.handle_get_session_header(),
            "get_session_stats" => self.handle_get_session_stats(),
            "get_model_catalog" => self.handle_get_model_catalog(),
            "get_queue" => self.handle_get_queue(),
            "clear_queue" => self.handle_clear_queue().await,
            "get_last_assistant_text" => self.handle_get_last_assistant_text(),
            "get_connection_state" => self.handle_get_connection_state(),
            "get_mcp_connections" => self.handle_get_mcp_connections().await,
            "set_mcp_static_token" => self.handle_set_mcp_static_token(payload).await,
            "remove_mcp_connection" => self.handle_remove_mcp_connection(payload).await,
            "get_rlm_children" => self.handle_get_rlm_children().await,
            "get_context_tree" => self.handle_get_context_tree().await,
            "get_commands" => self.handle_get_commands(),
            "get_resource_snapshot" => self.handle_get_resource_snapshot(),
            "get_session_context" => self.handle_get_session_context().await,
            "get_system_prompt" => self.handle_get_system_prompt().await,
            "get_chat_view" => self.handle_get_chat_view().await,
            "get_tool_definition" => self.handle_get_tool_definition(payload).await,
            "get_rlm_max_depth_status" => self.handle_get_rlm_max_depth_status().await,
            "get_available_models" => self.handle_get_available_models().await,
            "worker_deliver_message" => self.handle_worker_deliver_message(payload).await,
            "kill" => self.handle_kill(payload).await,
            "shutdown" => self.handle_shutdown().await,
            "rename" => self.handle_rename("rename", payload).await,
            "set_session_name" => self.handle_rename("set_session_name", payload).await,
            "mark_anthropic_warning_shown" => self.handle_mark_anthropic_warning_shown().await,
            "rename_saved_session" => self.handle_rename_saved_session(payload).await,
            "delete_saved_session" => self.handle_delete_saved_session(payload).await,
            "replace_acp_mcp_servers" => self.handle_replace_acp_mcp_servers(payload),
            "set_model" => self.handle_set_model(payload).await,
            "set_thinking_level" => self.handle_set_thinking_level(payload).await,
            "cycle_model" => self.handle_cycle_model(payload).await,
            "set_scoped_models" => self.handle_set_scoped_models(payload),
            "cycle_thinking_level" => self.handle_cycle_thinking_level().await,
            "set_service_tier" => self.handle_set_service_tier(payload).await,
            "set_transport" => self.handle_set_transport(payload),
            "set_steering_mode" => self.handle_set_queue_mode("set_steering_mode", payload),
            "set_follow_up_mode" => self.handle_set_queue_mode("set_follow_up_mode", payload),
            "set_auto_retry" => self.handle_set_auto_retry(payload),
            "abort_retry" => self.handle_abort_retry().await,
            "get_session_tree" => self.tree_navigation.get_session_tree().await,
            "get_user_messages_for_forking" => {
                self.tree_navigation.get_user_messages_for_forking().await
            }
            "set_session_entry_label" => {
                self.tree_navigation.set_session_entry_label(payload).await
            }
            "navigate_tree" => self.handle_navigate_tree(payload).await,
            "fork" => self.handle_fork(payload).await,
            "abort_branch_summary" => {
                self.tree_navigation.abort();
                response_success(None, "abort_branch_summary", None)
            }
            "export_html" => self.exports.export_html(payload).await,
            "export_jsonl" => self.exports.export_jsonl(payload).await,
            "mutate_queued_message" => self.handle_mutate_queued_message(payload).await,
            "resume_queue" => self.handle_resume_queue().await,
            "factory_activity" => self.handle_factory_activity(payload).await,
            "execute_bash" => self.handle_execute_bash(payload),
            "execute_bash_and_wait" => self.handle_execute_bash_and_wait(payload).await,
            "abort_bash" => self.handle_abort_bash().await,
            "list_kernel_bash" | "tail_kernel_bash" | "kill_kernel_bash" => {
                self.handle_kernel_bash_activity(command_type, payload)
                    .await
            }
            "append_custom_message" => self.handle_append_custom_message(payload).await,
            "restore_next_turn" => self.handle_restore_next_turn(payload).await,
            "restore_actions" => self.handle_restore_actions(payload).await,
            "refine" => self.handle_refine(payload).await,
            "reload" => self.handle_reload(),
            "cancel_rlm_child" => self.handle_cancel_rlm_child(payload).await,
            "delete_rlm_subagent" => self.handle_delete_rlm_subagent(payload).await,
            "set_rlm_max_depth" => self.handle_set_rlm_max_depth(payload).await,
            "acquire_session_input_pause" => self.handle_acquire_session_input_pause(payload),
            "release_session_input_pause" => self.handle_release_session_input_pause(payload),
            "cancel_prompt_admission" => self.handle_cancel_prompt_admission(payload).await,
            "new_session" => self.handle_new_session(payload).await,
            "switch_session" => self.handle_switch_session(payload).await,
            "import_jsonl" => self.handle_import_jsonl(payload).await,
            "agent_messages_status" => self.handle_agent_messages_status(),
            "agent_messages_pause" => self.handle_agent_messages_pause().await,
            "agent_messages_resume" => self.handle_agent_messages_resume(),
            "agent_messages_clear" => self.handle_agent_messages_clear().await,
            "cron_list" => self.handle_cron_list(payload),
            "heartbeats_list" => self.handle_heartbeats_list(),
            "heartbeat_manage" => self.handle_heartbeat_manage(payload).await,
            "cron_add" => self.handle_cron_add(payload).await,
            "cron_cancel" => self.handle_cron_cancel(payload).await,
            "heartbeat_get" => self.handle_heartbeat_get(payload),
            "heartbeat_set" => self.handle_heartbeat_set(payload).await,
            "heartbeat_update" => self.handle_heartbeat_update(payload).await,
            other => response_failure(
                None,
                command_type,
                &format!("Unknown worker command: {other}"),
                None,
            ),
        }
    }

    // DaemonResponse is the wire response struct and is deliberately wide;
    // the error channel carries the whole response.
    #[allow(clippy::result_large_err)]
    pub(crate) fn require_created(&self, command_type: &str) -> Result<(), DaemonResponse> {
        let core = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if !core.created {
            return Err(response_failure(
                None,
                command_type,
                "Session is still initializing",
                None,
            ));
        }
        // A command dispatched while the graceful stop is closing must not
        // start new work the exit would orphan.
        if core.shutdown_requested {
            return Err(response_failure(
                None,
                command_type,
                "Session is shutting down",
                None,
            ));
        }
        Ok(())
    }

    /// `replace_acp_mcp_servers`: the session's owner-fenced ACP MCP store.
    fn handle_replace_acp_mcp_servers(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "replace_acp_mcp_servers";
        let owner_id = payload
            .get("ownerId")
            .and_then(Value::as_str)
            .unwrap_or_default();
        if owner_id.is_empty() {
            return response_failure(None, COMMAND, "ACP MCP owner id is required", None);
        }
        let servers: Vec<eukhe_core::mcp::AcpMcpServerConfig> = payload
            .get("servers")
            .cloned()
            .map(|servers| serde_json::from_value(servers).unwrap_or_default())
            .unwrap_or_default();
        // The agent cannot adopt a different MCP tool list mid-run.
        let busy = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .is_busy();
        if !servers.is_empty() && busy {
            return response_failure(
                None,
                COMMAND,
                "Cannot replace ACP MCP servers while the agent is running",
                None,
            );
        }
        // The hosted session owns the MCP manager its prompt gating reads;
        // before create the worker-level store serves.
        let manager = self.session.get().map_or_else(
            || Arc::clone(&self.acp_mcp),
            |hosted| Arc::clone(&hosted.deps().mcp),
        );
        let manager = manager
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        match manager.replace_acp_servers(&servers, owner_id) {
            Ok(_) => response_success(None, COMMAND, None),
            Err(error) => {
                // Roll back any partially applied configuration.
                if manager.can_release_acp_servers(owner_id) {
                    let _ = manager.replace_acp_servers(&[], owner_id);
                }
                response_failure(None, COMMAND, &error.to_string(), None)
            }
        }
    }

    /// Abort the main conversation's run. Durable `abort` withdraws the
    /// queued inputs; the worker keeps them per `queue`: suspended (shown,
    /// resubmitted by `resume_queue` or the next steered prompt), sent
    /// again at once, or dropped. The withdrawn inputs live in the durable
    /// `eukhe.daemon.suspended` document on the main conversation, so a
    /// worker restart keeps them.
    pub(crate) async fn handle_abort(&self, queue: AbortQueue) -> DaemonResponse {
        let command = queue.command();
        let hosted = match self.hosted(command) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let main = match hosted.main() {
            Ok(main) => main,
            Err(error) => return response_failure(None, command, &error.to_string(), None),
        };
        // The inbox as committed (the bridge's preview mirror may lag a
        // just-queued input): the inputs the abort withdraws.
        let withdrawn = match super::durable_host::bridge::inbox_previews(
            hosted.harness(),
            main.id(),
            &BACKGROUND_CONTEXT,
        )
        .await
        {
            Ok(inbox) => inbox,
            Err(error) => return response_failure(None, command, &error.to_string(), None),
        };
        if let Err(error) = main
            .abort(ConversationAbortOptions::default(), &BACKGROUND_CONTEXT)
            .await
        {
            return response_failure(None, command, &error.to_string(), None);
        }
        // The durable rewrite: the withdrawn inbox inputs join the
        // suspended and held ones, then `queue` decides their fate. A
        // live input-pause lease keeps a `send` queued as held (the
        // release delivers it), exactly like a fresh admission.
        let paused = self.input_pauses.paused();
        let cleared = match mutate_withdrawn(&hosted, &self.core, &self.events, move |mut state| {
            state
                .suspended
                .extend(withdrawn.iter().map(WithdrawnInput::from));
            match queue {
                AbortQueue::Suspend => {
                    state.suspended.append(&mut state.held);
                    (state, Vec::new())
                }
                AbortQueue::Send => {
                    let mut taken = std::mem::take(&mut state.suspended);
                    taken.append(&mut state.held);
                    if paused {
                        state.held = taken;
                        (state, Vec::new())
                    } else {
                        let taken = taken.iter().map(WithdrawnInput::queued).collect();
                        (state, taken)
                    }
                }
                AbortQueue::Clear => {
                    let mut taken = std::mem::take(&mut state.suspended);
                    taken.append(&mut state.held);
                    let taken = taken.iter().map(WithdrawnInput::queued).collect();
                    (state, taken)
                }
            }
        })
        .await
        {
            Ok(cleared) => cleared,
            Err(error) => return response_failure(None, command, &error, None),
        };
        self.emit_action_update();
        let data = match queue {
            AbortQueue::Suspend => None,
            AbortQueue::Send => {
                if let Err(error) = resubmit(&hosted, cleared).await {
                    return response_failure(None, command, &error, None);
                }
                None
            }
            AbortQueue::Clear => Some(lane_texts(&cleared)),
        };
        hosted.events_delivered().await;
        response_success(None, command, data)
    }

    /// Resubmit the suspended inputs (an abort suspended them; a cron or
    /// heartbeat fire resumes them — the pause-held ones resume through
    /// the pause release instead).
    pub(crate) async fn resume_suspended_inputs(
        &self,
        hosted: &HostedSession,
    ) -> Result<bool, String> {
        resubmit_suspended(hosted, &self.core, &self.events).await
    }

    fn handle_get_state(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("get_state") {
            return response;
        }
        let core = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let summary = self.summary_locked(&core);
        response_success(
            None,
            "get_state",
            Some(serde_json::to_value(&summary).unwrap_or(Value::Null)),
        )
    }

    /// `get_session_header`: the session header (`{ header: ... }`).
    fn handle_get_session_header(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("get_session_header") {
            return response;
        }
        let core = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let mut header = json!({
            "type": "session",
            "id": core.session_id,
            "timestamp": core.created_at,
            "cwd": core.cwd,
        });
        if core.rlm_depth > 0 {
            header["rlmDepth"] = json!(core.rlm_depth);
        }
        response_success(
            None,
            "get_session_header",
            Some(json!({ "header": header })),
        )
    }

    /// `get_session_stats`: message counts, the main conversation's
    /// cumulative usage (`pi.usage`), and the tray's context usage.
    fn handle_get_session_stats(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("get_session_stats") {
            return response;
        }
        let core = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let Some(view) = core.view.as_ref() else {
            return response_failure(
                None,
                "get_session_stats",
                "Session is still initializing",
                None,
            );
        };
        let mirror = view.translator.mirror();
        let messages: Vec<Value> = mirror
            .entries
            .iter()
            .filter_map(entry_wire_message)
            .collect();
        let count = |role: &str| {
            messages
                .iter()
                .filter(|message| crate::types::message_role(message) == Some(role))
                .count()
        };
        let tool_calls: usize = messages
            .iter()
            .filter(|message| crate::types::message_role(message) == Some("assistant"))
            .filter_map(|message| message.get("content").and_then(Value::as_array))
            .map(|blocks| {
                blocks
                    .iter()
                    .filter(|block| block.get("type").and_then(Value::as_str) == Some("toolCall"))
                    .count()
            })
            .sum();
        let (mut input, mut output, mut cache_read, mut cache_write, mut cost) = (0, 0, 0, 0, 0.0);
        for usage in mirror
            .usage
            .models
            .values()
            .chain(mirror.usage.tools.values())
        {
            input += usage.input;
            output += usage.output;
            cache_read += usage.cache_read;
            cache_write += usage.cache_write;
            cost += usage.cost.total;
        }
        let mut stats = json!({
            "sessionFile": core.session_file(),
            "sessionId": core.session_id,
            "userMessages": count("user"),
            "assistantMessages": count("assistant"),
            "toolCalls": tool_calls,
            "toolResults": count("toolResult"),
            "totalMessages": messages.len(),
            "tokens": {
                "input": input,
                "output": output,
                "cacheRead": cache_read,
                "cacheWrite": cache_write,
                "total": input + output + cache_read + cache_write,
            },
            "cost": cost,
        });
        // The tray's context usage, the estimate the attach snapshot
        // carries; omitted without a model context window (TS sessions
        // without a model).
        if let Some(window) = crate::state_getters::model_context_window(
            super::model_metadata(&core, &self.session).as_ref(),
        ) {
            stats["contextUsage"] =
                crate::state_getters::mirror_context_usage(&mirror.entries, window);
        }
        response_success(None, "get_session_stats", Some(stats))
    }

    fn handle_get_messages(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("get_messages") {
            return response;
        }
        let core = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let messages = core
            .view
            .as_ref()
            .map(|view| transcript_messages(&view.translator.mirror().entries))
            .unwrap_or_default();
        response_success(None, "get_messages", Some(json!({ "messages": messages })))
    }

    fn handle_get_queue(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("get_queue") {
            return response;
        }
        let snapshot = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            super::session_snapshot(&core)
        };
        response_success(
            None,
            "get_queue",
            Some(json!({ "steering": snapshot.steering, "followUp": snapshot.follow_ups })),
        )
    }

    /// `clear_queue`: withdraw every queued input (inbox, suspended, and
    /// held) and answer their texts. The durable store clears with them.
    async fn handle_clear_queue(&self) -> DaemonResponse {
        const COMMAND: &str = "clear_queue";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let inbox = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            core.view
                .as_ref()
                .map(|view| view.inbox.clone())
                .unwrap_or_default()
        };
        let main_id = hosted.main().ok().map(|main| main.id());
        let mut cleared = Vec::new();
        for input in inbox {
            match hosted
                .harness()
                .abort_submission(input.id, main_id, &BACKGROUND_CONTEXT)
                .await
            {
                Ok(eukhe_durable::harness::AbortSubmissionResult::Aborted) => cleared.push(input),
                Ok(_) => {}
                Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
            }
        }
        let withdrawn = match mutate_withdrawn(&hosted, &self.core, &self.events, |state| {
            let cleared = state.queued();
            (SuspendedState::default(), cleared)
        })
        .await
        {
            Ok(withdrawn) => withdrawn,
            Err(error) => return response_failure(None, COMMAND, &error, None),
        };
        cleared.extend(withdrawn);
        self.emit_action_update();
        response_success(None, COMMAND, Some(lane_texts(&cleared)))
    }

    fn handle_get_last_assistant_text(&self) -> DaemonResponse {
        if let Err(response) = self.require_created("get_last_assistant_text") {
            return response;
        }
        let core = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let text = core.view.as_ref().and_then(|view| {
            view.translator
                .mirror()
                .entries
                .iter()
                .rev()
                .filter(|entry| entry.kind == "pi.assistant")
                .find_map(entry_wire_message)
                .map(|message| crate::types::message_text(&message))
        });
        response_success(
            None,
            "get_last_assistant_text",
            Some(json!({ "text": text })),
        )
    }

    /// `kill`: abort the run, close the session (Harness close, lease
    /// release), and announce `session_closed`. `killed` cancels the
    /// session's scheduled jobs and archives it; `replaced` cancels its RLM
    /// heartbeats; `shutdown` keeps both (the later wake resumes it).
    async fn handle_kill(&self, payload: &Value) -> DaemonResponse {
        let reason = KillCloseReason::from_payload(payload);
        self.side_questions
            .abort_all_and_settle(super::SIDE_QUESTION_SETTLE_TIMEOUT)
            .await;
        match reason {
            KillCloseReason::Killed => self.cancel_session_scheduled_jobs().await,
            KillCloseReason::Replaced => self.cancel_session_rlm_heartbeats().await,
            KillCloseReason::Shutdown => {}
        }
        // TS `closeSessionOnce(reason)` cascades the close to the session's
        // resident RLM children with the same reason before its own close.
        if let Some(hosted) = self.session.get() {
            let child_reason = match reason {
                KillCloseReason::Killed => crate::rlm_children::ChildCloseReason::Killed,
                KillCloseReason::Shutdown => crate::rlm_children::ChildCloseReason::Shutdown,
                KillCloseReason::Replaced => crate::rlm_children::ChildCloseReason::Replaced,
            };
            self.close_rlm_children(&hosted, child_reason).await;
        }
        if let Some(hosted) = self.session.get() {
            if reason != KillCloseReason::Shutdown {
                if let Err(error) = meta::mark_archived(hosted.harness(), &BACKGROUND_CONTEXT).await
                {
                    return response_failure(None, "kill", &error.to_string(), None);
                }
                // The archive reaches telemetry before the close ends the
                // session (the old engine's `session archived` order).
                if let Some(telemetry) = hosted.telemetry() {
                    telemetry.note_archived();
                }
            }
        }
        self.core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .created = false;
        self.user_bash.abort().await;
        self.close_hosted_session().await;
        let active_session_id = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .active_session_id
            .clone();
        let _ = self.emit_session_closed(&active_session_id, reason.session_closed_reason());
        let _ = self.record_recovery(false, reason.recovery_operation());
        // The pane reporter releases its pane as the last write.
        let reporter = std::mem::take(
            &mut *self
                .herdr
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
        );
        reporter.release().await;
        response_success(None, "kill", None)
    }

    /// Abort the run and close the hosted session (the Harness flushes,
    /// the lease releases).
    pub(crate) async fn close_hosted_session(&self) {
        let Some(hosted) = self.session.take() else {
            return;
        };
        if let Ok(main) = hosted.main() {
            if let Err(error) = main
                .abort(ConversationAbortOptions::default(), &BACKGROUND_CONTEXT)
                .await
            {
                eprintln!("eukhe-daemon worker: aborting the run at close failed: {error}");
            }
        }
        hosted.events_delivered().await;
        if let Err(error) = hosted.close(&BACKGROUND_CONTEXT).await {
            eprintln!("eukhe-daemon worker: closing the session failed: {error}");
        }
    }

    /// `mark_anthropic_warning_shown`: the once-per-session marker.
    async fn handle_mark_anthropic_warning_shown(&self) -> DaemonResponse {
        const NAME: &str = "mark_anthropic_warning_shown";
        let hosted = match self.hosted(NAME) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let shown = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .anthropic_warning_shown;
        if shown {
            return response_success(None, NAME, None);
        }
        match meta::mark_anthropic_warning_shown(hosted.harness(), &BACKGROUND_CONTEXT).await {
            Ok(()) => {
                self.core
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .anthropic_warning_shown = true;
                response_success(None, NAME, None)
            }
            Err(error) => response_failure(None, NAME, &error.to_string(), None),
        }
    }

    pub(crate) async fn handle_rename(&self, command: &str, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted(command) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let name = payload.get("name").and_then(Value::as_str).unwrap_or("");
        if name.trim().is_empty() {
            return response_failure(None, command, "Session name cannot be empty", None);
        }
        // One rename at a time: the previous-name read, the name write, and
        // its notice must not interleave with another rename's (the notice
        // would name a contradicted history).
        let _rename = self.rename_gate.lock().await;
        let previous = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .session_name
            .clone();
        if let Err(error) = meta::set_session_name(
            hosted.harness(),
            Some(name.to_string()),
            &BACKGROUND_CONTEXT,
        )
        .await
        {
            return response_failure(None, command, &error.to_string(), None);
        }
        let summary = {
            let mut core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            core.session_name = Some(name.to_string());
            self.summary_locked(&core)
        };
        // Every attached client re-reads the name.
        self.emit_worker_event(json!({ "type": "session_info_changed", "name": name }));
        self.push_roster_delta();
        // TS #2529 `applyStateSessionName`: a rename that changed an
        // existing name leaves the renamed session a displayed transcript
        // notice (" by parent" when the parent session directed it); a
        // first name leaves none. The notice is advisory: the name already
        // committed, so a failed notice is reported, never the rename's.
        if let Some(previous) = previous.filter(|previous| previous != name) {
            let renamed_by_parent = payload.get("renamedBy").and_then(Value::as_str)
                == Some(AgentFamilyRelationship::Parent.as_str());
            let suffix = if renamed_by_parent { " by parent" } else { "" };
            let notice = json!({
                "customType": SESSION_RENAMED_CUSTOM_TYPE,
                "content": format!("Session renamed `{previous}` -> `{name}`{suffix}"),
                "display": true,
                "timestamp": crate::util::now_ms(),
            });
            let written = async {
                let main = hosted.main()?;
                crate::session_custom::write_custom_row(&main, &notice).await
            }
            .await;
            if let Err(error) = written {
                eprintln!("eukhe-daemon worker: the session_renamed notice failed: {error:#}");
            }
        }
        response_success(
            None,
            command,
            Some(serde_json::to_value(&summary).unwrap_or(Value::Null)),
        )
    }
}

/// What an abort does with the queued inputs it withdraws.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AbortQueue {
    /// `abort`: keep them suspended.
    Suspend,
    /// `abort_and_send_queued`: submit them again at once.
    Send,
    /// `abort_and_clear_queue`: drop them.
    Clear,
}

impl AbortQueue {
    fn command(self) -> &'static str {
        match self {
            Self::Suspend => "abort",
            Self::Send => "abort_and_send_queued",
            Self::Clear => "abort_and_clear_queue",
        }
    }
}

/// Submit `inputs` again on the main conversation, in order.
async fn resubmit(hosted: &HostedSession, inputs: Vec<QueuedInput>) -> Result<(), String> {
    let main = hosted.main().map_err(|error| error.to_string())?;
    for input in inputs {
        main.submit(
            InputSubmissionDraft {
                request_id: None,
                content: input.content,
                when_busy: Some(match input.mode {
                    QueuedMode::Steer => WhenBusy::Steer,
                    QueuedMode::FollowUp => WhenBusy::FollowUp,
                }),
            },
            &BACKGROUND_CONTEXT,
        )
        .await
        .map_err(|error| error.to_string())?;
    }
    Ok(())
}

/// `{ steering: [...], followUp: [...] }` of `inputs`.
fn lane_texts(inputs: &[QueuedInput]) -> Value {
    let lane = |mode: QueuedMode| {
        inputs
            .iter()
            .filter(|input| input.mode == mode)
            .map(|input| input.text.clone())
            .collect::<Vec<String>>()
    };
    json!({ "steering": lane(QueuedMode::Steer), "followUp": lane(QueuedMode::FollowUp) })
}

/// The cached withdrawn-input state as the durable document's value.
fn withdrawn_of(core: &super::SessionCore) -> SuspendedState {
    SuspendedState {
        suspended: core.suspended.iter().map(WithdrawnInput::from).collect(),
        held: core.held.iter().map(WithdrawnInput::from).collect(),
    }
}

/// Install `state` into the caches (the durable write already succeeded).
fn install_withdrawn(core: &mut super::SessionCore, state: &SuspendedState) {
    core.suspended = state.suspended.iter().map(WithdrawnInput::queued).collect();
    core.held = state.held.iter().map(WithdrawnInput::queued).collect();
}

/// One serialized read-modify-write of the durable withdrawn-input store
/// (the `eukhe.daemon.suspended` document on the main conversation):
/// `decide` maps the cached state to `(next, outcome)`, the next state is
/// committed, and the caches follow. The whole exchange holds the core's
/// mutation gate, so concurrent mutations cannot lose one another's
/// writes.
pub(crate) async fn mutate_withdrawn<T, F>(
    hosted: &HostedSession,
    core: &Arc<std::sync::Mutex<super::SessionCore>>,
    events: &Arc<super::EventPump>,
    decide: F,
) -> Result<T, String>
where
    F: FnOnce(SuspendedState) -> (SuspendedState, T),
{
    let gate = {
        let core = core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        std::sync::Arc::clone(&core.withdrawn_gate)
    };
    let _serialized = gate.lock().await;
    let current = {
        let core = core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        withdrawn_of(&core)
    };
    let (next, outcome) = decide(current);
    let main = hosted.main().map_err(|error| error.to_string())?;
    write_suspended(hosted.harness(), main.id(), &next, &BACKGROUND_CONTEXT)
        .await
        .map_err(|error| error.to_string())?;
    {
        let mut core = core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        install_withdrawn(&mut core, &next);
        super::emit_action_update_locked(&mut core, events);
    }
    Ok(outcome)
}

/// Replace the whole durable withdrawn-input store (the caller computed
/// the complete next state) under the same mutation gate.
pub(crate) async fn set_withdrawn(
    hosted: &HostedSession,
    core: &Arc<std::sync::Mutex<super::SessionCore>>,
    events: &Arc<super::EventPump>,
    state: SuspendedState,
) -> Result<(), String> {
    mutate_withdrawn(hosted, core, events, move |_| (state, ())).await
}

/// Which withdrawn list a resume drains: the abort-suspended inputs
/// (`resume_queue`, a fire's resume site) or the ones an input-pause
/// lease holds (the pause release).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WithdrawnList {
    Suspended,
    Held,
}

/// Drain one withdrawn list back into the conversation: the inputs leave
/// the durable store and resubmit, in order. `false` when the list was
/// empty. The resubmission happens inside the mutation gate and before
/// the store clears, so a crash mid-resume leaves the inputs in the
/// store (re-drained on the next resume), never lost silently.
pub(crate) async fn drain_withdrawn(
    hosted: &HostedSession,
    core: &Arc<std::sync::Mutex<super::SessionCore>>,
    events: &Arc<super::EventPump>,
    list: WithdrawnList,
) -> Result<bool, String> {
    let gate = {
        let core = core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        std::sync::Arc::clone(&core.withdrawn_gate)
    };
    let _serialized = gate.lock().await;
    let current = {
        let core = core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        withdrawn_of(&core)
    };
    if match list {
        WithdrawnList::Suspended => current.suspended.is_empty(),
        WithdrawnList::Held => current.held.is_empty(),
    } {
        return Ok(false);
    }
    let drained: Vec<QueuedInput> = match list {
        WithdrawnList::Suspended => current
            .suspended
            .iter()
            .map(WithdrawnInput::queued)
            .collect(),
        WithdrawnList::Held => current.held.iter().map(WithdrawnInput::queued).collect(),
    };
    resubmit(hosted, drained).await?;
    let next = match list {
        WithdrawnList::Suspended => SuspendedState {
            suspended: Vec::new(),
            held: current.held,
        },
        WithdrawnList::Held => SuspendedState {
            suspended: current.suspended,
            held: Vec::new(),
        },
    };
    let main = hosted.main().map_err(|error| error.to_string())?;
    write_suspended(hosted.harness(), main.id(), &next, &BACKGROUND_CONTEXT)
        .await
        .map_err(|error| error.to_string())?;
    {
        let mut core = core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        install_withdrawn(&mut core, &next);
        super::emit_action_update_locked(&mut core, events);
    }
    Ok(true)
}

/// Resubmit the abort-suspended inputs on the main conversation; `false`
/// when there was nothing to resume.
pub(crate) async fn resubmit_suspended(
    hosted: &HostedSession,
    core: &Arc<std::sync::Mutex<super::SessionCore>>,
    events: &Arc<super::EventPump>,
) -> Result<bool, String> {
    drain_withdrawn(hosted, core, events, WithdrawnList::Suspended).await
}
