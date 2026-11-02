//! Which daemon commands a tab may `run`, and how they are sent: the
//! compiled Bend core decides (`bend/dash_policy.bend`, entry
//! `bend/ffi_dash_policy.bend`, laws `laws/dash_policy.bend`). The bound
//! session's user controls go to the bound session (the bridge sets its
//! id); catalog commands (saved sessions, schedules) go with no session id;
//! everything else is refused, a command the core does not list included.

use eukhe_bend::wire::{Reader, Writer};
use eukhe_bend::{call, expect_core, Entry, Error};
use eukhe_types::daemon::DaemonCommand;

/// Whether, and how, the dashboard runs one command for a tab.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Verdict {
    /// Sent for the bound session (the bridge sets `activeSessionId`).
    Bound,
    /// Sent with no session id: the command names its sessions itself.
    Catalog,
    Refused,
}

/// The wire name (`type`) of `command`. The match names every variant, so
/// a new daemon command does not compile until it has a name here; the
/// core refuses every name it does not list.
// One arm per daemon command: no decision, only the serde name.
#[allow(clippy::too_many_lines)]
fn wire_name(command: &DaemonCommand) -> &'static str {
    match command {
        DaemonCommand::ListSavedSessions { .. } => "list_saved_sessions",
        DaemonCommand::RenameSavedSession { .. } => "rename_saved_session",
        DaemonCommand::CronList { .. } => "cron_list",
        DaemonCommand::HeartbeatsList { .. } => "heartbeats_list",
        DaemonCommand::Rename { .. } => "rename",
        DaemonCommand::CancelPromptAdmission { .. } => "cancel_prompt_admission",
        DaemonCommand::Abort { .. } => "abort",
        DaemonCommand::PauseWorkers { .. } => "pause_workers",
        DaemonCommand::ResumeWorkers { .. } => "resume_workers",
        DaemonCommand::AbortAndSendQueued { .. } => "abort_and_send_queued",
        DaemonCommand::AbortBash { .. } => "abort_bash",
        DaemonCommand::AnswerShellApproval { .. } => "answer_shell_approval",
        DaemonCommand::GetSessionHeader { .. } => "get_session_header",
        DaemonCommand::GetState { .. } => "get_state",
        DaemonCommand::GetConnectionState { .. } => "get_connection_state",
        DaemonCommand::GetMessages { .. } => "get_messages",
        DaemonCommand::GetRlmChildren { .. } => "get_rlm_children",
        DaemonCommand::GetSessionStats { .. } => "get_session_stats",
        DaemonCommand::GetContextTree { .. } => "get_context_tree",
        DaemonCommand::GetCommands { .. } => "get_commands",
        DaemonCommand::GetResourceSnapshot { .. } => "get_resource_snapshot",
        DaemonCommand::GetMcpConnections { .. } => "get_mcp_connections",
        DaemonCommand::GetModelCatalog { .. } => "get_model_catalog",
        DaemonCommand::GetAvailableModels { .. } => "get_available_models",
        DaemonCommand::GetQueue { .. } => "get_queue",
        DaemonCommand::MutateQueuedMessage { .. } => "mutate_queued_message",
        DaemonCommand::ClearQueue { .. } => "clear_queue",
        DaemonCommand::AbortAndClearQueue { .. } => "abort_and_clear_queue",
        DaemonCommand::SetModel { .. } => "set_model",
        DaemonCommand::CycleModel { .. } => "cycle_model",
        DaemonCommand::SetScopedModels { .. } => "set_scoped_models",
        DaemonCommand::SetThinkingLevel { .. } => "set_thinking_level",
        DaemonCommand::SetServiceTier { .. } => "set_service_tier",
        DaemonCommand::CycleThinkingLevel { .. } => "cycle_thinking_level",
        DaemonCommand::SetSteeringMode { .. } => "set_steering_mode",
        DaemonCommand::SetFollowUpMode { .. } => "set_follow_up_mode",
        DaemonCommand::SetAutoCompaction { .. } => "set_auto_compaction",
        DaemonCommand::SetAutoRetry { .. } => "set_auto_retry",
        DaemonCommand::Cvar { .. } => "cvar",
        DaemonCommand::CvarSave { .. } => "cvar_save",
        DaemonCommand::Compact { .. } => "compact",
        DaemonCommand::AbortCompaction { .. } => "abort_compaction",
        DaemonCommand::AbortBranchSummary { .. } => "abort_branch_summary",
        DaemonCommand::AbortRetry { .. } => "abort_retry",
        DaemonCommand::Fork { .. } => "fork",
        DaemonCommand::NavigateTree { .. } => "navigate_tree",
        DaemonCommand::SetSessionName { .. } => "set_session_name",
        DaemonCommand::GetSessionContext { .. } => "get_session_context",
        DaemonCommand::GetSessionTree { .. } => "get_session_tree",
        DaemonCommand::GetUserMessagesForForking { .. } => "get_user_messages_for_forking",
        DaemonCommand::GetLastAssistantText { .. } => "get_last_assistant_text",
        DaemonCommand::GetSystemPrompt { .. } => "get_system_prompt",
        DaemonCommand::GetChatView { .. } => "get_chat_view",
        DaemonCommand::GetMemory { .. } => "get_memory",
        DaemonCommand::GetMemoryTree { .. } => "get_memory_tree",
        DaemonCommand::GetStateTree { .. } => "get_state_tree",
        DaemonCommand::GetToolDefinition { .. } => "get_tool_definition",
        DaemonCommand::WorkflowActivity { .. } => "workflow_activity",
        DaemonCommand::ExportHtml { .. } => "export_html",
        DaemonCommand::ExportJsonl { .. } => "export_jsonl",
        DaemonCommand::DeleteSavedSession { .. } => "delete_saved_session",
        DaemonCommand::List { .. } => "list",
        DaemonCommand::ListAgentPeers { .. } => "list_agent_peers",
        DaemonCommand::GetDirectWorkerTransport { .. } => "get_direct_worker_transport",
        DaemonCommand::GetWorkerLiveness { .. } => "get_worker_liveness",
        DaemonCommand::GetWorkerPeerTransport { .. } => "get_worker_peer_transport",
        DaemonCommand::RosterSubscribe { .. } => "roster_subscribe",
        DaemonCommand::WorkerIdlePassivation { .. } => "worker_idle_passivation",
        DaemonCommand::WorkerRosterDelta { .. } => "worker_roster_delta",
        DaemonCommand::ProviderAdmissionAcquire { .. } => "provider_admission_acquire",
        DaemonCommand::RosterUnsubscribe { .. } => "roster_unsubscribe",
        DaemonCommand::Create { .. } => "create",
        DaemonCommand::Attach { .. } => "attach",
        DaemonCommand::Reattach { .. } => "reattach",
        DaemonCommand::Detach { .. } => "detach",
        DaemonCommand::CompleteOwnedSession { .. } => "complete_owned_session",
        DaemonCommand::PromoteOwnedSession { .. } => "promote_owned_session",
        DaemonCommand::Kill { .. } => "kill",
        DaemonCommand::Prompt { .. } => "prompt",
        DaemonCommand::PromptAndWait { .. } => "prompt_and_wait",
        DaemonCommand::Steer { .. } => "steer",
        DaemonCommand::FollowUp { .. } => "follow_up",
        DaemonCommand::RestoreNextTurn { .. } => "restore_next_turn",
        DaemonCommand::RestoreActions { .. } => "restore_actions",
        DaemonCommand::AppendCustomMessage { .. } => "append_custom_message",
        DaemonCommand::ResumeQueue { .. } => "resume_queue",
        DaemonCommand::SendMessage { .. } => "send_message",
        DaemonCommand::AgentMessagesStatus { .. } => "agent_messages_status",
        DaemonCommand::AgentMessagesPause { .. } => "agent_messages_pause",
        DaemonCommand::AgentMessagesResume { .. } => "agent_messages_resume",
        DaemonCommand::AgentMessagesClear { .. } => "agent_messages_clear",
        DaemonCommand::StartSideQuestion { .. } => "start_side_question",
        DaemonCommand::AbortSideQuestion { .. } => "abort_side_question",
        DaemonCommand::ExecuteBash { .. } => "execute_bash",
        DaemonCommand::ListKernelBash { .. } => "list_kernel_bash",
        DaemonCommand::TailKernelBash { .. } => "tail_kernel_bash",
        DaemonCommand::KillKernelBash { .. } => "kill_kernel_bash",
        DaemonCommand::FactoryActivity { .. } => "factory_activity",
        DaemonCommand::CancelRlmChild { .. } => "cancel_rlm_child",
        DaemonCommand::DeleteRlmSubagent { .. } => "delete_rlm_subagent",
        DaemonCommand::WaitForIdle { .. } => "wait_for_idle",
        DaemonCommand::WaitForHeadlessCompletion { .. } => "wait_for_headless_completion",
        DaemonCommand::SetMcpStaticToken { .. } => "set_mcp_static_token",
        DaemonCommand::RemoveMcpConnection { .. } => "remove_mcp_connection",
        DaemonCommand::ReplaceAcpMcpServers { .. } => "replace_acp_mcp_servers",
        DaemonCommand::AcquireSessionInputPause { .. } => "acquire_session_input_pause",
        DaemonCommand::ReleaseSessionInputPause { .. } => "release_session_input_pause",
        DaemonCommand::HeartbeatManage { .. } => "heartbeat_manage",
        DaemonCommand::CronAdd { .. } => "cron_add",
        DaemonCommand::CronCancel { .. } => "cron_cancel",
        DaemonCommand::HeartbeatGet { .. } => "heartbeat_get",
        DaemonCommand::HeartbeatSet { .. } => "heartbeat_set",
        DaemonCommand::HeartbeatUpdate { .. } => "heartbeat_update",
        DaemonCommand::SetTransport { .. } => "set_transport",
        DaemonCommand::Refine { .. } => "refine",
        DaemonCommand::ExecuteBashAndWait { .. } => "execute_bash_and_wait",
        DaemonCommand::Reload { .. } => "reload",
        DaemonCommand::NewSession { .. } => "new_session",
        DaemonCommand::SwitchSession { .. } => "switch_session",
        DaemonCommand::ImportJsonl { .. } => "import_jsonl",
        DaemonCommand::GetRlmMaxDepthStatus { .. } => "get_rlm_max_depth_status",
        DaemonCommand::SetRlmMaxDepth { .. } => "set_rlm_max_depth",
        DaemonCommand::GetRunOutcome { .. } => "get_run_outcome",
        DaemonCommand::SubscribeStateTree { .. } => "subscribe_state_tree",
        DaemonCommand::UnsubscribeStateTree { .. } => "unsubscribe_state_tree",
        DaemonCommand::GetStateRewindPlan { .. } => "get_state_rewind_plan",
        DaemonCommand::SetSessionEntryLabel { .. } => "set_session_entry_label",
        DaemonCommand::MarkAnthropicWarningShown { .. } => "mark_anthropic_warning_shown",
        DaemonCommand::AgentRelay { .. } => "agent_relay",
        DaemonCommand::RelayShellApproval { .. } => "relay_shell_approval",
        DaemonCommand::AgentReply { .. } => "agent_reply",
        DaemonCommand::AckResult { .. } => "ack_result",
        DaemonCommand::RetryWorker { .. } => "retry_worker",
        DaemonCommand::Restart { .. } => "restart",
        DaemonCommand::Shutdown { .. } => "shutdown",
        DaemonCommand::WorkerRegister { .. } => "worker_register",
        DaemonCommand::WorkflowCancel { .. } => "workflow_cancel",
    }
}

/// The verdict on `command`.
pub(crate) fn verdict(command: &DaemonCommand) -> Verdict {
    let kind = wire_name(command);
    let answer = || -> Result<Verdict, Error> {
        let reply = call(Entry::DashPolicy, &Writer::new().str(kind).finish()?)?;
        let mut reader = Reader::reply(&reply)?;
        let verdict = match reader.tag_of(3, "a command verdict")? {
            0 => Verdict::Bound,
            1 => Verdict::Catalog,
            2.. => Verdict::Refused,
        };
        reader.end()?;
        Ok(verdict)
    };
    expect_core(Entry::DashPolicy, answer())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_core_decides_each_kind_of_verdict() {
        assert_eq!(
            ["get_state", "cron_list", "list"].map(|kind| {
                let command: DaemonCommand = serde_json::from_value(
                    serde_json::json!({ "type": kind, "activeSessionId": "s" }),
                )
                .expect("a daemon command");
                assert_eq!(wire_name(&command), kind);
                verdict(&command)
            }),
            [Verdict::Bound, Verdict::Catalog, Verdict::Refused]
        );
    }
}
