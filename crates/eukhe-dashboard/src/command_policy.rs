//! Which daemon commands a tab may `run`, and how they are sent. The
//! bound session's user controls (models, thinking, queue, compaction,
//! retry, cvars, approvals, inspection) go to the bound session: the
//! bridge sets its id. Catalog commands (saved sessions, schedules) name
//! their sessions themselves and go with no session id, so the supervisor
//! answers for every session. Everything the bridge owns itself (create,
//! attach, detach, prompts, exports, deletes: a raw export writes wherever
//! its `outputPath` says, a raw delete cannot stop the chat's worker
//! first) and every worker-internal or supervisor-wide command is refused.
//! The match names every variant, so a new daemon command does not compile
//! until it is classified here.

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

/// The verdict on `command`.
// One name per daemon command: the list is the classification.
#[allow(clippy::too_many_lines)]
pub(crate) fn verdict(command: &DaemonCommand) -> Verdict {
    match command {
        DaemonCommand::ListSavedSessions { .. }
        | DaemonCommand::RenameSavedSession { .. }
        | DaemonCommand::CronList { .. }
        | DaemonCommand::HeartbeatsList { .. } => Verdict::Catalog,
        DaemonCommand::Rename { .. }
        | DaemonCommand::CancelPromptAdmission { .. }
        | DaemonCommand::Abort { .. }
        | DaemonCommand::AbortAndSendQueued { .. }
        | DaemonCommand::AbortBash { .. }
        | DaemonCommand::AnswerShellApproval { .. }
        | DaemonCommand::GetSessionHeader { .. }
        | DaemonCommand::GetState { .. }
        | DaemonCommand::GetConnectionState { .. }
        | DaemonCommand::GetMessages { .. }
        | DaemonCommand::GetRlmChildren { .. }
        | DaemonCommand::GetSessionStats { .. }
        | DaemonCommand::GetContextTree { .. }
        | DaemonCommand::GetCommands { .. }
        | DaemonCommand::GetResourceSnapshot { .. }
        | DaemonCommand::GetMcpConnections { .. }
        | DaemonCommand::GetModelCatalog { .. }
        | DaemonCommand::GetAvailableModels { .. }
        | DaemonCommand::GetQueue { .. }
        | DaemonCommand::MutateQueuedMessage { .. }
        | DaemonCommand::ClearQueue { .. }
        | DaemonCommand::AbortAndClearQueue { .. }
        | DaemonCommand::SetModel { .. }
        | DaemonCommand::CycleModel { .. }
        | DaemonCommand::SetScopedModels { .. }
        | DaemonCommand::SetThinkingLevel { .. }
        | DaemonCommand::SetServiceTier { .. }
        | DaemonCommand::CycleThinkingLevel { .. }
        | DaemonCommand::SetSteeringMode { .. }
        | DaemonCommand::SetFollowUpMode { .. }
        | DaemonCommand::SetAutoCompaction { .. }
        | DaemonCommand::SetAutoRetry { .. }
        | DaemonCommand::Cvar { .. }
        | DaemonCommand::CvarSave { .. }
        | DaemonCommand::Compact { .. }
        | DaemonCommand::AbortCompaction { .. }
        | DaemonCommand::AbortBranchSummary { .. }
        | DaemonCommand::AbortRetry { .. }
        | DaemonCommand::Fork { .. }
        | DaemonCommand::NavigateTree { .. }
        | DaemonCommand::SetSessionName { .. }
        | DaemonCommand::GetSessionContext { .. }
        | DaemonCommand::GetSessionTree { .. }
        | DaemonCommand::GetUserMessagesForForking { .. }
        | DaemonCommand::GetLastAssistantText { .. }
        | DaemonCommand::GetSystemPrompt { .. }
        | DaemonCommand::GetChatView { .. }
        | DaemonCommand::GetMemory { .. }
        | DaemonCommand::GetMemoryTree { .. }
        | DaemonCommand::GetStateTree { .. }
        | DaemonCommand::GetToolDefinition { .. } => Verdict::Bound,
        DaemonCommand::ExportHtml { .. }
        | DaemonCommand::ExportJsonl { .. }
        | DaemonCommand::DeleteSavedSession { .. }
        | DaemonCommand::List { .. }
        | DaemonCommand::ListAgentPeers { .. }
        | DaemonCommand::GetDirectWorkerTransport { .. }
        | DaemonCommand::GetWorkerLiveness { .. }
        | DaemonCommand::GetWorkerPeerTransport { .. }
        | DaemonCommand::RosterSubscribe { .. }
        | DaemonCommand::WorkerIdlePassivation { .. }
        | DaemonCommand::WorkerRosterDelta { .. }
        | DaemonCommand::ProviderAdmissionAcquire { .. }
        | DaemonCommand::RosterUnsubscribe { .. }
        | DaemonCommand::Create { .. }
        | DaemonCommand::Attach { .. }
        | DaemonCommand::Reattach { .. }
        | DaemonCommand::Detach { .. }
        | DaemonCommand::CompleteOwnedSession { .. }
        | DaemonCommand::PromoteOwnedSession { .. }
        | DaemonCommand::Kill { .. }
        | DaemonCommand::Prompt { .. }
        | DaemonCommand::PromptAndWait { .. }
        | DaemonCommand::Steer { .. }
        | DaemonCommand::FollowUp { .. }
        | DaemonCommand::RestoreNextTurn { .. }
        | DaemonCommand::RestoreActions { .. }
        | DaemonCommand::AppendCustomMessage { .. }
        | DaemonCommand::ResumeQueue { .. }
        | DaemonCommand::SendMessage { .. }
        | DaemonCommand::AgentMessagesStatus { .. }
        | DaemonCommand::AgentMessagesPause { .. }
        | DaemonCommand::AgentMessagesResume { .. }
        | DaemonCommand::AgentMessagesClear { .. }
        | DaemonCommand::StartSideQuestion { .. }
        | DaemonCommand::AbortSideQuestion { .. }
        | DaemonCommand::ExecuteBash { .. }
        | DaemonCommand::ListKernelBash { .. }
        | DaemonCommand::TailKernelBash { .. }
        | DaemonCommand::KillKernelBash { .. }
        | DaemonCommand::FactoryActivity { .. }
        | DaemonCommand::CancelRlmChild { .. }
        | DaemonCommand::DeleteRlmSubagent { .. }
        | DaemonCommand::WaitForIdle { .. }
        | DaemonCommand::WaitForHeadlessCompletion { .. }
        | DaemonCommand::SetMcpStaticToken { .. }
        | DaemonCommand::RemoveMcpConnection { .. }
        | DaemonCommand::ReplaceAcpMcpServers { .. }
        | DaemonCommand::AcquireSessionInputPause { .. }
        | DaemonCommand::ReleaseSessionInputPause { .. }
        | DaemonCommand::HeartbeatManage { .. }
        | DaemonCommand::CronAdd { .. }
        | DaemonCommand::CronCancel { .. }
        | DaemonCommand::HeartbeatGet { .. }
        | DaemonCommand::HeartbeatSet { .. }
        | DaemonCommand::HeartbeatUpdate { .. }
        | DaemonCommand::SetTransport { .. }
        | DaemonCommand::Refine { .. }
        | DaemonCommand::ExecuteBashAndWait { .. }
        | DaemonCommand::Reload { .. }
        | DaemonCommand::NewSession { .. }
        | DaemonCommand::SwitchSession { .. }
        | DaemonCommand::ImportJsonl { .. }
        | DaemonCommand::GetRlmMaxDepthStatus { .. }
        | DaemonCommand::SetRlmMaxDepth { .. }
        | DaemonCommand::GetRunOutcome { .. }
        | DaemonCommand::SubscribeStateTree { .. }
        | DaemonCommand::UnsubscribeStateTree { .. }
        | DaemonCommand::GetStateRewindPlan { .. }
        | DaemonCommand::SetSessionEntryLabel { .. }
        | DaemonCommand::MarkAnthropicWarningShown { .. }
        | DaemonCommand::AgentRelay { .. }
        | DaemonCommand::RelayShellApproval { .. }
        | DaemonCommand::AgentReply { .. }
        | DaemonCommand::AckResult { .. }
        | DaemonCommand::RetryWorker { .. }
        | DaemonCommand::Restart { .. }
        | DaemonCommand::Shutdown { .. }
        | DaemonCommand::WorkerRegister { .. } => Verdict::Refused,
    }
}
