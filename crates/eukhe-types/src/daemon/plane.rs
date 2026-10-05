//! Daemon command planes (TS `DAEMON_COMMAND_PLANE`): which socket a
//! command belongs on. Session-plane commands address exactly one live
//! session and may travel over a direct worker peer link; control-plane
//! commands belong to the supervisor (roster, lifecycle, restarts) or
//! mutate supervisor-owned state.
//!
//! The worker enforces this table for direct peer connections (a session
//! client may only send session-plane commands for its own session) and the
//! routed clients in eukhe-tui use it to pick the socket per request, so the
//! table is the shared wire contract and lives here.

/// The plane one command type belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DaemonCommandPlane {
    /// Serves one session; valid on a direct worker peer link.
    Session,
    /// Supervisor-owned; never valid on a direct worker peer link.
    Control,
}

/// TS `DAEMON_COMMAND_PLANE`: every session-plane command the TS product
/// defines has an entry; all other commands, known or unknown, are control
/// (never forwarded on a peer link).
#[must_use]
pub fn command_plane(command_type: &str) -> DaemonCommandPlane {
    use DaemonCommandPlane::{Control, Session};
    match command_type {
        "attach"
        | "detach"
        | "prompt"
        | "cancel_prompt_admission"
        | "prompt_and_wait"
        | "steer"
        | "follow_up"
        | "restore_next_turn"
        | "restore_actions"
        | "append_custom_message"
        | "resume_queue"
        | "abort"
        | "abort_and_send_queued"
        | "start_side_question"
        | "abort_side_question"
        | "execute_bash"
        | "abort_bash"
        | "list_kernel_bash"
        | "tail_kernel_bash"
        | "kill_kernel_bash"
        | "cancel_rlm_child"
        | "delete_rlm_subagent"
        | "wait_for_idle"
        | "wait_for_headless_completion"
        | "get_session_header"
        | "get_state"
        | "get_connection_state"
        | "get_messages"
        | "get_rlm_children"
        | "get_session_stats"
        | "get_context_tree"
        | "get_commands"
        | "get_resource_snapshot"
        | "get_mcp_connections"
        | "replace_acp_mcp_servers"
        | "get_model_catalog"
        | "get_available_models"
        | "get_queue"
        | "mutate_queued_message"
        | "clear_queue"
        | "abort_and_clear_queue"
        | "acquire_session_input_pause"
        | "release_session_input_pause"
        | "set_model"
        | "cycle_model"
        | "set_scoped_models"
        | "set_thinking_level"
        | "set_service_tier"
        | "cycle_thinking_level"
        | "set_transport"
        | "set_steering_mode"
        | "set_follow_up_mode"
        | "set_auto_compaction"
        | "set_auto_retry"
        | "compact"
        | "refine"
        | "abort_compaction"
        | "abort_branch_summary"
        | "abort_retry"
        | "execute_bash_and_wait"
        | "reload"
        | "new_session"
        | "switch_session"
        | "fork"
        | "navigate_tree"
        | "import_jsonl"
        | "export_html"
        | "export_jsonl"
        | "get_rlm_max_depth_status"
        | "set_rlm_max_depth"
        | "get_session_context"
        | "get_session_tree"
        | "get_user_messages_for_forking"
        | "get_last_assistant_text"
        | "get_system_prompt"
        | "get_chat_view"
        | "get_tool_definition"
        | "set_session_entry_label" => Session,
        _ => Control,
    }
}

/// TS `isSessionPlaneDaemonCommand`.
#[must_use]
pub fn is_session_plane_daemon_command(command_type: &str) -> bool {
    command_plane(command_type) == DaemonCommandPlane::Session
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The plane assignments the direct-attach path depends on: the session
    /// commands a peer may send, and the control commands it must not.
    #[test]
    fn planes_match_ts() {
        for session in [
            "attach",
            "detach",
            "prompt",
            "prompt_and_wait",
            "get_state",
            "get_last_assistant_text",
            "start_side_question",
        ] {
            assert!(is_session_plane_daemon_command(session), "{session}");
        }
        for control in [
            "list",
            "get_direct_worker_transport",
            "create",
            "kill",
            "rename",
            "set_session_name",
            "shutdown",
            "restart",
            "retry_worker",
        ] {
            assert!(!is_session_plane_daemon_command(control), "{control}");
        }
        // Unknown commands never ride a peer link.
        assert!(!is_session_plane_daemon_command("not_a_command"));
    }
}
