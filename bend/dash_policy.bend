# dash_policy: which daemon commands a dashboard tab may `run`, and how
# they are sent (Rust: crates/eukhe-dashboard command_policy.rs, called by
# bridge.rs for every `run` frame with the command's `type`).
#
# The bound session's user controls (models, thinking, queue, compaction,
# retry, cvars, approvals, inspection) go to the bound session: the bridge
# sets its id. Catalog commands (saved sessions, schedules) name their
# sessions themselves and go with no session id, so the supervisor answers
# for every session. Every other command is refused: what the bridge owns
# itself (create, attach, detach, prompts, exports, deletes: a raw export
# writes wherever its `outputPath` says, a raw delete cannot stop the
# chat's worker first), every worker-internal or supervisor-wide command,
# and any name eukhe does not list (a new daemon command runs nowhere
# until it is listed here). Names compare exactly, char by char.
# Pure: no IO, no @unsafe.

import Base

# Whether, and how, the dashboard runs one command for a tab
type Verdict is Data:
  # sent for the bound session (the bridge sets `activeSessionId`)
  ForSession{}
  # sent with no session id: the command names its sessions itself
  ForCatalog{}
  # not run
  NotRun{}

# the commands sent with no session id (their `type`)
def catalog() -> List<&2, String>:
  ["list_saved_sessions", "rename_saved_session", "cron_list", "heartbeats_list"]

# the commands sent for the bound session (their `type`)
def session() -> List<&2, String>:
  ["rename", "cancel_prompt_admission", "abort", "abort_and_send_queued", "abort_bash", "answer_shell_approval", "get_session_header", "get_state", "get_connection_state", "get_messages", "get_rlm_children", "get_session_stats", "get_context_tree", "get_commands", "get_resource_snapshot", "get_mcp_connections", "get_model_catalog", "get_available_models", "get_queue", "mutate_queued_message", "clear_queue", "abort_and_clear_queue", "set_model", "cycle_model", "set_scoped_models", "set_thinking_level", "set_service_tier", "cycle_thinking_level", "set_steering_mode", "set_follow_up_mode", "set_auto_compaction", "set_auto_retry", "cvar", "cvar_save", "compact", "abort_compaction", "abort_branch_summary", "abort_retry", "fork", "navigate_tree", "set_session_name", "get_session_context", "get_session_tree", "get_user_messages_for_forking", "get_last_assistant_text", "get_system_prompt", "get_chat_view", "get_memory", "get_memory_tree", "get_state_tree", "get_tool_definition", "workflow_activity"]

# a and b are the same text, char by char
def same(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SNil{} SCon{y, v}:
      False{}
    case SCon{x, u} SNil{}:
      False{}
    case SCon{x, u} SCon{y, v}:
      Bool.and(Char.is_eq(x, y), same(u, v))

# n is one of the names xs
def listed(+n: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(same(x, n), listed(n, t))

def verdict.of(cat: Bool, ses: Bool) -> Verdict:
  match cat:
    case True{}:
      ForCatalog{}
    case False{}:
      match ses:
        case True{}:
          ForSession{}
        case False{}:
          NotRun{}

# the verdict on the command named n
def verdict(+n: String) -> Verdict:
  verdict.of(listed(n, catalog()), listed(n, session()))
