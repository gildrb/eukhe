# eukhe: the laws of area dash_policy

import Base
import ../bend/dash_policy.bend as Dp
import ../bend/ffi_dash_policy.bend as FDp
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (D1) Which daemon commands a dashboard tab may run
# --------------------------------------------------
# bend/dash_policy.bend, run as the compiled core by
# bend/ffi_dash_policy.bend (crates/eukhe-dashboard command_policy.rs,
# bridge.rs: every `run` frame of a tab, named by its `type`). Every input
# is free: any text as the name.
#
# R1: the catalog commands (saved sessions, schedules) go with no session
#     id: list_saved_sessions, rename_saved_session, cron_list,
#     heartbeats_list.
# R2: the bound session's user controls (models, thinking, queue,
#     compaction, retry, cvars, approvals, inspection) go to the bound
#     session: the names of dp_session below.
# R3: nothing else runs. In particular never what the bridge owns itself
#     (create, attach, detach, prompts, exports, deletes), nor a
#     worker-internal or supervisor-wide command (dp_owned below), nor a
#     name eukhe does not list (a new daemon command, a near miss, a name
#     in another case or with a space).
# R4: the entry answers each request Rust writes (the name, within the
#     wire) with the verdict of R1-R3, reads exactly the request and
#     nothing after it, and answers any other input with the exact error
#     form `E dash_policy: malformed request`.

# Spec helpers
# ------------

# R1
def dp_catalog() -> List<&2, String>:
  ["list_saved_sessions", "rename_saved_session", "cron_list", "heartbeats_list"]

# R2
def dp_session() -> List<&2, String>:
  ["rename", "cancel_prompt_admission", "abort", "abort_and_send_queued", "abort_bash", "answer_shell_approval", "get_session_header", "get_state", "get_connection_state", "get_messages", "get_rlm_children", "get_session_stats", "get_context_tree", "get_commands", "get_resource_snapshot", "get_mcp_connections", "get_model_catalog", "get_available_models", "get_queue", "mutate_queued_message", "clear_queue", "abort_and_clear_queue", "set_model", "cycle_model", "set_scoped_models", "set_thinking_level", "set_service_tier", "cycle_thinking_level", "set_steering_mode", "set_follow_up_mode", "set_auto_compaction", "set_auto_retry", "cvar", "cvar_save", "compact", "abort_compaction", "abort_branch_summary", "abort_retry", "fork", "navigate_tree", "set_session_name", "get_session_context", "get_session_tree", "get_user_messages_for_forking", "get_last_assistant_text", "get_system_prompt", "get_chat_view", "get_memory", "get_memory_tree", "get_state_tree", "get_tool_definition", "workflow_activity"]

# R3: the daemon commands the bridge owns itself, and the worker-internal
# and supervisor-wide ones
def dp_owned() -> List<&2, String>:
  ["export_html", "export_jsonl", "delete_saved_session", "list", "list_agent_peers", "get_direct_worker_transport", "get_worker_liveness", "get_worker_peer_transport", "roster_subscribe", "worker_idle_passivation", "worker_roster_delta", "provider_admission_acquire", "roster_unsubscribe", "create", "attach", "reattach", "detach", "complete_owned_session", "promote_owned_session", "kill", "prompt", "prompt_and_wait", "steer", "follow_up", "restore_next_turn", "restore_actions", "append_custom_message", "resume_queue", "send_message", "agent_messages_status", "agent_messages_pause", "agent_messages_resume", "agent_messages_clear", "start_side_question", "abort_side_question", "execute_bash", "list_kernel_bash", "tail_kernel_bash", "kill_kernel_bash", "factory_activity", "cancel_rlm_child", "delete_rlm_subagent", "wait_for_idle", "wait_for_headless_completion", "set_mcp_static_token", "remove_mcp_connection", "replace_acp_mcp_servers", "acquire_session_input_pause", "release_session_input_pause", "heartbeat_manage", "cron_add", "cron_cancel", "heartbeat_get", "heartbeat_set", "heartbeat_update", "set_transport", "refine", "execute_bash_and_wait", "reload", "new_session", "switch_session", "import_jsonl", "get_rlm_max_depth_status", "set_rlm_max_depth", "get_run_outcome", "subscribe_state_tree", "unsubscribe_state_tree", "get_state_rewind_plan", "set_session_entry_label", "mark_anthropic_warning_shown", "agent_relay", "relay_shell_approval", "agent_reply", "ack_result", "retry_worker", "restart", "shutdown", "worker_register", "workflow_cancel"]

# n is one of xs, char by char
def dp_in(+n: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(LawsBase.text_same(x, n), dp_in(n, t))

def dp_verdict.pick(cat: Bool, ses: Bool) -> Dp.Verdict:
  match cat ses:
    case True{} True{}:
      Dp.ForCatalog{}
    case True{} False{}:
      Dp.ForCatalog{}
    case False{} True{}:
      Dp.ForSession{}
    case False{} False{}:
      Dp.NotRun{}

# R1-R3: the verdict on the command named n
def dp_verdict(+n: String) -> Dp.Verdict:
  dp_verdict.pick(dp_in(n, dp_catalog()), dp_in(n, dp_session()))

# R4: the reply Rust reads: 0 bound session, 1 catalog, 2 refused
def dp_tag(v: Dp.Verdict) -> Nat:
  match v:
    case Dp.ForSession{}:
      0n
    case Dp.ForCatalog{}:
      1n
    case Dp.NotRun{}:
      2n

def dp_reply(+n: String) -> String:
  Wr.put_nat(dp_tag(dp_verdict(n)), "")

# Laws: the verdict
# -----------------

# LAW dash_policy_spec (R1-R3): the verdict on every name is the spec's:
# catalog when R1 lists it, the bound session when R2 lists it, else
# refused
# EXCLUDES: a command moved between the tables, added to one, dropped from
#   one; a prefix, case-insensitive or trimmed comparison; a default
#   verdict other than refused
law dash_policy_spec:
  for +n: String
  {Dp.verdict(n) == dp_verdict(n) : Dp.Verdict}

# LAW dash_policy_owned_refused (R3): every command the bridge owns itself,
# and every worker-internal or supervisor-wide command, is refused
# EXCLUDES: a raw create, attach, prompt, export, delete, kill, shutdown
#   or bash command run for a tab (a table that lists one of them)
law dash_policy_owned_refused:
  for +n: String
  for owned: {dp_in(n, dp_owned()) == True{} : Bool}
  {Dp.verdict(n) == Dp.NotRun{} : Dp.Verdict}

# LAW dash_policy_example (R1-R3): anchor: one name of each table and an
# owned one; near misses (a prefix, another case, a trailing space, an
# empty name) are refused
# EXCLUDES: a fuzzy, prefix or case-insensitive comparison
law dash_policy_example:
  {[Dp.verdict("cron_list"), Dp.verdict("get_state"), Dp.verdict("prompt"), Dp.verdict("get_stat"), Dp.verdict("Get_State"), Dp.verdict("get_state "), Dp.verdict(""), Dp.verdict("get_state_tree")] == [Dp.ForCatalog{}, Dp.ForSession{}, Dp.NotRun{}, Dp.NotRun{}, Dp.NotRun{}, Dp.NotRun{}, Dp.NotRun{}, Dp.ForSession{}] : List<&2, Dp.Verdict>}

# Laws: the entry (R4)
# --------------------

# LAW dash_policy_entry_answers (R4): the entry answers every request Rust
# spells (a name within the wire) with the spelled verdict of the spec
# EXCLUDES: a name misread, a reply tag other than Rust's, a default
law dash_policy_entry_answers:
  for +n: String
  for h: {LawsBase.wire_fits(String.length(n)) == True{} : Bool}
  {FDp.ffi(Wr.put_str(n, "")) == dp_reply(n) : String}

# LAW dash_policy_entry_reads (R4): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law dash_policy_entry_reads:
  for +n: String
  for +rest: String
  for h: {LawsBase.wire_fits(String.length(n)) == True{} : Bool}
  {FDp.get_req(Wr.put_str(n, rest)) == Wr.Got{n, rest} : Wr.Dec<String>}

# LAW dash_policy_entry_exact (R4): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: a verdict made on input that is no request (a malformed
#   length, a short text, input left over)
law dash_policy_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FDp.ffi(s)) == False{} : Bool}
  exs n: String
  {s == Wr.put_str(n, "") : String} & {LawsBase.wire_fits(String.length(n)) == True{} : Bool}

# LAW dash_policy_entry_refuses (R4): every error the entry answers is
# exactly `E dash_policy: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law dash_policy_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FDp.ffi(s)) == True{} : Bool}
  {FDp.ffi(s) == Wr.err("dash_policy: malformed request") : String}

# LAW dash_policy_entry_example (R4): anchor: the wire strings Rust sends
# and the replies it reads; a short text and input left over
# EXCLUDES: tags in another order, a length in bytes
law dash_policy_entry_example:
  {[FDp.ffi("9,get_state"), FDp.ffi("9,cron_list"), FDp.ffi("6,create"), FDp.ffi("9,get_stat"), FDp.ffi("9,get_stateX")] == ["0,", "1,", "2,", Wr.err("dash_policy: malformed request"), Wr.err("dash_policy: malformed request")] : List<&2, String>}
