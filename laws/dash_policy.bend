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
#     session: the names marked DpSession in dp_wire below.
# R3: nothing else runs. In particular never what the bridge owns itself
#     (create, attach, detach, prompts, exports, deletes), nor a
#     worker-internal or supervisor-wide command (the names marked DpOwned
#     in dp_wire below), nor a name eukhe does not list (a new daemon
#     command, a near miss, a name in another case or with a space).
# R4: the entry answers each request Rust writes (the name, within the
#     wire) with the verdict of R1-R3, reads exactly the request and
#     nothing after it, and answers any other input with the exact error
#     form `E dash_policy: malformed request`.

# Spec helpers
# ------------

# where R1-R3 place a daemon command
type DpClass is Data:
  DpCatalog{}
  DpSession{}
  DpOwned{}

type DpEntry is Data:
  DpEntry{name: String, cls: DpClass}

# R1-R3: every wire name Rust can send, one per DaemonCommand variant, in
# the order of `wire_name` (crates/eukhe-dashboard/src/command_policy.rs,
# whose match names every variant, so the list is complete), each with the
# requirement that places it: R1 DpCatalog, R2 DpSession, R3 DpOwned
def dp_wire() -> List<&2, DpEntry>:
  [DpEntry{"list_saved_sessions", DpCatalog{}}, DpEntry{"rename_saved_session", DpCatalog{}}, DpEntry{"cron_list", DpCatalog{}}, DpEntry{"heartbeats_list", DpCatalog{}}, DpEntry{"rename", DpSession{}}, DpEntry{"cancel_prompt_admission", DpSession{}}, DpEntry{"abort", DpSession{}}, DpEntry{"pause_workers", DpOwned{}}, DpEntry{"resume_workers", DpOwned{}}, DpEntry{"abort_and_send_queued", DpSession{}}, DpEntry{"abort_bash", DpSession{}}, DpEntry{"answer_shell_approval", DpSession{}}, DpEntry{"get_session_header", DpSession{}}, DpEntry{"get_state", DpSession{}}, DpEntry{"get_connection_state", DpSession{}}, DpEntry{"get_messages", DpSession{}}, DpEntry{"get_rlm_children", DpSession{}}, DpEntry{"get_session_stats", DpSession{}}, DpEntry{"get_context_tree", DpSession{}}, DpEntry{"get_commands", DpSession{}}, DpEntry{"get_resource_snapshot", DpSession{}}, DpEntry{"get_mcp_connections", DpSession{}}, DpEntry{"get_model_catalog", DpSession{}}, DpEntry{"get_available_models", DpSession{}}, DpEntry{"get_queue", DpSession{}}, DpEntry{"mutate_queued_message", DpSession{}}, DpEntry{"clear_queue", DpSession{}}, DpEntry{"abort_and_clear_queue", DpSession{}}, DpEntry{"set_model", DpSession{}}, DpEntry{"cycle_model", DpSession{}}, DpEntry{"set_scoped_models", DpSession{}}, DpEntry{"set_thinking_level", DpSession{}}, DpEntry{"set_service_tier", DpSession{}}, DpEntry{"cycle_thinking_level", DpSession{}}, DpEntry{"set_steering_mode", DpSession{}}, DpEntry{"set_follow_up_mode", DpSession{}}, DpEntry{"set_auto_compaction", DpSession{}}, DpEntry{"set_auto_retry", DpSession{}}, DpEntry{"cvar", DpSession{}}, DpEntry{"cvar_save", DpSession{}}, DpEntry{"compact", DpSession{}}, DpEntry{"abort_compaction", DpSession{}}, DpEntry{"abort_branch_summary", DpSession{}}, DpEntry{"abort_retry", DpSession{}}, DpEntry{"fork", DpSession{}}, DpEntry{"navigate_tree", DpSession{}}, DpEntry{"set_session_name", DpSession{}}, DpEntry{"get_session_context", DpSession{}}, DpEntry{"get_session_tree", DpSession{}}, DpEntry{"get_user_messages_for_forking", DpSession{}}, DpEntry{"get_last_assistant_text", DpSession{}}, DpEntry{"get_system_prompt", DpSession{}}, DpEntry{"get_chat_view", DpSession{}}, DpEntry{"get_memory", DpSession{}}, DpEntry{"get_memory_tree", DpSession{}}, DpEntry{"get_state_tree", DpSession{}}, DpEntry{"get_tool_definition", DpSession{}}, DpEntry{"workflow_activity", DpSession{}}, DpEntry{"export_html", DpOwned{}}, DpEntry{"export_jsonl", DpOwned{}}, DpEntry{"delete_saved_session", DpOwned{}}, DpEntry{"list", DpOwned{}}, DpEntry{"list_agent_peers", DpOwned{}}, DpEntry{"get_direct_worker_transport", DpOwned{}}, DpEntry{"get_worker_liveness", DpOwned{}}, DpEntry{"get_worker_peer_transport", DpOwned{}}, DpEntry{"roster_subscribe", DpOwned{}}, DpEntry{"worker_idle_passivation", DpOwned{}}, DpEntry{"worker_roster_delta", DpOwned{}}, DpEntry{"provider_admission_acquire", DpOwned{}}, DpEntry{"roster_unsubscribe", DpOwned{}}, DpEntry{"create", DpOwned{}}, DpEntry{"attach", DpOwned{}}, DpEntry{"reattach", DpOwned{}}, DpEntry{"detach", DpOwned{}}, DpEntry{"complete_owned_session", DpOwned{}}, DpEntry{"promote_owned_session", DpOwned{}}, DpEntry{"kill", DpOwned{}}, DpEntry{"prompt", DpOwned{}}, DpEntry{"prompt_and_wait", DpOwned{}}, DpEntry{"steer", DpOwned{}}, DpEntry{"follow_up", DpOwned{}}, DpEntry{"restore_next_turn", DpOwned{}}, DpEntry{"restore_actions", DpOwned{}}, DpEntry{"append_custom_message", DpOwned{}}, DpEntry{"resume_queue", DpOwned{}}, DpEntry{"send_message", DpOwned{}}, DpEntry{"agent_messages_status", DpOwned{}}, DpEntry{"agent_messages_pause", DpOwned{}}, DpEntry{"agent_messages_resume", DpOwned{}}, DpEntry{"agent_messages_clear", DpOwned{}}, DpEntry{"start_side_question", DpOwned{}}, DpEntry{"abort_side_question", DpOwned{}}, DpEntry{"execute_bash", DpOwned{}}, DpEntry{"list_kernel_bash", DpOwned{}}, DpEntry{"tail_kernel_bash", DpOwned{}}, DpEntry{"kill_kernel_bash", DpOwned{}}, DpEntry{"factory_activity", DpOwned{}}, DpEntry{"cancel_rlm_child", DpOwned{}}, DpEntry{"delete_rlm_subagent", DpOwned{}}, DpEntry{"wait_for_idle", DpOwned{}}, DpEntry{"wait_for_headless_completion", DpOwned{}}, DpEntry{"set_mcp_static_token", DpOwned{}}, DpEntry{"remove_mcp_connection", DpOwned{}}, DpEntry{"replace_acp_mcp_servers", DpOwned{}}, DpEntry{"acquire_session_input_pause", DpOwned{}}, DpEntry{"release_session_input_pause", DpOwned{}}, DpEntry{"heartbeat_manage", DpOwned{}}, DpEntry{"cron_add", DpOwned{}}, DpEntry{"cron_cancel", DpOwned{}}, DpEntry{"heartbeat_get", DpOwned{}}, DpEntry{"heartbeat_set", DpOwned{}}, DpEntry{"heartbeat_update", DpOwned{}}, DpEntry{"set_transport", DpOwned{}}, DpEntry{"refine", DpOwned{}}, DpEntry{"execute_bash_and_wait", DpOwned{}}, DpEntry{"reload", DpOwned{}}, DpEntry{"new_session", DpOwned{}}, DpEntry{"switch_session", DpOwned{}}, DpEntry{"import_jsonl", DpOwned{}}, DpEntry{"get_rlm_max_depth_status", DpOwned{}}, DpEntry{"set_rlm_max_depth", DpOwned{}}, DpEntry{"get_run_outcome", DpOwned{}}, DpEntry{"subscribe_state_tree", DpOwned{}}, DpEntry{"unsubscribe_state_tree", DpOwned{}}, DpEntry{"get_state_rewind_plan", DpOwned{}}, DpEntry{"set_session_entry_label", DpOwned{}}, DpEntry{"mark_anthropic_warning_shown", DpOwned{}}, DpEntry{"relay_shell_approval", DpOwned{}}, DpEntry{"agent_reply", DpOwned{}}, DpEntry{"ack_result", DpOwned{}}, DpEntry{"retry_worker", DpOwned{}}, DpEntry{"restart", DpOwned{}}, DpEntry{"shutdown", DpOwned{}}, DpEntry{"register_headless_parent", DpOwned{}}, DpEntry{"headless_parent_receipt", DpOwned{}}, DpEntry{"worker_register", DpOwned{}}, DpEntry{"workflow_cancel", DpOwned{}}]

def dp_class.at(b: Bool, k: DpClass, r: Maybe<&2, DpClass>) -> Maybe<&2, DpClass>:
  match b:
    case True{}:
      Some{k}
    case False{}:
      r

# the place of the first entry of es named n, char by char (None: no entry
# is named n)
def dp_class(+n: String, es: List<&2, DpEntry>) -> Maybe<&2, DpClass>:
  match es:
    case Nil{}:
      None{}
    case e <> t:
      match e:
        case DpEntry{x, k}:
          dp_class.at(LawsBase.text_same(x, n), k, dp_class(n, t))

# R1-R3: the verdict each place asks for
def dp_of(k: DpClass) -> Dp.Verdict:
  match k:
    case DpCatalog{}:
      Dp.ForCatalog{}
    case DpSession{}:
      Dp.ForSession{}
    case DpOwned{}:
      Dp.NotRun{}

# the place runs its commands (R1, R2)
def dp_runs(k: DpClass) -> Bool:
  match k:
    case DpCatalog{}:
      True{}
    case DpSession{}:
      True{}
    case DpOwned{}:
      False{}

# R4: the reply Rust reads: 0 bound session, 1 catalog, 2 refused
# (command_policy.rs `verdict`: tag 0 Bound, 1 Catalog, 2.. Refused)
def dp_tag(v: Dp.Verdict) -> Nat:
  match v:
    case Dp.ForSession{}:
      0n
    case Dp.ForCatalog{}:
      1n
    case Dp.NotRun{}:
      2n

# Laws: the verdict
# -----------------

# LAW dash_policy_rust_names (R1-R3): every name Rust can send (dp_wire,
# Rust's wire_name table) gets the verdict its place asks for: catalog
# (R1), the bound session (R2), refused (R3: every command the bridge owns
# itself, every worker-internal or supervisor-wide one)
# EXCLUDES: a command moved between the tables, dropped from one, or added
#   to the allowed ones while R3 refuses it (a raw create, attach, prompt,
#   export, delete, kill, shutdown, pause_workers or bash command run for
#   a tab)
law dash_policy_rust_names:
  for +n: String
  for +k: DpClass
  for named: {dp_class(n, dp_wire()) == Some{k} : Maybe<&2, DpClass>}
  {Dp.verdict(n) == dp_of(k) : Dp.Verdict}

# LAW dash_policy_listed_only (R1-R3): every name that runs, for the
# catalog or the bound session, is a name of dp_wire placed there, char by
# char; so any other text (a new daemon command, a prefix, another ASCII
# case, a trailing space, the empty name) is refused
# EXCLUDES: a prefix, case-insensitive or trimmed comparison; a default
#   verdict other than refused; a name run that Rust cannot send
law dash_policy_listed_only:
  for +n: String
  for +k: DpClass
  for ran: {Dp.verdict(n) == dp_of(k) : Dp.Verdict}
  for runs: {dp_runs(k) == True{} : Bool}
  {dp_class(n, dp_wire()) == Some{k} : Maybe<&2, DpClass>}

# LAW dash_policy_example (R1-R3): anchor: one name of each table and an
# owned one; near misses (a prefix, another case, a trailing space, an
# empty name) are refused
# EXCLUDES: a fuzzy, prefix or case-insensitive comparison
law dash_policy_example:
  {[Dp.verdict("cron_list"), Dp.verdict("get_state"), Dp.verdict("prompt"), Dp.verdict("get_stat"), Dp.verdict("Get_State"), Dp.verdict("get_state "), Dp.verdict(""), Dp.verdict("get_state_tree")] == [Dp.ForCatalog{}, Dp.ForSession{}, Dp.NotRun{}, Dp.NotRun{}, Dp.NotRun{}, Dp.NotRun{}, Dp.NotRun{}, Dp.ForSession{}] : List<&2, Dp.Verdict>}

# Laws: the entry (R4)
# --------------------

# LAW dash_policy_entry_answers (R4): the entry answers every request Rust
# spells (a name within the wire) with the model's verdict (Dp.verdict,
# pinned by dash_policy_rust_names and dash_policy_listed_only) under
# Rust's reply tag
# EXCLUDES: a name misread, a reply tag other than Rust's, a default
law dash_policy_entry_answers:
  for +n: String
  for h: {LawsBase.wire_fits(String.length(n)) == True{} : Bool}
  {FDp.ffi(Wr.put_str(n, "")) == Wr.put_nat(dp_tag(Dp.verdict(n)), "") : String}

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
