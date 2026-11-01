# spec

The written spec of eukhe: one folder per pillar. A spec file restates a rule
without calling the code. Laws (`laws/<area>.bend`) state that the shipped
Bend model refines it; `PROOF.bend` proves every law; `LAWS.lock` freezes them.

```
bend PROOF.bend             # every law checks
bend PROOF.bend --verdict   # the same, Lean-proven BendTT kernel
python3 scripts/check_laws_wired.py .
```

Rust keeps IO only. Each rule runs as the proven model: a compiled-core entry
(`bend/ffi_<area>.bend`, id in `bend/core_entries.txt`). Bend 2 only.

## Pillars

|Pillar|Source|Spec|Law areas (laws)|
|---|---|---|---|
|durable|[pi-durable](https://github.com/earendil-works/pi/tree/main/packages/durable) (`crates/eukhe-durable`)|`durable/log.bend`, `durable/task_life.bend`, `durable/task_life_wire.bend`, `durable/headless.bend`, `durable/headless_wire.bend`|log (25), staging (26), listing (12), tree (30), task_life (16), job (37), job_step (15), wait (19), headless_settle (16), headless_exit (29)|
|rlm|[prime-agent](https://www.primeintellect.ai/blog/prime-agent) RLM: context as a variable in the REPL, subagents as function calls|`rlm/family.bend`, `rlm/query.bend`|family (15), rlm_query (19), child (16), child_env (19), workflow (37), progress (19), work (16)|
|harness|[omp²](https://github.com/can1357/oh-my-pi/blob/omp2/PHILOSOPHY.md): speculation then effect, decode what they meant, version everything, documents checked out, data over code, Directors at a candidate stop|`harness/{effect,arguments,lift,lift_wire,rebase,stop}.bend`|tool_call (21), arg_repair (21), call_lift (13), rebase (12), facts (48), model_facts (8), quirks (17), stop (26)|
|memory|[OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449)|`memory/optchat.bend`, `memory/thread.bend`|optchat (31), compactor (29), admission (36), thread (13)|
|agents|[Fold subagents into the main loop](https://claude.com/resources/articles/building-agents-when-to-fold-subagents-into-your-main-agent-loop)|`rlm/family.bend` (spawn reasons), `agents/kin.bend` (who messages whom)|run (60), family (15), kin (13), tools (35), tool_surface (4), skill_load (11), runners (11), approvals (33), director (33)|
|autoresearch|[oh-my-pi autoresearch](https://github.com/can1357/oh-my-pi/tree/main/packages/coding-agent/src/autoresearch)|`autoresearch/{decimal,metric_line,segment,stats,step}.bend`|autoresearch (54)|
|settings|eukhe|`settings/config.bend`, `settings/config_rules.bend`|config (48), cvar (35)|
|theme|eukhe|`theme/{color,model,read,rules,wire}.bend`|theme (51), theme_model (16), color (39)|

## Requirements

|Id|Requirement|Laws|
|---|---|---|
|D1|An acknowledged commit survives any crash; open reads exactly the complete lines; the log holds a prefix of the commits, in order.|`log_ack_durable`, `log_reads_lines`, `log_only_commits`|
|D2|A publish never overwrites a live storage; a sweep never removes a live or young staging directory.|`publish_never_overwrites`, `sweep_never_live`, `sweep_never_young`|
|D3|A terminal task never changes; a task's outcome is set once; resume keeps every checkpoint and leaves no task running; joins follow failFast or allSettled; an abort marks exactly the owned live tasks; a submission never moves back.|`task_life_terminal_absorbs`, `task_life_outcome_once`, `task_life_resume_keeps_checkpoint`, `task_life_join_fail_fast`, `task_life_join_all_settled`, `task_life_abort_reaches_owned`, `task_life_submission_forward`, `task_life_step_refines_spec`|
|D4|Every run ends; every wait has an exit: a headless run (`-p`, `--mode json`, `--mode rpc`) stops waiting only when nothing runs, nothing is pending and nothing is unknown, gives up only at its wait limit, and never waits past it.|`run_ends`, wait laws, `headless_settle_refines_spec`, `headless_settle_done_iff_quiet`, `headless_settle_*_never_done`, `headless_settle_give_up_needs_limit`, `headless_settle_limit_exits`|
|D5|Honest exit codes: a headless run exits 0 only when it answered; a failed command, a give-up, a failed run, a failed terminal entry, a failed compaction or autonomous turn each exit 1, the first of them its cause; a reset, stale or withdrawn run is no failure by itself.|`headless_exit_refines_spec`, `headless_exit_zero_iff_answered`, `headless_exit_code_at_most_one`, `headless_exit_*_fails`, `headless_exit_command_failed_first`, `headless_exit_gave_up_before_run`, `headless_exit_run_before_transcript`, `headless_exit_transcript_before_flags`, `headless_exit_compaction_before_autonomous`, `headless_exit_unfailed_run_neutral`|
|R1|A subagent is admitted only with a reason (`parallel`, `isolate`, `tools`, `user`), below the depth limit, inside the family cap; a batch admits all or none.|`family_admit_iff`, `family_why_required`, `family_admit_depth_bound`, `family_cap_bound`, `family_batch_all_or_none`, `family_refusal_precedence`|
|R2|Every subagent reports exactly once; no credential reaches a child.|child laws, `env_drops_credentials`|
|R3|`rlm.query`/`query_batch` (tool-less sub-model calls whose results return as values): budget first, then the concurrency cap, then waves that cover every call once, in order; a result cut stays UTF-8 safe and within `max_bytes`.|`rlm_query_plan_spec`, `rlm_query_budget_refuses`, `rlm_query_full_refuses`, `rlm_query_admits`, `rlm_query_cap_bound`, `rlm_query_covers`, `rlm_query_cut_spec`|
|H1|Speculation, then effect: a tool runs only for a call of a committed assistant entry; a history with no commit changes nothing; an unsafe call never runs twice across a restart; each call settles once.|`tool_call_gate_is_spec`, `execute_after_committed`, `uncommitted_drop_inert`, `effect_once`, `effect_settles_once`|
|H2|Decode what they meant: every argument repair (decoded key, alias, scalar spelling) is recorded once; declared keys are never renamed; refused or unknown keys reject the call; a repair is idempotent.|`arg_repair_spec`, `arg_repair_recorded`, `arg_repair_never_renames`, `arg_repair_refused_rejects`, `arg_repair_unknown_rejects`, `arg_repair_idempotent`|
|H3|Version everything: a replayed call of an older `family@rev` is lifted to the current rev; current and foreign calls stay untouched; no argument is lost; a transcript's bytes never change when a turn is appended.|`call_lift_refines_spec`, `call_lift_reaches_current`, `call_lift_current_is_identity`, `call_lift_unknown_family_untouched`, `call_lift_preserves_unmapped`, `call_lift_replay_byte_stable`|
|H4|Documents checked out: a stale edit lands only where its window is unique in base and head; otherwise it is refused whole with the reason, never guessed or written in part.|`rebase_refines`, `rebase_disjoint_lands`, `rebase_conflict_no_write`, `rebase_ambiguous_refused`, `rebase_result_applies`|
|H5|Data over code: wire shape never branches on a model id or provider name in Rust; the rulebook's families and hosts decide it.|`facts_reasoning_exact`, `facts_bedrock_reasoning_oracle`, `facts_flag_exact`|
|H6|Directors at a candidate stop (a reply with no tool call): a reply cut at the output limit, with no text, or with markup the harness could not read never ends the run as its answer; any other reply stands, whatever it says (also one that names a next step), as does one that stops while the session owns running work; each Director's reminders in a row are capped, and every run still ends.|`stop_walk_refines`, `stop_verdict_exact`, `stop_cut_continues`, `stop_empty_continues`, `stop_markup_continues`, `stop_pending_pauses`, `stop_reply_stands`, `stop_pending_never_continues`, `stop_empty_gives_up`, `rec_leak_gives_up`, `rec_notes_capped`, `run_ends`|
|M1|The view and the compaction view tile the messages; merges follow Taelin's rollback push (due = (T − last) / 2^l); a fit reaches its budget; a turn never waits forever on memory.|`view_covers`, `cview_covers`, `push_agrees_always`, `fit_reaches_budget`, `need_progress`|
|M2|A compactor line fits its budget; interactive requests never wait behind background work.|compactor laws, admission laws|
|M3|Each session is its own thread: a session's request holds only its own thread's messages; the newest turns are present verbatim until compaction; the view keeps only the history that scrolled out of the transcript.|`thread_log_chat`, `thread_request_own`, `thread_newest_verbatim`, `thread_history_before`, `thread_history_kept`, `thread_history_lines_spec`, `thread_history_lines_is_model`|
|A1|One loop: the roster is fixed at open and stays small; late tools come through `dyn`; skills show only name and description and load on demand; a failed skill load is reported.|`roster_fixed`, `dyn_reaches_joined`, skill_load laws|
|A2|Every runner goes through the approval gate.|`gate_covers_every_runner`|
|A3|An agent messages only its parent and its own children, never itself or across trees; an admitted message always reaches the target's inbox: queued while it is busy, delivered when idle, and a parked target is woken, never dropped.|`kin_refines_spec`, `kin_admit_iff`, `kin_no_cross_tree`, `kin_no_self`, `kin_relation_exact`, `kin_wake`|
|X1|Only an improvement is kept, and every improvement is: a keep is accepted exactly when the run passed, its parsed metric is strictly better than the best unflagged keep of the current segment, and it stayed in scope or is justified; the baseline is the first such keep; the best never gets worse.|`keep_is_better`, `keep_accepted`, `keep_needs_pass`, `keep_needs_justification`, `best_is_best`, `best_never_worse`, `baseline_is_first`|
|X2|At most one pending run; every started run is logged or abandoned; a refused log changes nothing; the iteration cap stops the loop; the logged metric is the parsed one.|`run_conservation`, `log_needs_pending`, `log_accepted`, `log_records`, `effect_matches_status`, `metric_line_sound`, `metric_last_wins`, `autoresearch_step_is_model`|

## Trust

Proven: the Bend source of every rule above. Trusted: the Bend compiler, the C
shim (`crates/eukhe-bend/src/ffi.rs`), the Rust codecs and IO. Tested, not
proven: the host paths (`cargo test`), and run-time `Nat` sizes (Bend aborts
past 2^48-1; laws see unbounded numbers): `fifteen_digit_metrics_run_in_the_core`.
