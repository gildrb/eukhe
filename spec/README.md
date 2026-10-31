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
|durable|[pi-durable](https://github.com/earendil-works/pi/tree/main/packages/durable) (`crates/eukhe-durable`)|`durable/log.bend`, `durable/task_life.bend`, `durable/task_life_wire.bend`|log (25), staging (26), listing (12), tree (30), task_life (16), job (37), job_step (15), tool_call (11), wait (19)|
|rlm|[prime-agent](https://github.com/PrimeIntellect-ai/prime-agent) RLM: REPL kernel, `rlm.spawn` child sessions|`rlm/family.bend`|family (15), child (16), child_env (19), workflow (37), progress (19), work (16)|
|memory|[OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449)|`memory/optchat.bend`|optchat (31), compactor (29), admission (36)|
|agents|[Fold subagents into the main loop](https://claude.com/resources/articles/building-agents-when-to-fold-subagents-into-your-main-agent-loop)|`rlm/family.bend` (spawn reasons)|run (60), family (15), tools (35), tool_surface (4), skill_load (11), runners (11), approvals (33), director (33)|
|autoresearch|[oh-my-pi autoresearch](https://github.com/can1357/oh-my-pi/tree/main/packages/coding-agent/src/autoresearch)|`autoresearch/{decimal,metric_line,segment,stats}.bend`|autoresearch (47)|
|settings|eukhe|`settings/config.bend`, `settings/config_rules.bend`|config (48), cvar (35)|
|theme|eukhe|`theme/{color,model,read,rules,wire}.bend`|theme (51), theme_model (16), color (39)|

## Requirements

|Id|Requirement|Laws|
|---|---|---|
|D1|An acknowledged commit survives any crash; open reads exactly the complete lines; the log holds a prefix of the commits, in order.|`log_ack_durable`, `log_reads_lines`, `log_only_commits`|
|D2|A publish never overwrites a live storage; a sweep never removes a live or young staging directory.|`publish_never_overwrites`, `sweep_never_live`, `sweep_never_young`|
|D3|A terminal task never changes; a task's outcome is set once; resume keeps every checkpoint and leaves no task running; joins follow failFast or allSettled; an abort marks exactly the owned live tasks; a submission never moves back.|`task_life_terminal_absorbs`, `task_life_outcome_once`, `task_life_resume_keeps_checkpoint`, `task_life_join_fail_fast`, `task_life_join_all_settled`, `task_life_abort_reaches_owned`, `task_life_submission_forward`, `task_life_step_refines_spec`|
|D4|Every run ends; every wait has an exit.|`run_ends`, wait laws|
|R1|A subagent is admitted only with a reason (`parallel`, `isolate`, `tools`, `user`), below the depth limit, inside the family cap; a batch admits all or none.|`family_admit_iff`, `family_why_required`, `family_admit_depth_bound`, `family_cap_bound`, `family_batch_all_or_none`, `family_refusal_precedence`|
|R2|Every subagent reports exactly once; no credential reaches a child.|child laws, `env_drops_credentials`|
|M1|The view and the compaction view tile the messages; merges follow Taelin's rollback push (due = (T − last) / 2^l); a fit reaches its budget; a turn never waits forever on memory.|`view_covers`, `cview_covers`, `push_agrees_always`, `fit_reaches_budget`, `need_progress`|
|M2|A compactor line fits its budget; interactive requests never wait behind background work.|compactor laws, admission laws|
|A1|One loop: the roster is fixed at open and stays small; late tools come through `dyn`; skills show only name and description and load on demand; a failed skill load is reported.|`roster_fixed`, `dyn_reaches_joined`, skill_load laws|
|A2|Every runner goes through the approval gate.|`gate_covers_every_runner`|
|X1|Only an improvement is kept, and every improvement is: a keep is accepted exactly when the run passed, its parsed metric is strictly better than the best unflagged keep of the current segment, and it stayed in scope or is justified; the baseline is the first such keep; the best never gets worse.|`keep_is_better`, `keep_accepted`, `keep_needs_pass`, `keep_needs_justification`, `best_is_best`, `best_never_worse`, `baseline_is_first`|
|X2|At most one pending run; every started run is logged or abandoned; a refused log changes nothing; the iteration cap stops the loop; the logged metric is the parsed one.|`run_conservation`, `log_needs_pending`, `log_accepted`, `log_records`, `effect_matches_status`, `metric_line_sound`, `metric_last_wins`, `autoresearch_step_is_model`|

## Trust

Proven: the Bend source of every rule above. Trusted: the Bend compiler, the C
shim (`crates/eukhe-bend/src/ffi.rs`), the Rust codecs and IO. Tested, not
proven: the host paths (`cargo test`, bridge tests with `EUKHE_REQUIRE_BEND=1`).
