# Harness laws: settings and directors

Shared rules (what a law secures, the adversary, H1 to H6): [harness.md](harness.md).

### S4. Settings as console variables

Each setting is a console variable (cvar), declared once in one table: id, type, scope, two flags, default. Id = dotted key path in `settings.json` (`retry.enabled`).

1. Registry holds each id once. Duplicate id, or default not of the cvar's type: eukhe stops at startup (`RegistryError`).
2. Scope Global or Local. Global: one value for every agent, set only by the global config. Local: may differ per agent.
3. `persist`: an agent may write its sets of the cvar to its cfg. `replicate`: clients see the value.

Value layers, higher wins:

```text
default < config < each agent of the family, root first:
                   its profile < its own sets
```

- Config: `settings.json` (global, then project), then `config.cfg` (global `<agent dir>/config.cfg`, then project `.eukhe/config.cfg`). Project files obey `settings.json` project trust rules; never set a Global cvar.
- Subagent profile: `subagent.cfg`, then `agents/<name>.cfg` for a named agent. Root session = agent `main`.
- Agent sets: runtime sets (`/set`, `/toggle`, session switches). Session state: conversation document `eukhe.cvar.agent`, committed per change; shown in the state tree; restored by rewind or fork.

- Per layer, the last valid set wins. Valid: cvar declared, value of its type; in a profile or agent sets also Local. Invalid: typed `CvarError` (`Undeclared`, `BadValue`, `Global`, `NotBool`).
- Subagent starts from its parent's family (spawn carries parent layers); own profile and sets on top.
- Session switches (transport, steering mode, follow-up mode, auto retry, auto compaction, service tier): sets of the session's own agent; never change another session.
- Session cannot set a Global cvar; `/set --global` writes it to global `config.cfg`.
- `toggle` in `/set --global` flips only the global layer (global `settings.json`, then global `config.cfg`); a project file never changes what it flips.
- Cfg read-change-write holds the file lock: concurrent sessions lose no set.
- Existing unreadable cfg file: settings error, never written. Profile file errors and unparsable agent-state aliases: settings errors.
- `eukhe.settings` service shows a session's settings errors as an `eukhe.settings_error` row of its main conversation (display-only, not in model context): at open, and each new error after reload; each distinct error once per opened session.

One command language for cfg files, the `/set` family and key binds. Line = commands separated by `;`; double quotes keep spaces.

| Command | Does |
| --- | --- |
| `set <id> <value>` | Sets the cvar. |
| `toggle <id>` | Bool cvar to the opposite of its value in the agent (inherited values included). |
| `alias <name> "<cmds>"` | Names a command list. |
| `bind <key> "<cmds>"` | Commands a key press runs. |
| `action <id>` | Runs a built-in client action (in a bind). |
| `<name>` | Runs alias `<name>`. |

4. Expansion replaces each alias run with its commands; nests at most one level per table alias, plus one. Deeper = repeated alias = cycle (`ExpandError::Cycle`). Missing alias: `ExpandError::Unknown`. Failed expansion runs nothing.
5. Key binds: `<agent dir>/binds.cfg`.
   - First bind of a key wins; user binds before defaults.
   - Unbound key runs nothing; empty bind (`bind <key> ""`) disables a default.
   - Default actions sharing a key share one bind; the screen receiving the key runs its own action.
   - Press sends `set`, `toggle`, `alias` to the session; runs `action` in the client.
   - No `binds.cfg`: written once from `keybindings.json`, same actions per key.
   - Unreadable `binds.cfg` or unwritable import: warning at startup and `/reload`.
6. `/cvar save` writes the agent's `persist` sets to `agents/<name>.cfg`; read back as profile, same values.

Model: `bend/cvar.bend` (`registry`, `value`, `written`, `toggle`, `expand`, `press`). Laws: `LAWS.bend` section (S4). Proofs: `PROOF.bend` section `cvar`. Free inputs: any declarations (duplicate ids, wrong defaults), config, agent family with any profiles and sets (wrong types, Global cvars, undeclared ids), alias table, binds.

| Law | Says |
| --- | --- |
| `cvar_registry_unique` | Each id once in registry (S4.1). |
| `cvar_registry_typed` | Each default has its type (S4.1). |
| `cvar_value_typed` | Each value has its cvar's type in each agent; undeclared cvar has no value. |
| `cvar_inherits` | Subagent without profile or sets has parent's values. |
| `cvar_set_wins` | Subagent's last valid set beats parent's value. |
| `cvar_global_uniform` | Global cvar: one value in every agent, config over default (S4.2). |
| `cvar_written_flagged` | Agent writes to cfg only `persist` cvars, replicates only `replicate` cvars (S4.3). |
| `cvar_persist_roundtrip` | Written cfg read back as profile gives each persisting cvar's value (S4.6). |
| `cvar_toggle_twice` | Two toggles restore the value. |
| `alias_expands_fully` | Expansion leaves no alias, or reports cycle or unknown alias (S4.4). |
| `alias_self_cycle` | Self-running alias is a cycle; the cycle names the alias (S4.4). |
| `alias_unknown_reported` | Run of a missing alias is reported with its name (S4.4). |
| `alias_runs_body` | Alias of plain commands runs exactly them (S4.4). |
| `alias_expands_in_order` | A list expands command by command, in order: two lists expand to the first's commands then the second's; the first error, left to right, is the outcome (S4.4). |
| `alias_expand_example` | Anchor: the Rust test's table (chain of two aliases, cycle of two, run of a missing alias) (S4.4). |
| `bind_press_plain` | Key press runs only plain commands (S4.5). |
| `bind_unbound_runs_nothing` | Unbound key runs nothing (S4.5). |
| `bind_first_wins` | Key press runs the key's first bind (S4.5). |

Code:

- `eukhe-types/src/cvar.rs` (command language): `parse_list`, `parse_script`, `Aliases`, `Binds`, `ExpandError`.
- `eukhe-bend/src/rules/cvar.rs`: `expand`, `Presses`: expansion and key presses run as the compiled model (entry `bend/ffi_cvar.bend`, laws `LAWS.bend` section `cvar_entry`); a press table lives in the core, so a press sends only its key.
- `eukhe-core/src/settings/cvar.rs`: `Registry`, `Cvars::value`, `Cvars::execute`, `Sets::written`, `document_sets`; `settings/cvar/table.rs` (declarations).
- `settings/cfg.rs`: config layer (`settings.json`, then `config.cfg` files under trust rules).
- `settings/manager.rs`, `settings/getters.rs`: getters, all through `Cvars`.
- `eukhe-core/src/durable/cvar_agent.rs` (session agent): `CvarAgent`, `eukhe.cvar.agent` document, `run_cvar_line`, `save_agent_cfg`.
- `durable/settings.rs`: `EukheSettings` (session family over its config).
- `eukhe-daemon/src/setting_switches.rs`: daemon commands `cvar { line, global }`, `cvar_save`; refusal answers its `CvarError` as `data: { kind, id?, message }`.
- Spawn carries parent family in create config (`cvarFamily`).
- `eukhe-tui/src/session_ui/cvar.rs`: TUI sends `/set`, `/toggle`, `/alias`, `/cvar` as `cvar` lines.

Tie: `settings::cvar::bridge::the_rust_cvars_equal_the_bend_model` vs `bend/bridge_cvar.bend`, byte for byte, 300 generated scenarios reaching every rule: registries (duplicate ids, wrong defaults); values over config and family (wrong types, Global cvars, undeclared ids, profiles, sets); toggles of a family's last agent (subagent toggles an inherited value); written sets (`persist`, `replicate`). Expansion and presses: no bridge, they run as the model; `rules::cvar::tests` checks the glue (names and commands to the model's numbers and back).

Regression tests:

- `a_switch_changes_only_its_own_session` (daemon: two workers on one agent dir; one's switches change neither the other nor `settings.json`)
- `a_setter_never_clobbers_a_global_settings_file_that_failed_to_parse` (setter refuses to overwrite an unparsed `settings.json`)
- `cvar_rejects_a_global_cvar_from_a_session`, `a_subagent_inherits_its_parents_family_under_its_profile`, `a_fork_starts_from_the_agent_state_at_its_fork_point`, `an_unreadable_cfg_file_is_reported_and_never_overwritten`, `concurrent_global_sets_both_land`, `a_global_toggle_flips_the_global_value_not_the_projects`, `profile_and_agent_alias_errors_reach_the_manager`, `settings_errors_show_as_a_row_of_the_session`, `unreadable_binds_cfg_and_failed_import_are_warnings`
- `keybindings::tests` (`binds.cfg` import, presses)

### S4b. Config documents

Documents: `settings.json` (global, project), `mcp-connections.json`, `auth.json`. No input lost silently.

1. Writer reads under lock, applies its change, writes. Read fails (unreadable, invalid JSON, not an object, unknown version): writes nothing, returns the error. Only a missing file reads as empty. Untouched keys keep values. Applies to `eukhe mcp add`, `eukhe mcp remove`, every settings setter, connection records, `AuthStorage` `set` and `remove` (both return the error to the caller).
2. Settings setter writes the on-disk document, not its loaded copy: keys that failed to load and keys another writer added stay. Refuses a value its setting cannot hold. If a higher layer sets the same setting (global `config.cfg`, project `settings.json`, project `config.cfg`), it names that file (`Persisted::Shadowed`); client shows it. Daemon shows an unsavable default model or thinking level as a settings error row.
3. Each `settings.json` leaf applies or is named by a settings error. Leaf: a non-object value, or a cvar's whole value. Value its setting cannot hold: `BadValue`; undeclared key: `Undeclared` (same `CvarError`s and row as `config.cfg`). A bad leaf drops only itself. Known top-level keys come from the `Settings` type.
4. Malformed limit fails closed: non-whole `providerMaxInFlight` entry limits its provider to 1; non-map value limits each provider to 1. `idleEvictionMinutes` and session archive rules: whole number, `off` or `none` (`NatOrOff`); else settings error.
5. Untrusted project changes no limit, system prompt or credential: `maxToolRounds`, `subagentMaxConcurrency`, `subagentStallMs`, `toolBlockingBudgetMs`, `autonomous`, `directors`, `thinkingBudgets`, `retry.maxRetries`, `retry.failover.maxRetries` withheld with the code-running keys, plus project `SYSTEM.md` and `APPEND_SYSTEM.md`; trust warning names them. `trustedProjects`: global layer only (global `settings.json`, then global `config.cfg`).
6. `mcpServers` entry is a unit: a project entry replaces the same-named global entry, never takes its URL or credential. `kernelTransport` is a unit too.
7. Sessions directory, one precedence for every reader (CLI, dashboard, gateway, daemon; `settings::resolve_session_dir`): `--session-dir`, `EUKHE_SESSION_DIR` (or legacy `EUKHE_CODING_AGENT_SESSION_DIR`), `sessionDir` setting, `<agent dir>/sessions`.

Model: `bend/config.bend`. Laws: `LAWS.bend` section `config`. Proofs: `PROOF.bend` section `config`.

| Law | Says |
| --- | --- |
| `rmw_refuses_broken` | Unreadable or unparsable document never written (S4b.1). |
| `rmw_keeps_others` | Write keeps every untouched key (S4b.1). |
| `rmw_applies_change` | Changed key has the set value. |
| `settings_save_preserves` | Setter writes the on-disk document with its key changed, whatever copy it loaded (S4b.2). |
| `leaf_applied_or_reported` | Each leaf applies or is named by a diagnostic (S4b.3). |
| `leaf_not_both` | No leaf both applies and is named. |
| `limit_malformed_fails_closed` | Malformed in-flight limit = 1, never "no limit" (S4b.4). |
| `limit_number_applies` | Whole-number entry is its provider's limit. |
| `untrusted_changes_nothing_guarded` | Untrusted project changes no limit, prompt or credential (S4b.5). |
| `trusted_project_applies` | Trusted project's item applies. |
| `project_entry_never_merges` | Project MCP entry applies whole (S4b.6). |
| `global_entry_kept` | Global entry the project does not name stays whole. |

Saved default model laws: [inference.md](inference.md) ("S6 models.json and the saved default model"), `LAWS.bend` section `config`.

Tie: `settings::bridge::the_rust_config_code_equals_the_bend_model` vs `bend/bridge_config.bend`, byte for byte, 360 generated scenarios: each writer over missing, valid, invalid, unreadable, other-version files; setters after another writer's change; documents with good, wrong-typed, undeclared leaves; `providerMaxInFlight` values; projects under each trust; global and project `mcpServers` entries.

Regression tests: `add_refuses_a_settings_file_that_does_not_parse`, `a_setter_keeps_a_field_that_failed_to_load_and_a_concurrent_edit`, `another_version_is_refused_and_never_rewritten`, `set_over_an_unreadable_auth_file_is_refused_and_writes_nothing`, `a_bad_leaf_drops_only_itself_and_is_named`, `a_setting_a_cfg_file_shadows_says_so`, `a_project_mcp_entry_never_takes_global_credentials`.

### S5. The Director stack

After each final answer the agent loop asks a stack of Directors what to do. Director = one layer: a kind and a budget (loop steps it may still request). Kinds: goal, autonomous run, reminder, forced tool call.

1. Top layer decides first. Verdicts:
   - `Defer`: next layer down decides; layer stays.
   - `Again`: loop continues; costs 1 budget; no budget = yield.
   - `Yield`: loop stops; control to user.
   - `Stack{l}`: push `l` on top of itself, loop continues; costs 1 budget; no budget = yield. Needs room: layers above (including deferred, left or led ones) + the layer + layers below < cap. No room: loop fails.
   - `Leave`: layer removes itself; next layer down decides.
   - `Abort`: loop stops with failure.
   - `Lead`: layer leads the step's continuation: loop goes on → it leaves with it; step ends the loop (no lower layer continues, or no step left) → it stays. Either way the next layer down decides.
2. No layer decides: control to user.
3. Each run's loop has a global step budget; each continuation costs 1; none left: continuation yields.
4. Verdict per kind, from session state:
   - Goal: active = `Again`, unless the progress check stops it (8). Paused, budget-limited, complete or failed = yield. Cleared = leave. Empty reply never reaches the goal: harness fails it as a model error ([harness.md](harness.md) H4.7); goal fails with it.
   - Autonomous: defers while a goal drives continuations (goal keeps priority). Disabled = leave. Else gates and limits give `Again` or `Yield`.
   - Reminder: its text goes first in the step's continuation and it leads it (`Lead`): leaves with it; step not continuing → stays until a continuation comes. Never makes its own continuation; waits for goal or autonomous run.
   - Forced tool call: each request forces its tool (`stream.forceTool`, S6) until a response calls it; layer leaves at the next final answer. Each forced response without the call = miss. Miss after `tries` retries fails the generation with `ForcedToolError::NotCalled` (S6.3), real request count; that miss removes the layer and appends a display row with the error (`eukhe.director`, not in model context) in one commit, so the next request is unforced. Run ending before any forced request: layer continues (`Again`) while budget lasts; continuation only names the forced call, the forced request's soft prompt asks for it. No budget: aborts with `ForcedToolError::NotCalled` and the same row.
5. Step evaluates from the top until one decides. Autonomous gates run before the step commit. One commit: stack, goal and autonomous changes, goal context row, decision. Rerun of the same generation repeats the decision.
6. Run with a new first input = new loop: global budget (`directors.maxSteps`, default 200) restored; goal layer gets it; autonomous layer gets remaining continuations (`autonomous.maxContinuations` minus used). Goal and autonomous run join the stack (goal above autonomous) when driving continuations without a layer, below pushed layers (reminders, forced calls), so pushed layers decide first. `directors.stackCap` (default 8) caps pushed layers only; 2 extra places (goal, autonomous) always have room: max `directors.stackCap + 2` layers, each decision gets that cap. Push past cap: refused with error. No layer: final answer writes nothing.
7. Reminder and forced-call entry points: session slash commands `/remind <text>`, `/force <tool> [--tries <n>]` (TUI sends via daemon); kernel host request `directors.push` (Python REPL `goal.remind(text)`, `goal.force_tool(tool, tries=1)`). Forced call: 1 budget, `tries` 1 by default.
8. Stack = conversation document `eukhe.directors`, rewindable: fork or branch move starts from the stack at its fork entry (rewind drops later Directors, restores removed ones). Resume reads the stored stack. Document is a state tree node (S1) under its conversation.

Model: `bend/director.bend`. Laws: `LAWS.bend` section (S5). Proofs: `PROOF.bend` section `director`. Every verdict free: the adversary picks each layer's verdict each step.

| Law | Says |
| --- | --- |
| `dir_stack_bounded` | Decision never grows stack past cap (S5.1). |
| `dir_loop_stack_bounded` | Nor does the loop, over any steps (S5.1). |
| `dir_loop_ends` | Loop ends (control back or failure) within n + 1 steps, n = global budget, whatever layers say (S5.3). |
| `dir_end_is_final` | Ended loop stays ended (S5.3). |
| `dir_encode_sound` | Stored stack is a sound tree (S5.8). |
| `dir_resume_restores` | Resume reads back the stored stack exactly (S5.8). |
| `dir_rewind_restores` | Rewinding a sound tree to a stack's tree restores that stack exactly (S5.8). |
| `dir_go_*` (`empty`, `unjudged`, `defer`, `leave`, `lead_stays`, `lead_leaves`, `yield`, `abort`, `again`, `again_spent`, `push`, `push_full`, `push_spent`) | One decision per verdict: its effect on stack and outcome (S5.1); together they give every decision exactly. |
| `dir_room`, `dir_decide_goes_on` | A push has room when the whole stack holds fewer than cap layers; a loop decision is the one where a leading layer leaves (S5.1). |
| `dir_tick_goes_on`, `dir_tick_out_of_steps`, `dir_tick_hands_back`, `dir_tick_fails` | One loop step by outcome: goes on with one step fewer, or ends with leading layers staying (S5.1, S5.3). |
| `dir_lead_leaves_with_the_continuation`, `dir_lead_stays_when_the_loop_ends`, `dir_lead_goes_example`, `dir_lead_stays_example` | A step that goes on = the step with every `Lead` read as `Leave`; a step that ends = every `Lead` read as `Defer` (S5.4, reminder). |

Code:

- `eukhe-core/src/durable/directors/stack.rs`: `Loop::tick` (one step, run as the compiled model: entry `bend/ffi_director.bend`, laws `LAWS.bend` section `director_entry`; kinds cross as numbers, counts saturate at the wire's largest Nat), `Layer`, `LayerKind`, `Verdict`.
- `directors/mod.rs`: `DIRECTORS_DOC`, `DirectorState`, `DirectorLimits` (`bound`), `push_director`, `DIRECTOR_NOTICE_CUSTOM_TYPE`.
- `durable/goals/hooks.rs`: `on_yield` step (`begin`, `judge`, `commit_step`); forced tool of `before_request`; call or miss of `after_response`, `mark_forced_response`.
- `durable/goals/host.rs` (`directors.push`); `durable/session_commands.rs` (`/remind`, `/force`); `skills/goal/src/goal/__init__.py` (`remind`, `force_tool`).
- `eukhe-durable/src/harness/generation.rs`: `before_request` hooks may set a request's forced tool (`RequestMessages::force_tool`).
- `eukhe-core/src/settings` `directors`.

Tie: the step is the model itself (no bridge).

Regression tests:

- `durable::directors::tests`: goal layer until completion, global budget, reminder, reminder waiting for a continuation, forced call, forced call never made + unforced next run, goal on full stack, stack after reopen and in a fork.
- `durable::session_commands::tests`: `/remind`, `/force` on the stack; `/force` failing once.
- `durable::goals::tests`.

Not modelled (tied by tests): session state → verdict map (S5.4), `begin` (S5.6), layer kind data (model keeps a number).

#### S5.8. A goal without progress stops

8. At each continuation of an active goal the progress check counts the session's distinct acts: tool call + result (by tool name, arguments, result text, error flag), or an accepted progress note. Call ids, timestamps, text and thinking around a call: not work. Compared with the work at the last continuation of the same run and goal:
   - Work grew: no-progress streak = 0; goal continues.
   - Work did not grow: streak + 1. Under the cap: continues; continuation tells the model the streak and that the goal pauses at the cap. At cap (`directors.stallSteps`, default 3; `0` = default): goal pauses with reason `No progress: <n> goal continuations in a row made no tool call with a new result`, run yields, display row (`eukhe.director`, not in model context) says why and how to go on.
   - First continuation of a run or new goal starts the count: new user input or resume restores the full cap.

   Default 3: continuation 1 may only state a plan, 2 carries the note asking for one concrete step, 3 shows the model did not act. Without the check, an active goal with no token budget got up to `directors.maxSteps` (200) answer-only continuations (e.g. "waiting for the build"), each a full-context request. Reply with no text and no tool call = model error (H4.7); the check counts work, not replies.

Model: `bend/progress.bend` (`work`, `check`, `goal`, `judge`). Laws (`LAWS.bend` section `progress`): `goal_stops_without_progress` (cap-many consecutive continuations with only previously seen acts stop the goal from any count), `goal_progress_continues` (a continuation with a never-seen act clears the count); laws of `judge` (the check the Rust loop runs on the ledger's counts): `goal_first_check_starts`, `goal_judge_is_check`, `goal_judge_counts_work` (count grew exactly when the session did new work), `goal_judge_held`, `goal_judge_top_stops` (count held within the wire's largest Nat; a count there stops a goal with no new work); `goal_entry` (section `core_w6`: the core's entry answers the encoded `judge` on the request Rust writes). Proofs: `PROOF.bend` section `progress`.

Rust: `eukhe-core/src/durable/children/work.rs` (`WorkLedger`), `durable/goals/state.rs` (`stall_check`: `judge`, run as the compiled Bend core, `bend/ffi_progress.bend`), `durable/goals/hooks.rs` (`goal_check`, work read in `on_yield`, pause and row in `commit_step`), `durable/directors/mod.rs` (`DEFAULT_STALL_STEPS`).

Tie: `durable::goals::hooks::bridge::the_rust_progress_check_equals_the_bend_model` runs the ledger over real transcripts and `goal_check` vs `bend/bridge_progress.bend`. Regression: `durable::goals::tests::a_goal_without_progress_pauses_at_the_stall_cap`.
