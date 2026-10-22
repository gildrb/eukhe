# Harness laws: settings and directors

The shared rules (what a law secures, the adversary, H1 to H6) are in [harness.md](harness.md).

### S4. Settings as console variables

Each setting is a console variable (a cvar). One table declares each cvar
once: its id, its type, its scope, two flags and its default. The id is
the dotted path of the key in `settings.json` (`retry.enabled`).

1. The registry holds each id once. A second declaration of an id, or a
   default that does not have the type of its cvar, stops eukhe at
   startup (`RegistryError`).
2. The scope is Global or Local. A Global cvar has one value for every
   agent: only the global config sets it. A Local cvar can have a
   different value in each agent.
3. `persist`: an agent can write its sets of the cvar to its cfg.
   `replicate`: clients see the value of the cvar.

The value of a cvar comes from layers. A higher layer wins:

```text
default < config < each agent of the family, root first:
                   its profile < its own sets
```

- The config is `settings.json` (global, then project) and then
  `config.cfg` (global `<agent dir>/config.cfg`, then project
  `.eukhe/config.cfg`). The project files obey the project trust rules
  of `settings.json`. A project file never sets a Global cvar.
- The profile of a subagent is `subagent.cfg`, then
  `agents/<name>.cfg` for a named agent. The root session is the agent
  `main`.
- The sets of an agent are its runtime sets (`/set`, `/toggle`, the
  session switches). They are session state: the conversation document
  `eukhe.cvar.agent`, committed on each change. So the state tree shows
  them, and a rewind or a fork restores them.

In each layer, the last valid set of a cvar wins. A set is valid when its
cvar is declared and its value has the type of the cvar. In a profile or
an agent's sets, the cvar must also be Local. A set that is not valid is
rejected with a typed error (`CvarError`): `Undeclared`, `BadValue`,
`Global`, `NotBool`.

A subagent starts from the family of its parent: the spawn carries the
parent's layers. Its own profile and sets go on top of them.

The session switches (transport, steering mode, follow-up mode, auto
retry, auto compaction, service tier) are sets of the session's own
agent. They do not change another session. A session cannot set a Global
cvar: `/set --global` writes it to the global `config.cfg`. A `toggle`
in `/set --global` flips the value of the global layer only (the global
`settings.json`, then the global `config.cfg`). A project file never
changes what it flips. The read, the change and the write of a cfg file
hold the lock of the file, so two sessions that write at the same time
do not lose a set. A cfg file that exists but eukhe cannot read is a
settings error, and eukhe does not write it. The errors of a profile
file and of an alias in the agent state that does not parse are
settings errors too. The `eukhe.settings` service shows the settings
errors of a session as an `eukhe.settings_error` row of its main
conversation (display-only: the model does not see it). It shows the
errors at open, and after a reload it shows each new error. It shows
each distinct error one time for each session that eukhe opens.

The command language is the same in the cfg files, in the `/set` slash
command family and in key binds. A line is a list of commands, separated
by `;`. A word in double quotes keeps its spaces.

| Command | Does |
| --- | --- |
| `set <id> <value>` | Sets the cvar. |
| `toggle <id>` | Sets a Bool cvar to the opposite of its value in the agent, with the values the agent inherits. |
| `alias <name> "<cmds>"` | Gives a name to a list of commands. |
| `bind <key> "<cmds>"` | Gives the commands that a key press runs. |
| `action <id>` | Runs a built-in client action (in a bind). |
| `<name>` | Runs the alias `<name>`. |

4. An expansion replaces each run of an alias with its commands. It
   nests at most one level per alias of the table and one more. A deeper
   nest repeats an alias, so it is a cycle (`ExpandError::Cycle`). A run
   of an alias that does not exist is `ExpandError::Unknown`. An
   expansion that fails runs nothing.
5. The key binds are in `<agent dir>/binds.cfg`. The first bind of a key
   wins: the user's binds come before the default binds. A key with no
   bind runs nothing; an empty bind (`bind <key> ""`) turns off a
   default. The default actions that share a key share one bind; the
   screen that gets the key runs its own action. A key press sends its
   `set`, `toggle` and `alias` commands to the session and runs its
   `action` commands in the client. eukhe writes `binds.cfg` one time
   from `keybindings.json` when `binds.cfg` does not exist; the binds it
   writes give each key the actions that `keybindings.json` gave it. A
   `binds.cfg` that eukhe cannot read, or an import that eukhe cannot
   write, shows a warning at startup and at `/reload`.
6. `/cvar save` writes the agent's sets of `persist` cvars to its
   `agents/<name>.cfg`. Read back as the profile, they give the same
   values.

Model: `bend/cvar.bend` (`registry`, `value`, `written`, `toggle`,
`expand`, `press`). Laws: `LAWS.bend` section (S4). Proofs:
`PROOF.bend` section `cvar`. Every input is free: any declarations (with
duplicate ids and wrong defaults), any config, any family of agents with
any profiles and sets (wrong types, Global cvars, undeclared ids), any
alias table and any binds.

| Law | Says |
| --- | --- |
| `cvar_registry_unique` | The registry holds each id once (S4.1). |
| `cvar_registry_typed` | Each default of the registry has its type (S4.1). |
| `cvar_value_typed` | Each value has the type of its cvar in each agent; an undeclared cvar has no value. |
| `cvar_inherits` | A subagent with no profile and no sets has its parent's values. |
| `cvar_set_wins` | The last valid set of a subagent wins over its parent's value. |
| `cvar_global_uniform` | A Global cvar has one value in each agent: the config on the default (S4.2). |
| `cvar_written_flagged` | An agent writes to its cfg only `persist` cvars and replicates only `replicate` cvars (S4.3). |
| `cvar_persist_roundtrip` | The written cfg, read back as the profile, gives the same value of each persisting cvar (S4.6). |
| `cvar_toggle_twice` | Two toggles give back the value. |
| `alias_expands_fully` | An expansion leaves no alias to run, or it reports a cycle or an unknown alias (S4.4). |
| `alias_self_cycle` | An alias that runs itself is a cycle, and the cycle names the alias (S4.4). |
| `alias_unknown_reported` | A run of an alias that does not exist is reported with its name (S4.4). |
| `alias_runs_body` | An alias of plain commands runs exactly its commands (S4.4). |
| `alias_expands_in_order` | A list expands command by command, in order: the expansion of two lists is the first's commands, then the second's, and the first error, left to right, is the outcome (S4.4). |
| `alias_expand_example` | Anchor: the Rust test's table (a chain of two aliases, a cycle of two, a run of a missing alias) (S4.4). |
| `bind_press_plain` | A key press runs only plain commands (S4.5). |
| `bind_unbound_runs_nothing` | A key with no bind runs nothing (S4.5). |
| `bind_first_wins` | A key press runs the commands of the first bind of the key (S4.5). |

Code: `eukhe-types/src/cvar.rs` (the command language: `parse_list`,
`parse_script`, `Aliases`, `expand`, `Binds::press`);
`eukhe-core/src/settings/cvar.rs` (`Registry`, `Cvars::value`,
`Cvars::execute`, `Sets::written`, `document_sets`) and
`settings/cvar/table.rs` (the declarations); `settings/cfg.rs` (the
config layer: `settings.json`, then the `config.cfg` files under the
trust rules); `settings/manager.rs` and `settings/getters.rs` (the
getters, all through `Cvars`); `eukhe-core/src/durable/cvar_agent.rs` (the
session's agent: `CvarAgent`, the `eukhe.cvar.agent` document,
`run_cvar_line`, `save_agent_cfg`) and `durable/settings.rs`
(`EukheSettings`: the family of the session over its config). The daemon
commands `cvar { line, global }` and `cvar_save` run them
(`eukhe-daemon/src/setting_switches.rs`); a refused command answers its
`CvarError` with `data: { kind, id?, message }`. A spawn carries the parent's
family in the create config (`cvarFamily`). The TUI sends `/set`,
`/toggle`, `/alias` and `/cvar` as `cvar` lines
(`eukhe-tui/src/session_ui/cvar.rs`).

Ties: the bridge test
`settings::cvar::bridge::the_rust_cvars_equal_the_bend_model` compares
transcripts with `bend/bridge_cvar.bend` byte for byte. It runs 300
generated scenarios: registries (with duplicate ids and wrong
defaults), values over a config and a family (wrong types, Global
cvars, undeclared ids, profiles and sets), toggles of the last agent of
a family (a subagent toggles a value that it inherits), the written sets
(`persist` and `replicate`), expansions (cycles, unknown aliases) and
key presses. The scenarios reach every rule.

Regression tests: `a_switch_changes_only_its_own_session` (daemon: two
workers over one agent dir; the switches of one do not change the other
or `settings.json`); `a_setter_never_clobbers_a_global_settings_file_that_failed_to_parse`
(a setter refuses to write over a `settings.json` that did not parse);
`cvar_rejects_a_global_cvar_from_a_session`;
`a_subagent_inherits_its_parents_family_under_its_profile`;
`a_fork_starts_from_the_agent_state_at_its_fork_point`;
`an_unreadable_cfg_file_is_reported_and_never_overwritten`;
`concurrent_global_sets_both_land`;
`a_global_toggle_flips_the_global_value_not_the_projects`;
`profile_and_agent_alias_errors_reach_the_manager`;
`settings_errors_show_as_a_row_of_the_session`;
`unreadable_binds_cfg_and_failed_import_are_warnings`; the
`keybindings::tests` of the `binds.cfg` import and of the presses.

### S4b. Config documents

The config documents are `settings.json` (global and project),
`mcp-connections.json` and `auth.json`. No input of these documents is
lost in silence.

1. A writer reads the document under its lock, applies its change, and
   writes the result. When the read fails (the file cannot be read, it is
   not valid JSON or not an object, or its version is not known), the
   writer writes nothing and returns the error. Only a file that is not
   there reads as empty. Each key that the change does not touch keeps
   its value. This applies to `eukhe mcp add` and `eukhe mcp remove`, to
   each settings setter, to the connection records and to `AuthStorage`
   `set` and `remove`. `set` and `remove` return the error to the caller.
2. A settings setter writes the document that is on disk when it writes,
   not the copy that it loaded. A key that failed to load stays, and a
   key that another writer added stays. The setter refuses a value that
   its setting does not hold. When a higher layer sets the same setting
   (the global `config.cfg`, the project `settings.json` or the project
   `config.cfg`), the setter says which file sets it
   (`Persisted::Shadowed`), and the client shows it. The daemon shows a
   default model or thinking level that it could not save as a settings
   error row.
3. Each leaf of a `settings.json` applies or is named by a settings
   error. A leaf is a value that is not an object, or the whole value of
   a cvar. A value that its setting does not hold is `BadValue`; a key
   that no setting declares is `Undeclared`. These are the same
   `CvarError`s as for `config.cfg`, and they show in the same row. One
   bad leaf drops only that leaf. The known top-level keys come from the
   `Settings` type.
4. A malformed limit fails closed. A `providerMaxInFlight` entry that is
   not a whole number limits its provider to 1 request; a value that is
   not a map limits each provider to 1. `idleEvictionMinutes` and the
   session archive rules are a whole number, `off` or `none`
   (`NatOrOff`); another value is a settings error.
5. An untrusted project does not change a limit, a system prompt or a
   credential: `maxToolRounds`, `subagentMaxConcurrency`,
   `subagentStallMs`, `toolBlockingBudgetMs`, `autonomous`, `directors`,
   `thinkingBudgets`, `retry.maxRetries` and `retry.failover.maxRetries`
   are withheld with the keys that run code, and so are the project
   `SYSTEM.md` and `APPEND_SYSTEM.md`. The trust warning names them.
   `trustedProjects` comes from the global layer only (the global
   `settings.json`, then the global `config.cfg`).
6. An `mcpServers` entry is a unit: a project entry replaces the global
   entry of its name, and it never takes a URL or a credential from it.
   `kernelTransport` is a unit too.
7. The sessions directory has one precedence for each reader (the CLI,
   the dashboard, the gateway and the daemon,
   `settings::resolve_session_dir`): the `--session-dir` flag, then
   `EUKHE_SESSION_DIR` (or the legacy `EUKHE_CODING_AGENT_SESSION_DIR`),
   then the `sessionDir` setting, then `<agent dir>/sessions`.

Model: `bend/config.bend`. Laws: `LAWS.bend` section `config`. Proofs:
`PROOF.bend` section `config`.

| Law | Says |
| --- | --- |
| `rmw_refuses_broken` | A document that could not be read or parsed is never written (S4b.1). |
| `rmw_keeps_others` | A write keeps each key that the change does not touch (S4b.1). |
| `rmw_applies_change` | The key that the change sets has the value that it sets. |
| `settings_save_preserves` | A setter writes the document on disk with its key changed, whatever copy it loaded (S4b.2). |
| `leaf_applied_or_reported` | Each leaf applies or is named by a diagnostic (S4b.3). |
| `leaf_not_both` | No leaf both applies and is named. |
| `limit_malformed_fails_closed` | A malformed in-flight limit limits to 1, never "no limit" (S4b.4). |
| `limit_number_applies` | A whole-number entry is its provider's limit. |
| `untrusted_changes_nothing_guarded` | An untrusted project changes no limit, prompt or credential (S4b.5). |
| `trusted_project_applies` | A trusted project's item applies. |
| `project_entry_never_merges` | A project MCP entry applies whole (S4b.6). |
| `global_entry_kept` | A global entry that the project does not name stays whole. |

The laws of the saved default model are in [inference.md](inference.md)
("S6 models.json and the saved default model") and in
`LAWS.bend` section `config`.

Ties: the bridge test
`settings::bridge::the_rust_config_code_equals_the_bend_model` compares
transcripts with `bend/bridge_config.bend` byte for byte. It runs 360
generated scenarios: each writer over a missing, valid, invalid,
unreadable and other-version file; setters after another writer changed
the file; documents with good, wrong-typed and undeclared leaves;
`providerMaxInFlight` values; projects under each trust; and global and
project `mcpServers` entries.

Regression tests: `add_refuses_a_settings_file_that_does_not_parse`;
`a_setter_keeps_a_field_that_failed_to_load_and_a_concurrent_edit`;
`another_version_is_refused_and_never_rewritten`;
`set_over_an_unreadable_auth_file_is_refused_and_writes_nothing`;
`a_bad_leaf_drops_only_itself_and_is_named`;
`a_setting_a_cfg_file_shadows_says_so`;
`a_project_mcp_entry_never_takes_global_credentials`.

### S5. The Director stack

After each final answer, the agent loop asks a stack of Directors what to
do. A Director is one layer of the stack. A layer has a kind and a
budget: the loop steps that it can still ask for. The kinds are the goal,
the autonomous run, a reminder, and a forced tool call.

1. The top layer decides first. Each layer gives one verdict:
   - `Defer`: the next layer down decides. The layer stays.
   - `Again`: the loop continues. This costs the layer 1 unit of its
     budget. A layer with no budget yields.
   - `Yield`: the loop stops and gives control back to the user.
   - `Stack{l}`: the layer puts `l` on top of itself, and the loop
     continues. This costs 1 unit of budget. A layer with no budget
     yields. A push needs room in the full stack: the layers above the
     layer (also the layers that deferred, left or led), the layer, and
     the layers below must be fewer than the cap. With no room, the loop
     fails.
   - `Leave`: the layer removes itself. The next layer down decides.
   - `Abort`: the loop stops with a failure.
   - `Lead`: the layer leads the continuation of the step. It leaves with
     that continuation: when the loop goes on, it leaves; when the step
     ends the loop (no layer below continues, or no step is left), it
     stays. Either way the next layer down decides.
2. When no layer decides, the loop gives control back to the user.
3. The loop of one run has a global budget of steps. Each continuation
   costs 1 step. When no step is left, a continuation yields.
4. The verdict of each kind comes from the session state:
   - Goal: an active goal mints a continuation (`Again`), unless its
     progress check stops it (8). A paused, budget-limited, complete, or
     failed goal yields. A cleared goal leaves. An empty reply never gets
     to the goal: the harness fails it as a model error
     ([harness.md](harness.md) H4.7), and the goal fails with that error.
   - Autonomous: it defers while a goal drives continuations, so the goal
     keeps its priority. A disabled run leaves. Else its gates and limits
     continue the run (`Again`) or stop it (`Yield`).
   - Reminder: its text goes first in the continuation of the step, and it
     leads that continuation (`Lead`): it leaves with it, and when the step
     does not continue it stays on the stack until a continuation comes. A
     reminder never makes its own continuation, so it waits for the goal or
     the autonomous run.
   - Forced tool call: each request forces its tool (`stream.forceTool`,
     S6) until a response calls the tool. Then the layer leaves at the next
     final answer. Each response to a forced request without the call is
     a miss. The miss after the `tries` retries fails the generation with
     `ForcedToolError::NotCalled` (S6.3), with the real number of
     requests. That miss removes the layer and appends a display row with
     the error (`eukhe.director`, not in the model context) in one commit,
     so the next request is not forced. When a run ends before a request
     forced the tool, the layer continues the run (`Again`) while it has
     budget. The continuation only names the forced call; the soft prompt
     of the forced request asks for the call. With no budget, the layer
     aborts with `ForcedToolError::NotCalled` and the same display row.
5. A step evaluates the layers from the top until one decides. The
   autonomous gates run before the commit of the step. The step commits
   the stack, the goal and autonomous changes, the goal context row, and
   its decision in one commit. A rerun of the same generation repeats the
   decision.
6. A run that has a new first input starts a new loop: the global budget
   (`directors.maxSteps`, default 200) comes back, the goal layer gets that
   budget, and the autonomous layer gets its remaining continuations
   (`autonomous.maxContinuations` minus the used ones). The goal and the
   autonomous run come on the stack (the goal above the autonomous run)
   when they drive continuations and have no layer. They go below the
   pushed layers (reminders and forced calls), so the pushed layers decide
   first. `directors.stackCap` (default 8) caps the pushed layers only. The
   stack keeps 2 more places, one for the goal and one for the autonomous
   run, so these always have room: a stack holds at most
   `directors.stackCap + 2` layers, and each decision gets that cap. A
   push past the cap is refused with an error. With no layer, a final
   answer writes nothing.
7. Reminders and forced calls come on the stack from these entry points:
   the `/remind <text>` and `/force <tool> [--tries <n>]` session slash
   commands (the TUI sends them through the daemon), and the kernel host
   request `directors.push` (`goal.remind(text)` and
   `goal.force_tool(tool, tries=1)` in the Python REPL). A forced call
   gets 1 unit of budget and `tries` 1 when not given.
8. The stack is the conversation document `eukhe.directors`. It is
   rewindable: a fork or a branch move starts from the stack as of its
   fork entry, so a rewind removes the Directors added after that entry
   and brings back the ones removed. A resume reads the stored stack.
   The document is a node of the state tree (S1), under its conversation.

Model: `bend/director.bend`. Laws: `LAWS.bend` section (S5). Proofs:
`PROOF.bend` section `director`. Every verdict is free: each layer of each
step says what the adversary picks.

| Law | Says |
| --- | --- |
| `dir_stack_bounded` | A decision never grows the stack past its cap (S5.1). |
| `dir_loop_stack_bounded` | So the loop never does, whatever its steps (S5.1). |
| `dir_loop_ends` | The loop ends (gives control back or fails) after at most n + 1 steps, with n its global budget, whatever every layer says (S5.3). |
| `dir_end_is_final` | An ended loop stays as it ended (S5.3). |
| `dir_encode_sound` | The stack in the tree is a sound tree (S5.8). |
| `dir_resume_restores` | A resume reads back the stack that the tree holds, exactly (S5.8). |
| `dir_rewind_restores` | A rewind of a sound tree to the tree of a stack restores that stack, exactly (S5.8). |
| `dir_go_*` (`empty`, `unjudged`, `defer`, `leave`, `lead_stays`, `lead_leaves`, `yield`, `abort`, `again`, `again_spent`, `push`, `push_full`, `push_spent`) | One decision, verdict by verdict: what each verdict does to the stack and the outcome (S5.1). Together they give every decision exactly. |
| `dir_room`, `dir_decide_goes_on` | A push has room when the whole stack holds fewer than cap layers; a decision of the loop is the one where a layer that leads leaves (S5.1). |
| `dir_tick_goes_on`, `dir_tick_out_of_steps`, `dir_tick_hands_back`, `dir_tick_fails` | One loop step, by its outcome: it goes on with one step fewer, or it ends and the layers that lead stay (S5.1, S5.3). |
| `dir_lead_leaves_with_the_continuation`, `dir_lead_stays_when_the_loop_ends`, `dir_lead_goes_example`, `dir_lead_stays_example` | A step that goes on is the step with every `Lead` read as `Leave`; a step that ends is the step with every `Lead` read as `Defer` (S5.4, the reminder). |

Code: `eukhe-core/src/durable/directors/stack.rs` `decide`, `Loop::tick`,
`Layer`, `LayerKind`, `Verdict`; `directors/mod.rs` `DIRECTORS_DOC`,
`DirectorState`, `DirectorLimits` (`bound`), `push_director`,
`DIRECTOR_NOTICE_CUSTOM_TYPE`; `durable/goals/hooks.rs` (the `on_yield`
step: `begin`, `judge`, `commit_step`; the forced tool of
`before_request`; the call or the miss of `after_response`,
`mark_forced_response`); `durable/goals/host.rs` (`directors.push`);
`durable/session_commands.rs` (`/remind`, `/force`);
`skills/goal/src/goal/__init__.py` (`remind`, `force_tool`);
`eukhe-durable/src/harness/generation.rs` (the `before_request` hooks may
set the forced tool of a request, `RequestMessages::force_tool`);
`eukhe-core/src/settings` `directors`.

Tie: the bridge test
`durable::directors::bridge::the_rust_director_stack_equals_the_bend_model`
runs `decide`, `Loop::tick`, and the persisted `eukhe.directors` value
against `bend/bridge_director.bend` on 300 generated scenarios (stacks,
verdict lists per step, caps, global budgets; the model's `decide`,
`tick`, `run`, `encode`, and `decode`), and compares the transcripts byte
for byte. The scenarios reach every rule of the model (a push with room,
a push that fits only the layers below, a full stack, no budget, a
leave, all layers defer, no step left, a tick after the end, a lead that
leaves with the continuation, a lead that stays). Regression
tests: `durable::directors::tests` (the goal layer until the goal
completes, the global budget, a reminder, a reminder that waits on the
stack for a continuation, a forced tool call, a forced call that is never
made and a next run that is not forced, the goal on a full stack, the
stack after a reopen and in a fork); `durable::session_commands::tests`
(`/remind` and `/force` on the stack, a `/force` that fails once);
`durable::goals::tests`. Not modelled: the map from the session state to
the verdicts (S5.4), `begin` (S5.6), and the kind data of a layer (the
model keeps a number for the kind). Their tests tie them.

#### S5.8. A goal without progress stops

8. At each continuation of an active goal, the progress check looks at
   the work of the session: the number of its distinct acts (a tool call
   with its result, by tool name, arguments, result text and error flag;
   or an accepted progress note). Call ids, timestamps, and the text and
   thinking around a call are no work. The check compares the work with
   the work at the last continuation of the same run and goal:
   - The work grew: the count of continuations in a row with no new work
     goes back to 0, and the goal continues.
   - The work did not grow: the count grows by 1. Under the cap, the goal
     continues, and its continuation tells the model how many
     continuations in a row did no new work and that the goal pauses at
     the cap. At the cap (`directors.stallSteps`, default 3; `0` takes
     the default), the goal pauses with the reason (`No progress: <n>
     goal continuations in a row made no tool call with a new result`),
     the run yields, and a display row (`eukhe.director`, not in the
     model context) tells the user why and how to go on.
   - The first continuation of a run, or of a new goal, starts the
     count: a new user input or a resume gives the goal the full cap
     again.

   Before this check, an active goal with no token budget got up to
   `directors.maxSteps` (200) continuations when the model only answered
   (for example "waiting for the build"), each a request with the full
   context. The default 3: the first continuation can be an answer that
   only states a plan, the second carries the note that asks for one
   concrete step, and the third shows that the model did not act on it.
   (An earlier strike counted replies with no text and no tool call. Such
   a reply is now a model error, H4.7, so that strike was removed. This
   check counts work, not replies.)

Model: `bend/progress.bend` (`work`, `check`, `goal`, `judge`). Laws
(`LAWS.bend` section `progress`): `goal_stops_without_progress` (continuations in a
row whose acts the session did before, at least as many as the cap, stop
the goal from any count), `goal_progress_continues` (a continuation
with an act the session never did before clears the count), and the laws
of `judge`, the check the Rust loop runs on the ledger's counts:
`goal_first_check_starts`, `goal_judge_is_check`, `goal_judge_counts_work`
(the count grew exactly when the session did new work), `goal_judge_held`
and `goal_judge_top_stops` (the count is held within the wire's largest
Nat, and a count there stops a goal that did no new work), and
`goal_entry` (section `core_w6`: the core's entry answers the encoded
`judge` on the request Rust writes). Proofs:
`PROOF.bend` section `progress`.

Rust: `eukhe-core/src/durable/children/work.rs` (`WorkLedger`),
`durable/goals/state.rs` (`stall_check`: `judge`, run as the compiled
Bend core, `bend/ffi_progress.bend`), `durable/goals/hooks.rs`
(`goal_check`, the work read in `on_yield`, the pause and its row in
`commit_step`), `durable/directors/mod.rs` (`DEFAULT_STALL_STEPS`).

Tie: the bridge test
`durable::goals::hooks::bridge::the_rust_progress_check_equals_the_bend_model`
runs the ledger over real transcripts and `goal_check` against
`bend/bridge_progress.bend`. Regression test:
`durable::goals::tests::a_goal_without_progress_pauses_at_the_stall_cap`.
