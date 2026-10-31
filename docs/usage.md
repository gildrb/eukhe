# Usage

## Commands

```sh
cd /path/to/project
eukhe                      # start; run /login on first launch
eukhe agents               # search and open sessions
eukhe attach <agent>       # attach to a running session
eukhe --resume [path|id]   # resume a session
eukhe chat view            # print the memory view
eukhe chat status [--json] # chat size, compactor progress
eukhe chat browse          # whole memory as one HTML page
eukhe chat import sessions <path>...
eukhe status               # daemon state
eukhe state [agent]        # session state tree
eukhe provider caps        # provider capabilities; no network
eukhe provider models <p>  # models of provider <p>
eukhe tiny-models          # list or download local models
eukhe config               # show and set installed resources; no network
eukhe package install <s>  # install an npm or git package; add it to settings
eukhe package update [s]   # update installed packages
eukhe doctor [--fix]       # check or repair the daemon
eukhe shutdown [--force]   # stop all agents and the daemon
```

Only `eukhe package install`/`update` download (npm, git). Sessions and `eukhe config` use installed packages only and warn per missing configured package with its `eukhe package install` command.

## Slash commands

- `/` at prompt start: command menu, fuzzy on names and aliases.
- Space after a command name, or Tab/Enter on a command row: `/<name> `, its subcommand menu opens at once.
- Subcommand menu: the rows whose name starts with the typed word (any case). Tab/Enter on a row: `<sub> `, the next level opens if any. Ghost text after the cursor: rest of the selected row, then its usage.
- Enter on a fully typed path runs it: `/memory model`, `/workflows size large`. Bare command with subcommands: its default (`/memory` = `/memory view`, `/model` = the role hub). Bare path that needs a choice (`/dynamic-workflow --size`): its menu opens, nothing runs.
- A path never runs its parent. Unknown subcommand: `Unknown: /memory x. Did you mean /memory view?`; nothing runs.
- Paths: `/memory [view|model]`, `/model [<role>]`, `/workflows [size [small|medium|large]]`, `/dynamic-workflow [--size small|medium|large] <request>`, `/autoresearch [status|off|clear|<goal>]` ([workflows.md](workflows.md) "Autoresearch"), `/tier [<tier>]`, `/effort [<level>]` (the levels of the current model).

## Agents

- Subagents: `rlm.spawn`, `rlm.spawn_batch` in the Python REPL. One loop does the work; a spawn needs `why`: `parallel`, `isolate`, `tools` or `user`. Skill `subagents`: when and how.
- Family = all agents under one root session. Message any member by name, id or `parent/child` path; `all` for everyone.
- Subagent-to-subagent messages also show in the root chat as relay rows.
- The roster note has each agent's latest report or progress.
- `@name message`: message a family agent; reply shows as `name -> you`.
- `/agents`: session agents with status, depth, model, work.
- Agents view: Esc clears the search, then returns to the opening chat; Ctrl+D on empty search or double Ctrl+C exits.

Settings: [settings.md](settings.md#agents-and-providers).

## Skills

A skill teaches how; a tool does. The prompt lists each skill's name and description only (level 1). The model reads `SKILL.md` when a task matches (level 2: steps, rules, judgment, about 2 KB) and `references/` only when a step needs it (level 3: signatures, fields, examples). `evals/cases.jsonl`: golden routing examples `{prompt, expect_skill, expect}`. Rules and format: skill `skill-creator`. Guard: `crates/eukhe-core/tests/prompt_guards.rs` (each tool documented once, in `core.md` or its skill; description at most 1024 bytes and distinct; body at most 2560 bytes; links resolve; eval cases name real skills; zero load diagnostics).

|Skill|Use when|Kind|Level 3|
|---|---|---|---|
|`subagents`|before any spawn: parallel, isolate, tools, user|markdown|`references/api.md` (`rlm.*`)|
|`agent-message`|ask the agent with the context, reply to the parent, steer a child|python|`references/api.md`|
|`agent-observe`|read the family roster, an agent's detail or recent messages|python|`references/api.md`|
|`attach-image`|see an image file|python|none|
|`compact`|context fills while work remains|python|none|
|`goal`|persistent goal: start on request, complete when achieved|python|`references/api.md`|
|`refine`|a repeated failure or reusable tactic worth keeping|python|none|
|`rlm-heartbeat`|agent-owned recurring wake-ups (not `/heartbeat`)|python|`references/api.md`|
|`mcp`|external services over MCP|markdown|`references/api.md`|
|`factory`|stored state machines of child agents|markdown|`references/guide.md`, `rlm.factory.help()`|
|`skill-creator`|write, trim or review a skill; skill vs tool vs subagent|markdown|`references/format.md`, `references/python-skills.md`|
|`autoresearch`|`/autoresearch`, or optimize code toward a metric over many measured iterations|python|`references/api.md`|

## Providers

- `eukhe provider caps [provider]`: non-chat capabilities (count tokens, list models, embeddings, images, usage, web search, compaction); sends no request.
- `eukhe provider models <provider>`: asks the provider: ID, name, context, max output.
- `/model`: model role hub (chat, memory, auxiliary, image, subagent, gateway, titles, judge, translate, speech, dictation), each with model and source; `/model <role>` opens one role's models. Picks save globally; `chat` also switches the session. [settings.md](settings.md#model-roles).

## Session state

State tree per session: conversations, tasks, jobs, documents.

```sh
eukhe state [agent]                   # show the tree
eukhe state --since <cursor>          # changes after a cursor
eukhe state --follow                  # new changes until Ctrl+C
eukhe state rewind-plan <cursor>      # what a rewind stops, starts, restores
```
