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
- Paths: `/memory [view|model]`, `/model [<role>]`, `/workflows [size [small|medium|large]]`, `/dynamic-workflow [--size small|medium|large] <request>`, `/tier [<tier>]`, `/effort [<level>]` (the levels of the current model).

## Agents

- Subagents: `rlm.spawn`, `rlm.spawn_batch` in the Python REPL.
- Family = all agents under one root session. Message any member by name, id or `parent/child` path; `all` for everyone.
- Subagent-to-subagent messages also show in the root chat as relay rows.
- The roster note has each agent's latest report or progress.
- `@name message`: message a family agent; reply shows as `name -> you`.
- `/agents`: session agents with status, depth, model, work.
- Agents view: Esc clears the search, then returns to the opening chat; Ctrl+D on empty search or double Ctrl+C exits.

Settings: [settings.md](settings.md#agents-and-providers).

## Main and worker

`sessionShape` `main-worker` (default `single`; [settings.md](settings.md#agents-and-providers)), read when a root session opens:

- Main talks with you; one persistent child, `worker`, does the work. Main keeps its turns short and runs no long work: its tools are read-only (`read`, `grep`, `glob`, `zoom`, `date`) plus `worker_assign`, `worker_forward`, `worker_status`.
- Main routes each message by the tool it picks: it answers questions and chat itself (from `worker_status`, `zoom("worker")`, its read-only tools); context or an idea for the running work goes to the worker as `context` (folded in, same course); a change of course as `redirect` (the worker re-plans); new work as a task (`worker_assign`; a second worker `worker-2` for unrelated work while the first is busy).
- Your words reach the worker verbatim, with the images and `@file` references you sent with them, in order, once: main never restates them; its own note is labeled `[note from main]`. They land between the worker's tool calls, never inside one.
- The worker has the chat view (as a subagent: it logs nothing and never waits for main's turn) and reports to main with an agent message. It keeps that when stopped and woken again. Its model: `workerModel` (the `worker` role of `/model`), else main's. It may spawn its own subagents (`rlmMaxDepth` 3).
- `/goal` and `/autonomous` typed on main run on the worker, where the work runs (a stopped worker wakes for them); main's chat records where they went, the worker's chat shows the result. Before main has a worker they are refused: give main work first.
- Pause: `/pause` or Esc twice within 1 s on main sends `pause_workers`: the worker tree's current model request and tool calls finish; no new request, tool call or spawn starts; detached jobs keep running. Nothing is killed. The worker row shows `paused`, and a paused worker releases its kernel like an idle one.
- Wake: `/resume`, Enter on the paused worker row, any message main forwards, or your `@worker` message resumes from where it parked, with its whole context; messages sent meanwhile are delivered once, in order. A wake ends the whole tree's pause: main's row shows the worker running again.
- Alt+W toggles the live worker pane (right side at 140+ columns, else a bottom strip); Alt+Shift+W shows it full; Esc returns. The pane watches the worker without taking its approvals or holding its kernel.

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
