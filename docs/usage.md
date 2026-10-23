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

## Agents

- Subagents: `rlm.spawn`, `rlm.spawn_batch` in the Python REPL.
- Family = all agents under one root session. Message any member by name, id or `parent/child` path; `all` for everyone.
- Subagent-to-subagent messages also show in the root chat as relay rows.
- The roster note has each agent's latest report or progress.
- `@name message`: message a family agent; reply shows as `name -> you`.
- `/agents`: session agents with status, depth, model, work.
- Agents view: Esc clears the search, then returns to the opening chat; Ctrl+D on empty search or double Ctrl+C exits.

Settings: [settings.md](settings.md#agents-and-providers).

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
