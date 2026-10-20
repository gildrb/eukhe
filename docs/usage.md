# Usage

## Commands

```sh
cd /path/to/project
eukhe                      # start; run /login on first launch
eukhe agents               # search and open sessions
eukhe attach <agent>       # attach to a running session
eukhe --resume [path|id]   # resume a session
eukhe chat view            # print the memory view
eukhe chat status [--json] # show the chat size and compactor progress
eukhe chat browse          # write the whole memory as one HTML page
eukhe chat import sessions <path>...
eukhe status               # show daemon state
eukhe state [agent]        # show the session state tree
eukhe provider caps        # list provider capabilities; no network
eukhe provider models <p>  # list the models of provider <p>
eukhe tiny-models          # list or download local models
eukhe config               # show and set the installed resources; no network
eukhe package install <s>  # install an npm or git package; add it to settings
eukhe package update [s]   # update the installed packages
eukhe doctor [--fix]       # check or repair the daemon
eukhe shutdown [--force]   # stop all agents and the daemon
```

Only `eukhe package install` and `eukhe package update` download packages
(npm or git). Sessions and `eukhe config` use the installed packages only.
They do not install or fetch a package. For each configured package that
is not installed, they show a warning with the `eukhe package install`
command for it.

## Agents

An agent spawns subagents from its Python REPL with `rlm.spawn` or
`rlm.spawn_batch`. The family is every agent under one root session. Any
agent can message any family member by name, id, or `parent/child` path, or
all members with `all`. A message between two subagents also shows in the
root chat as a relay row. The roster note gives the latest report or progress
of each agent.

In the chat:

- `@name message` sends a message to a family agent. The reply comes back as
  `name -> you`.
- `/agents` lists the agents of this session: status, depth, model, and work.
- In the agents view, Esc clears the search, then returns to the chat the
  view was opened from. Ctrl+D with an empty search, or a double Ctrl+C,
  exits.

Settings: [settings.md](settings.md#agents-and-providers).

## Providers

`eukhe provider caps [provider]` shows what each provider can do beside
chat: count tokens, list models, embeddings, images, usage, web search and
compaction. It sends no request. `eukhe provider models <provider>` asks the
provider for its model list: ID, name, context and maximum output.

## Session state

Each session keeps a state tree: its conversations, tasks, jobs and
documents. `eukhe state [agent]` shows it. `--since <cursor>` shows the
changes after a cursor. `--follow` shows new changes until Ctrl+C.
`eukhe state rewind-plan <cursor>` shows what a rewind to the cursor stops,
starts and restores.
