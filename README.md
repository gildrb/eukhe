# eukhe

eukhe is a coding agent with one endless chat as its memory.

eukhe is a fork of [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent)
by Prime Intellect. It is not affiliated with Prime Intellect, Victor Taelin or Earendil.
Upstream remote: `upstream`. See [Attribution](#attribution).

## Changes from Prime Agent

- Memory: the [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449)
  chat log is the default memory. Each root turn starts from the chat view.
  The daemon owns the log and runs the compactor. See [Memory](#memory).
- Agents: every agent can message every agent of its family. See
  [Agents](#agents).
- Name: binary `eukhe`, crates `eukhe-*`, env vars `EUKHE_*`, state in
  `~/.eukhe`. eukhe and Prime Agent can run on one machine. They do not share
  state.
- Install: Nix flake and Home Manager module. No install scripts.
- Update: through Nix. `eukhe update` does not download.
- Prompt cache: breakpoints on text blocks.

## Install

Run once:

```sh
nix run github:gildrb/eukhe
```

Home Manager:

```nix
{
  inputs.eukhe.url = "github:gildrb/eukhe";

  # in the home configuration:
  imports = [ inputs.eukhe.homeManagerModules.default ];
  programs.eukhe = {
    enable = true;
    daemon.enable = true; # Linux: systemd user service
    settings.telemetry.enabled = false;
  };
}
```

`programs.eukhe.settings` is copied to `~/.eukhe/settings.json` at each
activation. `programs.eukhe.files` links files into `~/.eukhe`.

Build from source:

```sh
cargo build --release --locked -p eukhe-cli
```

## Usage

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
eukhe doctor [--fix]       # check or repair the daemon
eukhe shutdown [--force]   # stop all agents and the daemon
```

Each daemon reports its build: `<version>+<commit>`, with `.dirty` for a
modified tree. After an upgrade or a rebuild, the next `eukhe` start replaces
an idle daemon of another build, or a pre-rename `prime-agent` daemon on the
socket. A daemon with active work keeps running until the next idle start;
`eukhe shutdown` restarts it sooner. Sessions persist and reattach.

> [!WARNING]
> eukhe runs model-generated Python and shell commands with your user
> permissions. It is not a sandbox. Use trusted repositories only.

## Memory

The chat lives in `~/.eukhe/chat/`. It is one append-only log. Each message
has a kind: `user`, `talk`, `tool`, `echo`, or `work` (a subagent or
background report). The compactor writes one-line summaries into a binary
tree over the log. A summary has a 512-byte target; a longer one is tried
again while it gets shorter, up to 5 times, and the shortest is cut to 512
bytes. A failed summary is tried again at the next message, and every 10 s
while a turn waits for it; its third failure keeps its message cut to 512
bytes as the line. An idle chat makes no model call. A turn waits for the
view's summaries at most `memory.settleTimeoutMs`.

The view is the context each root turn starts from. When the view passes
128 KB, one batch merges it down to 64 KB. The view is saved to `view.json`
on each change, so the prompt cache stays valid across restarts. A cache mark
sits on the last whole block of 4 lines. Compaction calls use their own view
of 16 KB to 32 KB.

|Command|Effect|
|---|---|
|`/memory`|Show the status and every view line|
|`/memory zoom <id> <n>`|Show the messages or summaries of node `<id>+<n>`|
|`/memory-model`|Select the compaction model|

The status bar shows the view size as `mem N/128K`. Each compactor change
shows as a `memory:` row. The summary text shows at full detail only.

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

Settings in `~/.eukhe/settings.json`:

|Key|Default|Effect|
|---|---|---|
|`subagentMaxConcurrency`|`32`|Subagents that run at one time; `0` is no limit|
|`subagentStallMs`|`600000`|A subagent with no progress for this long is stopped and reported stalled; `0` takes the default|
|`subagentDefaultModel`|parent model|Model of a subagent spawned without `model`|
|`rlmMaxDepth`|`2`|Maximum subagent depth (global only)|
|`providerMaxInFlight`|none|`{"<provider>": n}`: model requests at one time per provider; `0` is no limit (global only)|
|`providerMaxQueued`|`64`|Requests that wait per provider; the next one fails (global only)|
|`retry.provider.streamIdleTimeoutMs`|`300000`|A model stream with no event for this long fails as stalled and retries; `0` is no limit|
|`memory.settleTimeoutMs`|`20000`|How long a turn waits for the memory's summaries; then a line not summarized yet shows its message cut to 512 bytes; `0` takes the default|
|`maxToolRounds`|`250`|Tool rounds one turn may make; at the cap the turn ends as failed; `0` takes the default|

The daemon applies the provider limits to all sessions together. The roster
shows a waiting request as `queued` and a running one as `generating`.

## Develop

```sh
make check   # fmt, clippy, tests
```

Run tests with a clean environment. Inherited `EUKHE_*` variables point
test daemons at real state:

```sh
env -i HOME="$HOME" PATH="$PATH" USER="$USER" LANG="$LANG" cargo test --workspace
```

## Attribution

- [Prime Intellect](https://www.primeintellect.ai): Prime Agent, the code
  base of eukhe. Copyright (c) 2025-2026 Prime Intellect Ltd., MIT.
- [Mario Zechner](https://github.com/badlogic): the original code of the
  Prime Agent TypeScript product, which eukhe ports. Copyright (c) 2025 Mario
  Zechner, MIT.
- [Victor Taelin](https://github.com/VictorTaelin): the chat memory design,
  [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449),
  and its predecessor [OptMem](https://github.com/VictorTaelin/OptMem). The
  memory prompts come from the OptChat specification.

## License

MIT. See [LICENSE](LICENSE). Prime Agent copyright stays with Prime
Intellect Ltd. and Mario Zechner.
