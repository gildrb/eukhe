# eukhe

eukhe (Greek εὐχή: a wish, a prayer) is a coding agent with one endless chat
as its memory.

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
- Install: Nix flake and Home Manager module, or a GitHub release (mise).
  No install scripts.
- Update: through Nix or mise. `eukhe update` does not download.
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

mise (the newest GitHub release; eukhe tags are `eukhe-v<version>`, the
repository also holds the upstream `v*` tags):

```toml
[tools]
"github:gildrb/eukhe" = { version = "latest", version_prefix = "eukhe-v" }
```

Build from source:

```sh
cargo build --release --locked -p eukhe-cli
```

A source build reports `<series>-dev` (`eukhe --version`, for example
`0.10.0-dev`); only a release reports a release version.

### Releases

Every commit of `main` that passes CI (`.github/workflows/ci.yml`: the
laws, the tests, the deny gate) is released once, by
`.github/workflows/eukhe-release.yml`. The version is the next patch of
the series in `Cargo.toml` (`[workspace.package] version = "X.Y.0"`): 1 +
the highest patch among the tags `eukhe-vX.Y.P`, or 0 for the first
release of a series. The release is tagged `eukhe-v<version>`, titled
`Eukhe v<version>`, marked latest, and pinned for the flake in
`nix/release.json`. To start a new series, set the workspace version to
the next `X.Y.0` (for example `0.11.0` or `1.0.0`). A workspace version
that is no `X.Y.0`, or a tag of a newer series, stops the release.
`scripts/release/next_version.py` computes the version; its rule is the
model `bend/semver.bend`, whose laws (`laws/release.bend`, section R1)
`PROOF.bend` proves, and `scripts/release/test_next_version.py` runs the
script and the model on the same cases.

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
eukhe state [agent]        # show the session state tree
eukhe provider caps        # list provider capabilities; no network
eukhe provider models <p>  # list the models of provider <p>
eukhe tiny-models          # list or download local models
eukhe doctor [--fix]       # check or repair the daemon
eukhe shutdown [--force]   # stop all agents and the daemon
```

Each daemon reports its build: `<version>+<commit>`, plus `.dirty.<hash>`
(a hash of the changes) when the sources differ from the commit, or
`<version>+src.<hash>` (a hash of the sources) when no commit is known, so
two builds of other sources never share a build. After an upgrade or a
rebuild, the next `eukhe` start replaces an idle daemon of another build,
or a pre-rename `prime-agent` daemon on the socket. A daemon with active
work keeps running until the next idle start; `eukhe shutdown` restarts it
sooner. Sessions persist and reattach.

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
|`compaction.keepRecentTokens`|`40000`|Tokens of recent context that compaction keeps; capped per model at half the size where compaction starts|
|`compaction.providerTokenCount`|`false`|Ask the provider's own token counter before the compaction check; one more request per generation; a provider with no counter uses the local estimate|
|`retry.provider.streamRepeatLimit`|`64`|A stream whose last this many lines repeat one line, or a block of up to a quarter of them, stops and retries; `0` takes the default|
|`directors.stackCap`|`8`|Reminders and forced calls that the Director stack holds; `0` takes the default|
|`directors.maxSteps`|`200`|Continuations that one run may make; a new user input resets the count; `0` takes the default|

The daemon applies the provider limits to all sessions together. The roster
shows a waiting request as `queued` and a running one as `generating`.

## Settings files

Each setting is a console variable (cvar). Its id is the dotted key in
`settings.json`. The value comes from layers. A higher layer wins:

1. The default.
2. `~/.eukhe/settings.json`, then the project `.eukhe/settings.json`.
3. `~/.eukhe/config.cfg`, then the project `.eukhe/config.cfg`.
4. The agent profile: `~/.eukhe/agents/main.cfg` for the root session;
   `~/.eukhe/subagent.cfg`, then `~/.eukhe/agents/<name>.cfg`, for a
   subagent.
5. The sets of the agent while it runs (`/set`, `/toggle`).

The project files obey project trust. A project file never sets a global
setting.

A cfg file has one command list on each line. A `;` separates two
commands. Double quotes keep spaces. `#` starts a comment.

```sh
set compaction.keepRecentTokens 60000
toggle titles.generate
alias quiet "set terminal.streamPace.lag 0; set titles.generate false"
```

Key binds are in `~/.eukhe/binds.cfg`. The first bind of a key wins. User
binds come before the defaults. An empty bind removes a default bind:

```sh
bind ctrl+e "action app.tools.expand"
bind ctrl+o ""
```

|Key|Action|Effect|
|---|---|---|
|Shift+Tab|`app.thinking.cycleForward`|Set the next thinking level that the model offers; after the last level, go to the first|
|Shift+Alt+Tab|`app.thinking.cycleBackward`|Set the previous thinking level that the model offers; before the first level, go to the last|

These keys operate at the prompt only. An open menu or picker uses Shift+Tab
first (the settings menu goes to the previous tab). A model with fewer than
two levels keeps its level, and the status row shows `Current model offers no
other thinking level`. `/effort` shows the levels that the model offers and
marks the current level.

|Command|Effect|
|---|---|
|`/set [--global] <id> <value>`|Set a value for this session; `--global` writes it to `~/.eukhe/config.cfg`|
|`/toggle <id>`|Flip a true/false setting|
|`/alias <name> "<commands>"`|Make `<name>` run the commands|
|`/cvar`|Show the settings that clients see|
|`/cvar save`|Write the session's sets to `~/.eukhe/agents/<name>.cfg`|
|`/reload`|Read `binds.cfg` again|

More settings:

|Key|Default|Effect|
|---|---|---|
|`shell.autoEffects`|`["read"]`|Effects of a `bash` tool step that run without approval: `read`, `write`, `exec`, `net`; a different step asks the attached client; no answer is a denial (no agent or untrusted project can set it)|
|`kernelTransport`|none|Run the Python kernel through a wrapper, e.g. `{"argvPrefix":["docker","exec","-i","box"],"pathMap":[{"sandbox":"/work","host":"/home/me/project"}]}`; `"command":"shell"` for ssh; none runs it as a local process (no agent or untrusted project can set it)|
|`ssh.hosts`|`[]`|Hosts that `ssh://host/path` reads can go to, as written in the URL (`box` or `user@box`); reads only, through your `ssh` and `~/.ssh/config` (global only)|
|`titles.generate`|`true`|Make a session title from the first message with the `tiny` role; a name you gave stays|
|`terminal.streamPace.minChars`|`2`|Fewest streamed characters that one frame shows; `0` reads as 1|
|`terminal.streamPace.lag`|`3`|How far the screen stays behind the stream: each frame shows the backlog divided by `1 + lag`|
|`terminal.showSpeed`|`true`|Show the generation speed on the status line: `prefill <elapsed>s` (or `prefill p/n tokens` from a llama.cpp server), `decode N tok/s`, then `prefill X tok/s (TTFT Ys) · decode Z tok/s` after the reply|

## Local models

eukhe can run small models on your computer for titles, judgments,
translation, speech and dictation. eukhe does not download them
automatically:

```sh
eukhe tiny-models                       # list models and their state
eukhe tiny-models download lfm2.5-230m  # download one model, or all
eukhe translate de hello                # translate text to German
eukhe say "hello" [--out a.wav]         # speak text, or write a WAV file
eukhe transcribe a.wav                  # write the text of a WAV file
```

The models are `lfm2.5-230m` and `lfm2.5-350m` (text), `whisper-base` and
`whisper-small` (speech to text), and `kokoro` (text to speech). They go in
`~/.eukhe/models/tiny/`. The download checks the size and the sha256 of each
file. The models need ONNX Runtime 1.24 or newer. The Nix package sets
`ORT_DYLIB_PATH` to the nixpkgs library; your own `ORT_DYLIB_PATH` wins.

Each task has a role. A role uses its model, then its fallback list. It uses
the first model that is available: a local model must be installed, and a
provider model must be the session's model. If no model is available, the
task fails.

|Role|Task|Default order|
|---|---|---|
|`tiny`|Session titles|`local/lfm2.5-230m`, `local/lfm2.5-350m`, the session's model|
|`judge`|Typed judgments|Same as `tiny`|
|`translate`|Translation|Same as `tiny`|
|`speech`|Text to speech|`local/kokoro`|
|`dictation`|Speech to text|`local/whisper-base`, `local/whisper-small`|

|Key|Default|Effect|
|---|---|---|
|`modelRoles.<role>`|none|The model of the role: `local/<id>` or `provider/model`|
|`retry.fallbackChains.<role>`|default order|List of models after `modelRoles.<role>`; `[]` uses only `modelRoles.<role>`|
|`tts.localVoice`|`af_heart`|Voice of `eukhe say`; `--voice` overrides it|
|`stt.enabled`|`false`|Dictation into the editor with the `dictation` role|
|`providers.tinyRuntimeLibrary`|none|Path of the ONNX Runtime library; none uses `ORT_DYLIB_PATH` (global only)|

For dictation, set `stt.enabled true`, then bind `action app.stt.pushToTalk`
(hold the key) or `action app.stt.toggle` in `binds.cfg`. Both are not bound
by default. Recording uses the first of `pw-record`, `parec` and `arecord`
on `PATH` (macOS: `sox`, then `ffmpeg`).

## Directors

After each final answer, a stack of Directors can continue the run: the
goal, the autonomous run, reminders and forced tool calls.

|Command|Effect|
|---|---|
|`/remind <text>`|Put `<text>` first in the next continuation; a reminder does not start a continuation|
|`/force <tool> [--tries <n>]`|Make the next requests call `<tool>` until a response calls it; after `n` misses (default `1`) the generation fails|

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

## Dashboard

`eukhe dashboard` serves a web app for the CLI session: chat, live turn
activity, session controls, saved sessions and the chat memory. It listens
on `127.0.0.1` only. To use it on a phone, run it under poros
(`poros eukhe dashboard`), or put `tailscale serve` in front and add
`--allow-host <tailnet name>`. See [docs/dashboard.md](docs/dashboard.md).

## Develop

```sh
nix develop  # Rust toolchain, uv, git, ONNX Runtime (sets ORT_DYLIB_PATH)
make check   # fmt, clippy, tests
make dashboard-ui  # Node: rebuild the dashboard web app into crates/eukhe-dashboard/web (commit it)
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
