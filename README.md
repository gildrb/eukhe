# eukhe

eukhe (Greek εὐχή: a wish, a prayer) is a coding agent with one endless chat
as its memory.

eukhe is a fork of [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent)
by Prime Intellect. It is not affiliated with Prime Intellect, Victor Taelin or Earendil.
See [Attribution](#attribution).

PROBLEM: A coding agent forgets. A new session starts empty. A compaction
removes the start of a long session.

SOLUTION: eukhe keeps one chat log for all sessions. Each turn starts from a
compact view of the full log.

## Install

macOS (Apple Silicon), Linux (x64, arm64):

```sh
curl -fsSL https://eukhe.com/install | sh
```

|Method|Command|
|---|---|
|Nix, one run|`nix run github:gildrb/eukhe`|
|Home Manager|`programs.eukhe.enable = true;` (module `inputs.eukhe.homeManagerModules.default`)|
|mise|`"github:gildrb/eukhe" = { version = "latest", version_prefix = "eukhe-v" }`|
|Source|`cargo build --release --locked -p eukhe-cli`|

To update, run the install command again. `eukhe update` does not download.
Details: [docs/install.md](docs/install.md).

## Use

```sh
cd /path/to/project
eukhe            # start; run /login at the first start
eukhe agents     # find and open sessions
eukhe gateway    # connect Signal on your phone to the CLI session
eukhe dashboard  # open the session in a browser
```

All commands: [docs/usage.md](docs/usage.md).

## Memory

- The chat log is in `~/.eukhe/chat/`. It is append-only.
- The compactor writes one-line summaries into a binary tree over the log.
- Each root turn starts from the view: 64 KB to 128 KB of lines.
- `/memory` shows the view. `/memory zoom <id> <n>` opens a node.
- `/memory-model` selects the compaction model and its reasoning effort.

The design is Victor Taelin's [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449).
Details: [docs/memory.md](docs/memory.md).

## Agents

- An agent starts subagents from its Python REPL (`rlm.spawn`).
- `@name message` sends a message to a family agent.
- `/agents` lists the agents of the session.

## Phone and browser

- `eukhe gateway` connects Signal to the CLI session. See [docs/gateway.md](docs/gateway.md).
- `eukhe dashboard` serves the session on `127.0.0.1`. For a phone, run
  `poros eukhe dashboard`. See [docs/dashboard.md](docs/dashboard.md).

## Develop

```sh
nix develop        # Rust toolchain, uv, git, ONNX Runtime (sets ORT_DYLIB_PATH)
make check         # fmt, clippy, tests
make dashboard-ui  # Node: rebuild the dashboard web app into crates/eukhe-dashboard/web (commit it)
```

Run tests with a clean environment. Inherited `EUKHE_*` variables point
test daemons at real state:

```sh
env -i HOME="$HOME" PATH="$PATH" USER="$USER" LANG="$LANG" cargo test --workspace
```

## References

|File|Content|
|---|---|
|[docs/install.md](docs/install.md)|Installer, Nix, Home Manager, mise, source build, daemon versions|
|[docs/usage.md](docs/usage.md)|Commands, agents, providers, session state|
|[docs/settings.md](docs/settings.md)|Settings files, key binds, all settings, Directors|
|[docs/memory.md](docs/memory.md)|Chat memory: use, rules, Bend model, proofs|
|[docs/local-models.md](docs/local-models.md)|Local models: titles, translation, speech, dictation|
|[docs/gateway.md](docs/gateway.md)|Signal gateway|
|[docs/dashboard.md](docs/dashboard.md)|Web dashboard|

## Limitations

- eukhe runs model-generated Python and shell commands with your user
  permissions. It is not a sandbox. Use trusted repositories only.
- Platforms: macOS (Apple Silicon), Linux (x64, arm64). No Windows.
- The kernel needs uv. The chat memory needs git. The Nix package supplies both.
- Local models need ONNX Runtime 1.24 or newer.

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
