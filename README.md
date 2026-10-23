# eukhe

eukhe (Greek εὐχή: a wish, a prayer): a coding agent whose memory is one endless chat log shared by all sessions (no empty new session, no compaction dropping the start); each turn starts from a compact view of the full log. Fork of [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent) by Prime Intellect; not affiliated with Prime Intellect, Victor Taelin or Earendil ([Attribution](#attribution)).

## Install

```sh
curl -fsSL https://eukhe.com/install | sh  # macOS (Apple Silicon), Linux (x64, arm64); rerun to update
```

|Method|Command|
|---|---|
|Nix, one run|`nix run github:gildrb/eukhe`|
|Home Manager|`programs.eukhe.enable = true;` (module `inputs.eukhe.homeManagerModules.default`)|
|mise|`"github:gildrb/eukhe" = { version = "latest", version_prefix = "eukhe-v" }`|
|Source|`cargo build --release --locked -p eukhe-cli`|

`eukhe update` does not download. Details: [docs/install.md](docs/install.md).

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

- Log: `~/.eukhe/chat/`, append-only.
- The compactor writes one-line summaries into a binary tree over the log.
- Each root turn starts from the view: 64 KB to 128 KB of lines.
- `/memory`: the view. `/memory model`: compaction model and reasoning effort (the `/model` hub at the memory role).

Design: Victor Taelin's [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449). Details: [docs/memory.md](docs/memory.md).

## Agents

- `rlm.spawn` in the agent's Python REPL starts subagents.
- `@name message`: message a family agent. `/agents`: list the session's agents.

## Dynamic workflows

- `/dynamic-workflow <request>`: the agent writes and runs one orchestration script that starts many subagents (fan-out, pipelines, phases).
- `--size small|medium|large`: how many agents; `/workflows size` sets the default. `/workflows`: phases, agents, log per run.

Details: [docs/workflows.md](docs/workflows.md).

## Phone and browser

- `eukhe gateway`: Signal to the CLI session ([docs/gateway.md](docs/gateway.md)).
- `eukhe dashboard`: the session on `127.0.0.1`; phone: `poros eukhe dashboard` ([docs/dashboard.md](docs/dashboard.md)).

## References

|File|Content|
|---|---|
|[docs/install.md](docs/install.md)|Installer, Nix, Home Manager, mise, source build, daemon versions|
|[docs/usage.md](docs/usage.md)|Commands, agents, providers, session state|
|[docs/settings.md](docs/settings.md)|Settings files, key binds, all settings, Directors|
|[docs/workflows.md](docs/workflows.md)|Dynamic workflows: sizes, script API, resume, limits|
|[docs/memory.md](docs/memory.md)|Chat memory: use, rules, Bend model, proofs|
|[docs/local-models.md](docs/local-models.md)|Local models: titles, translation, speech, dictation|
|[docs/gateway.md](docs/gateway.md)|Signal gateway|
|[docs/dashboard.md](docs/dashboard.md)|Web dashboard|
|[docs/develop.md](docs/develop.md)|Build, test, releases|

## Limitations

- Runs model-generated Python and shell with your user permissions; no sandbox. Trusted repositories only.
- macOS (Apple Silicon), Linux (x64, arm64). No Windows.
- Kernel needs uv; chat memory needs git; the Nix package supplies both.
- Local models need ONNX Runtime 1.24+.

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
