# eukhe

eukhe (Greek εὐχή: a wish, a prayer): a coding agent whose memory is one endless chat log shared by all sessions; each turn starts from a compact view of it. Fork of [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent) by Prime Intellect, not affiliated ([Attribution](#attribution)).

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

## Use

```sh
cd /path/to/project
eukhe            # start; /login at the first start
eukhe agents     # find and open sessions
eukhe gateway    # connect Signal on your phone to the CLI session
eukhe dashboard  # open the session in a browser; on the phone: poros eukhe dashboard
```

## Memory

- Log: `~/.eukhe/chat/`, append-only; the compactor writes one-line summaries into a binary tree over it.
- Each root turn starts from the view: 64 KB to 128 KB of lines.
- `/memory`: the view; `/memory model`: compaction model and reasoning effort.

Design: Victor Taelin's [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449).

## Agents

- The agent spawns subagents (`rlm.spawn` in its Python REPL) and messages any agent of its family from the prompt: `@name message`.
- `/agents`: list and open the session's agents.

## Limitations

- Runs model-generated Python and shell with your user permissions; no sandbox. Trusted repositories only.
- macOS (Apple Silicon), Linux (x64, arm64); no Windows.
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
