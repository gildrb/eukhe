# eukhe

eukhe (Greek εὐχή: a wish, a prayer): a coding agent whose memory is one endless chat log shared by all sessions ([Attribution](#attribution)).

## Install

```sh
curl -fsSL https://eukhe.com/install | sh  # macOS (Apple Silicon), Linux (x64, arm64); rerun to update
```

|Method|Command|
|---|---|
|Home Manager|`programs.eukhe.enable = true;` (module `inputs.eukhe.homeManagerModules.default`)|
|mise|`"github:gildrb/eukhe" = { version = "latest", version_prefix = "eukhe-v" }`|
|Source|`cargo build --release --locked -p eukhe-cli`|
- Needs uv; chat memory needs git; the Nix package supplies both.

## Use

```sh
cd /path/to/project
eukhe            # start; /login at the first start
eukhe agents     # find and open sessions
eukhe gateway    # connect Signal on your phone to the CLI session
eukhe dashboard  # open the session in a browser; on the phone: poros eukhe dashboard
```

## Memory

- One endless chat log at `~/.eukhe/chat/`, append-only, shared by all sessions.

## Privacy

- `privacy.anonymizeRemote` (default on): a remote provider gets tokens (`PERSON_1`, mapped back so tool calls run) for names, emails, home names, paths, and hashes for keys, cards, phones, IPs. Loopback providers see raw text; the log always keeps it. Domains pass as they are (the model must read them); your own domain goes in the terms.
- `privacy.terms`: your phrases become tokens. `"privacy": { "terms": ["Gil Rodrigues"] }` in `~/.eukhe/settings.json`.

## Agents

- The agent spawns subagents (`rlm.spawn` in its Python REPL) and messages any agent of its family from the prompt: `@name message`.
- `/agents`: list and open the session's agents.

## Limitations

- Runs model-generated Python and shell with your user permissions; no sandbox. Trusted repositories only.

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
