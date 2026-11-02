# eukhe

Coding agent with a memory of all things. εὐχή: a wish, a prayer.

## Install

```sh
curl -fsSL https://eukhe.com/install | sh  # macOS (Apple Silicon), Linux (x64, arm64); rerun to update
eukhe kernel install                       # one time: the Python kernel (needs uv)
```

- Nix: `nix run github:gildrb/eukhe`
- Home Manager: `programs.eukhe.enable = true;` (module `inputs.eukhe.homeManagerModules.default`)
- Source: `cargo build --release --locked -p eukhe-cli`

## Use

```sh
cd /path/to/project
eukhe            # start; run /login at the first start
eukhe agents     # find and open sessions
eukhe gateway    # chat with the session from Signal on your phone
eukhe dashboard  # open the session in a browser
```

`eukhe --help` lists the commands. In a session, type `/` for the slash commands.

## Memory

> γραμμάτων τε συνθέσεις, μνήμην ἁπάντων, μουσομήτορ᾽ ἐργάνην.
> And the joining of letters: memory of all things, the Muses' mother, a worker. (Aeschylus, Prometheus Bound 460-461)

- Each session is its own thread with its own append-only log. Nothing is deleted.
- A turn sends the newest messages verbatim and a view of the older ones: one-line summaries the agent can open back to the full text.
- No session reads the memory of another. `/memory` shows it.
- Design: Victor Taelin's [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449).

## Agents

- The agent starts subagents from its Python REPL and works with them as a tree.
- An agent sends messages only to its parent and its own children.
- `@name message`: send a message to an agent. `/agents`: list them.
- `gateway.rootHeartbeat`: one persistent `root` session for the phone, woken on a schedule.

## Laws

- The rules of eukhe are [Bend 2](https://github.com/bendlang/bend) models, compiled into the binary. `LAWS.bend` states their laws; `PROOF.bend` proves them. See [spec/README.md](spec/README.md).

```sh
bend PROOF.bend  # check every law
```

## Limitations

- Runs model-written Python and shell with your permissions. No sandbox. Trusted repositories only.
- No Windows.

## Attribution

- Fork of Prime Intellect's [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent), which ports Mario Zechner's TypeScript agent.
- Chat memory design: Victor Taelin's OptChat and [OptMem](https://github.com/VictorTaelin/OptMem).
- Not affiliated with Prime Intellect, Victor Taelin or Earendil.
- Made by [Gil Rodrigues](https://gildrb.com). Notices: [THIRD-PARTY-NOTICES](THIRD-PARTY-NOTICES).

## License

MIT. See [LICENSE](LICENSE).
