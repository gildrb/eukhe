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
- No session reads the memory of another.

## Agents

- The agent starts subagents from its Python REPL. They form a tree.
- An agent sends messages only to its parent and its own children.
- `@name message`: send a message to an agent. `/agents`: list them.

## Laws

- The rules of eukhe are [Bend 2](https://github.com/bendlang/bend) models, compiled into the binary. `LAWS.bend` states their laws; `PROOF.bend` proves them. See [spec/README.md](spec/README.md).

```sh
bend PROOF.bend  # check every law
```

## Components

- eukhe-bend: the compiled Bend core; every rule with a Bend model runs here.
- eukhe-chord: contexts, cancellation, JSON. Port of [chord](https://github.com/earendil-works/pi/tree/main/packages/chord).
- eukhe-ai: providers, model catalog, streaming. Port of [pi-ai](https://github.com/earendil-works/pi/tree/main/packages/ai).
- eukhe-durable: the durable harness; a turn survives a crash. Port of [pi-durable](https://github.com/earendil-works/pi/tree/main/packages/durable).
- eukhe-docs: read, hashline edits, grep, glob. Port of [omp](https://github.com/can1357/oh-my-pi) edit.
- eukhe-shell: in-process bash with its own coreutils; `grep` on ripgrep's engine.
- Chat memory: Victor Taelin's [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449).
- eukhe-tiny: local models (text, Whisper speech to text, Kokoro text to speech) on ONNX Runtime.
- eukhe-gateway: Signal on your phone. eukhe-dashboard: the browser app.

## Limitations

- Runs model-written Python and shell with your permissions. No sandbox. Trusted repositories only.
- No Windows.

## Credits

- Fork of Prime Intellect's [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent), built on Mario Zechner's [pi](https://github.com/earendil-works/pi).
- Victor Taelin: the chat memory design, OptChat, and its predecessor [OptMem](https://github.com/VictorTaelin/OptMem).
- [oh-my-pi](https://github.com/can1357/oh-my-pi): the edit tools and the harness design.
- Not affiliated with Prime Intellect, Victor Taelin or Earendil.
- Made by [Gil Rodrigues](https://gildrb.com). Notices: [THIRD-PARTY-NOTICES](THIRD-PARTY-NOTICES).

## License

MIT. See [LICENSE](LICENSE).
