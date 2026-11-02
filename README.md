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

- Each session keeps an append-only log. Nothing is deleted.
- A turn sends the newest messages verbatim and a view of the older ones: one-line summaries the agent can open back to the full text.

## Agents

- `@name message`: send a message to an agent. `/agents`: list them.

## Laws

- The rules of eukhe are [Bend 2](https://github.com/bendlang/bend) models, compiled into the binary. `LAWS.bend` states their laws; `PROOF.bend` proves them. See [spec/README.md](spec/README.md).

```sh
bend PROOF.bend  # check every law
```

## Components

- [Eukhe RLM](spec/rlm/): eukhe's fork of Prime Agent's RLM; each spawn names its reason.
- [Eukhe Memory](spec/memory/): eukhe's fork of OptChat; one thread per session.
- [Eukhe Hierarchy](spec/agents/): eukhe's fork of Prime Agent's agent tree; agents message only their parent and children.

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
