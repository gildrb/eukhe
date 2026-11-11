# Eukhe

The harness for the AGI era. εὐχή: a wish, a prayer.

Once AGI arrives, the model does the work. The harness still decides whether the work gets done your way: it keeps state through a crash, keeps the context small, loops until a condition holds, reports what happened.

Each pillar of Eukhe exists to make a stronger model more useful. A pillar is a spec turned into laws, proven with [Bend](https://bend-lang.com), so you can trust it without reading it.

Eukhe is the core to build harnesses and GUIs on, as [pi](https://github.com/earendil-works/pi) is for its forks: plug it into any product through its SDK. Its coding agent is one such product.

That's Eukhe - and you need nothing else.

## Install

```sh
curl -fsSL https://eukhe.com/install | sh  # macOS (Apple Silicon), Linux (x64, arm64); rerun to update
eukhe kernel install                       # one time: the Python kernel (needs uv); until then sessions have no ipython tool
```

- Nix: `nix run github:gildrb/eukhe`
- Home Manager: `programs.eukhe.enable = true;` (module `inputs.eukhe.homeManagerModules.default`)
- Source: `cargo build --release --locked -p eukhe-cli`

## Use

```sh
cd /path/to/project
eukhe            # start; run /login at the first start
eukhe -p "task"  # one run, no UI; exits 0 only when it answered
eukhe agents     # find and open sessions
eukhe gateway    # chat with the session from Signal on your phone
eukhe dashboard  # open the session in a browser
```

`eukhe --help` lists the commands. In a session, type `/` for the slash commands.

## Laws

- The spec: numbered requirements per pillar, written without the code ([spec/README.md](spec/README.md)).
- Laws state each requirement against a [Bend 2](https://github.com/bendlang/bend) decision core. `PROOF.bend` proves every law; `LAWS.lock` freezes them.
- The core is compiled into the binary. Rust does the IO and calls the core for every rule that has a law.

```sh
bend PROOF.bend  # check every law
```

## SDK

- In-process: [`eukhe-sdk`](crates/eukhe-sdk/) (Rust): `open_session`, `prompt`, `watch`.
- Over the daemon wire: [`eukhe-client`](crates/eukhe-client/) (Rust). Eukhe's terminal UI, web dashboard and Signal gateway are such clients.
- From any language, over stdio: `eukhe --mode json`, `--mode rpc`, `--mode acp`.

## Components

- [Durable](spec/durable/): a session is an append-only log, synced to disk at every commit; a crashed run resumes from it.
- [Memory](spec/memory/): nothing is deleted; a turn sends the newest messages verbatim and one-line summaries of the older ones, which the agent can open back to the full text.
- [RLM](spec/rlm/): context is a variable in a Python REPL and a subagent is a function call; every spawn must say why.
- [Autoresearch](spec/autoresearch/): an experiment loop that keeps only measured improvements.
- Loop (no spec of its own yet): `--autonomous` continues until its gate commands pass or a limit is reached; `--goal` keeps a session on one objective across turns.
- Planned: hard budgets, verified completion, exactly-once effects, capability security, replayable record, orchestration at scale, stable SDK contract.
- Also specified and proven: the tool-call rules, the agent tree, settings, themes ([spec/README.md](spec/README.md)).

## Limitations

- Runs model-written Python and shell with your permissions. No sandbox. Trusted repositories only.
- No Windows.
- The SDK crates are Rust only, not on crates.io, and may change with any release.
- Proven: the Bend core. Trusted, not proven: the Bend compiler, the C shim, the Rust IO ([spec/README.md](spec/README.md#trust)).

## Credits

- Fork of Prime Intellect's [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent), built on Mario Zechner's [pi](https://github.com/earendil-works/pi).
- Victor Taelin: the chat memory design, OptChat, and its predecessor [OptMem](https://github.com/VictorTaelin/OptMem).
- [oh-my-pi](https://github.com/can1357/oh-my-pi): the edit tools and the harness design.
- Not affiliated with Prime Intellect, Victor Taelin or Earendil.
- Made by [Gil Rodrigues](https://gildrb.com). Notices: [THIRD-PARTY-NOTICES](THIRD-PARTY-NOTICES).

## License

MIT. See [LICENSE](LICENSE).
