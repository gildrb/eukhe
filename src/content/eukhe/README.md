# Eukhe

The harness for the AGI era.

Eukhe is εὐχή, Greek for wish. You wish how the agent should do the work, and Eukhe gets it done that way.

You write the wish as rules in `AGENTS.md`, as a goal and as commands that must pass. When one of those commands fails, Eukhe gives its output to the agent and runs another turn, and it repeats this until every command passes or the run reaches a limit. A session is an append-only log on disk, so it survives a crash and `eukhe --continue` reopens it.

[spec/](spec/README.md) numbers what Eukhe's session log, memory, subagents and tool calls must do. A law is a theorem that the core, the part of Eukhe written in [Bend](https://bend-lang.com), meets one of those requirements. In a checkout, `bend PROOF.bend` checks the proof of every law, and the checked core is the code compiled into the binary you install.

The `eukhe` command runs a coding agent on this core in your terminal. The `eukhe-sdk` Rust crate runs sessions on it inside your own process.

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
eukhe -p "task"  # one run, no UI; exits 0 only if the agent answered
eukhe agents     # find and open sessions
eukhe gateway    # chat with the session from Signal on your phone
eukhe dashboard  # open the session in a browser
```

`eukhe --help` lists the commands. In a session, type `/` for the slash commands.

## Wish

- Eukhe reads `AGENTS.md` in your project and puts it in the system prompt.
- `eukhe --goal "objective"` starts a session that keeps running turns until the agent marks the goal complete or `--goal-token-budget` tokens are used.
- `eukhe --autonomous --autonomous-gate "cargo test"` runs `cargo test` after each turn. If it fails, Eukhe gives the agent its output and runs another turn. The run stops when the command passes or a limit is reached; `eukhe --help` lists the limits and their defaults.

## Laws

- The tables in [spec/README.md](spec/README.md) number the requirements and name the laws of each. A spec file such as [`spec/durable/log.bend`](spec/durable/log.bend) restates a requirement in Bend. It calls none of the shipped code, so a law compares two separately written definitions.
- A law is a theorem that the core does what a spec file says, and `PROOF.bend` holds a proof of every law. `LAWS.lock` holds a hash of each law and spec file, and the repository's pre-push hook rejects a push that changes one without the lock.
- Rust does the IO and calls the compiled core wherever a requirement has a law.

```sh
bend PROOF.bend  # check the proof of every law
```

The `bend` command comes from [bendlang/bend](https://github.com/bendlang/bend).

## SDK

- [`eukhe-sdk`](crates/eukhe-sdk/) is a Rust crate that runs sessions inside your process. Its main calls are `open_session`, `prompt` and `watch`.
- [`eukhe-client`](crates/eukhe-client/) is a Rust crate that connects to the Eukhe daemon (`eukhe --mode daemon`) over its socket. The terminal UI and the web dashboard use it.
- A program in any language starts `eukhe --mode <json|rpc|acp>` and talks to it over stdio.

## Components

- [Durable](spec/durable/) syncs every write of the session log to disk before acknowledging it. A resumed session keeps every checkpoint and has no task left running.
- [Memory](spec/memory/) never deletes a message. Each request to the model contains the newest messages in full and a one-line summary of each older one, and the agent can read the full text of any summarized message.
- [RLM](spec/rlm/) (recursive language model) gives the agent a Python REPL in which the conversation so far is a variable. The agent starts a subagent there with a function call, and Eukhe refuses a call that gives no reason.
- [Autoresearch](spec/autoresearch/) improves a number you can measure on your code, such as its speed or size. It runs the benchmark after each change and keeps the change only if the number improved.
- Loop is the code behind `--autonomous` and `--goal`. It has no requirements, spec files or laws yet.
- Planned and not built: hard budgets, verified completion, exactly-once effects, capability security, replayable record, orchestration at scale, stable SDK contract.
- [spec/README.md](spec/README.md) also lists requirements and laws for tool calls, the tree of agents and subagents, settings and themes.

## Limitations

- Runs model-written Python and shell with your permissions. No sandbox. Trusted repositories only.
- No Windows.
- The SDK crates (`eukhe-sdk`, `eukhe-client`) are Rust only and are not on crates.io. Their API may change with any release.
- The proofs cover the Bend core and say nothing about what the model writes. The Bend compiler, the C shim that links the core into the binary and the Rust IO are trusted without proof ([spec/README.md](spec/README.md#trust)).

## Credits

- Fork of Prime Intellect's [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent), built on Mario Zechner's [pi](https://github.com/earendil-works/pi).
- Victor Taelin: the chat memory design, OptChat, and its predecessor [OptMem](https://github.com/VictorTaelin/OptMem).
- [oh-my-pi](https://github.com/can1357/oh-my-pi): the edit tools and the harness design.
- Not affiliated with Prime Intellect, Victor Taelin or Earendil.
- Made by [Gil Rodrigues](https://gildrb.com). Notices: [THIRD-PARTY-NOTICES](THIRD-PARTY-NOTICES).

## License

MIT. See [LICENSE](LICENSE).
