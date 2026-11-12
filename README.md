# Eukhe

Eukhe (εὐχή, Greek for wish) is a harness and embeddable core for agents that work toward a goal, within limits, until checks pass.

- Goal: the work to be done.
- Limits: money, time, tokens. Never exceeded.
- Checks: commands that decide when the work is done, such as `cargo test` or `bend PROOF.bend --verdict`.
- Report: what was done, and which checks passed.

[Why?](PHILOSOPHY.md).

## Install

```sh
curl -fsSL https://eukhe.com/install | sh  # macOS (Apple Silicon), Linux (x64, arm64); rerun to update
```

- Nix: `nix run github:gildrb/eukhe`
- Home Manager: `programs.eukhe.enable = true;` (module `inputs.eukhe.homeManagerModules.default`)

## Use

```sh
cd /path/to/project
eukhe         # start; /login on the first run
eukhe agents  # find and open sessions
eukhe --help  # all commands
```

Eukhe follows your project's `AGENTS.md`. Type `/` in a session for the slash commands.

## What it does

- Budgets: `/budget set cost=5 time=2h` caps a task and its subagents at $5 and 2 hours. Caps cover money, tokens, tool calls, model requests and time. The agent is told when a budget runs low and still gives a final answer when it runs out.
- Checks: `/accept cmd cargo test` makes the task done only when `cargo test`, run by Eukhe on the final result, passes. The agent cannot set, change or skip a check. A failed check returns to the agent with its output.
- Loops: `/loop 20 --until 'cargo test' fix the failing tests` resends the prompt until the command passes or 20 repeats have run.
- Crash recovery: a killed session, `kill -9` included, resumes where it stopped. No effect runs twice.
- Memory: a long session keeps every message. Older ones become summaries the agent can reopen.
- Python: a REPL for the agent that keeps its state between calls and can start subagents.
- Background sessions: a daemon runs them. The terminal, `eukhe dashboard` (browser) and `eukhe gateway` (Signal) attach to the same sessions.
- Embedding: [`eukhe-sdk`](crates/eukhe-sdk/) runs sessions inside a Rust program, and [`eukhe-client`](crates/eukhe-client/) connects one to the daemon. Rust only, not on crates.io, API unstable.

# Limitations

```
- No sandbox: model-written code runs with the user's permissions.
- No Windows.
- A passing check can be gamed, for example by a hard-coded answer. Eukhe blocks changes to the checks, not this.
```

## Credits

- Fork of Prime Intellect's [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent), built on Mario Zechner's [pi](https://github.com/earendil-works/pi).
- Victor Taelin: the chat memory design, OptChat, and its predecessor [OptMem](https://github.com/VictorTaelin/OptMem).
- [oh-my-pi](https://github.com/can1357/oh-my-pi): the edit tools, the tokenizers and the harness design.
- Sander Land's [ctok](https://github.com/sanderland/ctok): the Claude tokenizer vocabulary.
- Not affiliated with Prime Intellect, Victor Taelin or Earendil.
- Made by [Gil Rodrigues](https://gildrb.com). Notices: [THIRD-PARTY-NOTICES](THIRD-PARTY-NOTICES).

## License

MIT. See [LICENSE](LICENSE).
