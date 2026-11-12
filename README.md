# Eukhe

Eukhe (εὐχή, Greek for wish) is an agent harness: it runs a model toward a goal, within limits, until checks pass.

- Goal: the work to be done.
- Limits: money, time, tokens. Never exceeded.
- Checks: commands that decide when the work is done, such as `cargo test` or `bend PROOF.bend --verdict`.
- Report: what was done, and which checks passed.

[Why](PHILOSOPHY.md).

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

## Budgets

- `/budget set cost=5 time=2h`: the task and all its subagents spend at most $5 and finish within 2 hours.
- Never exceeded, in money, tokens, tool calls, model requests or time.
- When the budget runs low the agent is told. When it runs out the agent still gives its final answer.

## Verified completion

- `/accept cmd cargo test`: the task counts as done only when `cargo test`, run by Eukhe on the final result, passes.
- The agent can't set, change or skip a check.
- Each result is labelled verified, failed or unverified. A failed check goes back to the agent with its output.

## Crash safety

- Kill Eukhe at any point, even with `kill -9`, then reopen the session: it picks up where it stopped.
- No effect runs twice, and nothing is reported done that didn't run.

## Loop

- `/loop 20 --until 'cargo test' fix the failing tests`: the prompt is sent again after every turn until `cargo test` passes, 20 repeats have run, or you stop it.
- Only the command's exit code decides. Esc pauses the loop, and it survives a restart.

## Components

- `eukhe`: the coding agent in your terminal.
- Daemon: runs sessions in the background. `eukhe` starts it, and the terminal, dashboard and gateway attach to it.
- Dashboard: `eukhe dashboard` opens your sessions in a browser.
- Gateway: `eukhe gateway` lets you chat with a session from Signal on your phone.
- [`eukhe-sdk`](crates/eukhe-sdk/): runs sessions inside your Rust program.
- [`eukhe-client`](crates/eukhe-client/): connects your Rust program to the daemon's sessions.
- `python` tool: a Python REPL for the agent that keeps its state between calls.
- Memory: a long session never loses a message. Older ones become one-line summaries the agent can open back up.
- RLM: the agent works over the whole conversation from Python and starts subagents from code.
- Autoresearch: `/autoresearch <goal>` improves a number you can measure, such as speed or size, and keeps only changes the benchmark confirms.

## Limitations

- Runs model-written code with your permissions. No sandbox. Trusted repositories only.
- No Windows.
- Checks judge the final result, not how the agent reached it.
- The SDK crates are Rust only and not on crates.io. Their API may change with any release.

## Credits

- Fork of Prime Intellect's [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent), built on Mario Zechner's [pi](https://github.com/earendil-works/pi).
- Victor Taelin: the chat memory design, OptChat, and its predecessor [OptMem](https://github.com/VictorTaelin/OptMem).
- [oh-my-pi](https://github.com/can1357/oh-my-pi): the edit tools, the tokenizers and the harness design.
- Sander Land's [ctok](https://github.com/sanderland/ctok): the Claude tokenizer vocabulary.
- Not affiliated with Prime Intellect, Victor Taelin or Earendil.
- Made by [Gil Rodrigues](https://gildrb.com). Notices: [THIRD-PARTY-NOTICES](THIRD-PARTY-NOTICES).

## License

MIT. See [LICENSE](LICENSE).
