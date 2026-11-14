# Eukhe (εὐχή)

Eukhe (εὐχή: a wish, a prayer) is a harness and embeddable core for agents that work toward a goal, within limits, until the specified checks pass.

- Goal: the work to be done.
- Limits: money, time, tokens. Each model request and tool call reserves its worst case first; spend passes a limit only when a provider reports more than the reserve.
- Checks: commands that decide when the work is done, such as `cargo test` or `bend PROOF.bend --verdict`.
- Report: the agent's final answer, and each check's verdict with its output.

[Why?](PHILOSOPHY.md)

## Install

```sh
curl -fsSL https://eukhe.com/install | sh  # macOS (Apple Silicon), Linux (x64, arm64)
```

- Nix: `nix run github:gildrb/eukhe`
- Home Manager: `programs.eukhe.enable = true;` (module `inputs.eukhe.homeManagerModules.default`)

## Use

```sh
cd /path/to/project
eukhe         # start; /login on the first run
eukhe agents  # find and open sessions
eukhe update  # install the latest release
eukhe --help  # all commands
```

Eukhe follows your project's `AGENTS.md`. Type `/` in a session for the slash commands.

## Capabilities

- Budgets: `/budget set cost=5 time=2h` gives a task and its subagents $5 and 2 hours. Budgets cover money, tokens, tool calls, model requests and time. The agent is told when a budget runs low and still gives a final answer when it runs out.
- Checks: `/accept cmd cargo test` makes the task done only when `cargo test`, run by Eukhe on the final result, passes; the result is labelled `checks passed, unconfined`. Only the task's owner sets checks. A failed check returns to the agent with its output.
- Loops: `/loop 20 --until 'cargo test' fix the failing tests` resends the prompt until the command passes or 20 repeats have run.
- Crash recovery: a session killed with `kill -9` reopens from its log. A tool call, job or subagent of unknown outcome is reported interrupted and is not run again; `eukhe effects` lists them.
- Memory: a long session keeps every message. Older ones become summaries the agent can reopen.
- Python: a REPL for the agent that keeps its state between calls (variables up to 16 MiB each survive a compaction or restart) and can start subagents.
- Background sessions: a daemon runs them. The terminal, `eukhe dashboard` (browser) and `eukhe gateway` (Signal) attach to the same sessions.
- Embedding: [`eukhe-sdk`](crates/eukhe-sdk/) runs sessions inside a Rust program, and [`eukhe-client`](crates/eukhe-client/) connects one to the daemon. Rust only, not on crates.io, API unstable.

## Limitations

```
- No sandbox: model-written code runs with the user's permissions and can change check inputs and the session's files.
- A model request cut by a crash is not sent again (unless its provider declares lasting deduplication; no shipped provider does): it is reported interrupted, its reserved spend stays counted until its usage is known, and the run continues with a new request.
- A limit left unset is unlimited.
- No Windows.
- A passing check can be gamed, for example by a hard-coded answer or an edited test. Eukhe refuses the agent's changes to the check list and fails a check whose `--protect` file changed.
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
