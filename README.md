# Eukhe

The harness for the AGI era.

You give Eukhe the goal and the limits: cost, time, quota. It gets there within them and reports truthfully what it did. [PHILOSOPHY.md](PHILOSOPHY.md) explains why.

## Install

```sh
curl -fsSL https://eukhe.com/install | sh  # macOS (Apple Silicon), Linux (x64, arm64); rerun to update
```

- Nix: `nix run github:gildrb/eukhe`
- Home Manager: `programs.eukhe.enable = true;` (module `inputs.eukhe.homeManagerModules.default`)
- Source: `cargo build --release --locked -p eukhe-cli`
- The `python` tool needs no install step. Its first start fetches Eukhe's pinned CPython 3.14.10 (about 50 MB, once).

## Use

```sh
cd /path/to/project
eukhe                                         # start; run /login at the first start
eukhe --budget-cost 5 --budget-time 2h        # a session that spends at most $5 and ends within 2 hours
eukhe -p "task" --accept-cmd "cargo test"     # one run, no UI; exits 0 only if cargo test passes at the end
eukhe agents                                  # find and open sessions
eukhe gateway                                 # chat with the session from Signal on your phone
eukhe dashboard                               # open the session in a browser
```

Eukhe puts the `AGENTS.md` of your project in the system prompt. `eukhe --help` lists the commands. In a session, type `/` for the slash commands.

## Budgets

- A budget limits what a task and every subagent it starts may spend: money, tokens, tool calls, model requests, and a deadline (`--budget-*`, `/budget`, `eukhe budget set|add`). It is never exceeded.
- Each model request and tool call reserves its worst case before it runs, with tokens counted by the model's own tokenizer, and is charged what it actually used when it returns. A request that does not fit is sent with a smaller output cap or not at all.
- When the budget runs low the agent is told. When nothing more fits, it still gets to write its final answer. `eukhe budget audit` replays the ledger and checks every number.

## Verified completion

- "Done" is a claim. You set acceptance checks (`--accept-cmd`, `--accept-judge`, `/accept`, `spawn(accept=...)` for a subagent), and Eukhe runs them itself on the final state. The agent cannot set, change or skip a check.
- An independent judge, one model request with no tools and no transcript, reads your messages and decides whether the final state meets what you ask for now. It never sees what the agent wrote.
- The result is labelled verified, failed or unverified. A failed check goes back to the agent with its output, at most 3 times in a row, and a run with no checks is never labelled verified.

## Exactly-once effects

- Every effect (a tool call, a model request, a file write, a background job, a subagent, a scheduled task, a queued message) is written to a journal before it happens.
- After a crash or `kill -9`, a call that may change something never runs twice, and nothing is reported done that did not run. A model request is resent under the same `Idempotency-Key`, at most 2 more times.
- `eukhe effects` lists the interrupted effects whose outcome is unknown, and `eukhe effects resolve <id> ran` (or `not-run`) settles one.

## Loop

- `/loop 20 --until 'cargo test' fix the failing tests` sends the prompt again after every turn until `cargo test` passes, 20 turns have run, or you stop it. Esc pauses it and `/loop --stop` ends it.
- Only the command's exit code decides. A command that times out or cannot start ends the loop as failed, never as done. The loop survives a restart without sending a prompt twice.
- `eukhe --goal "objective"` and `eukhe --autonomous --autonomous-gate "cargo test"` keep working toward an objective or a passing command; their limits are limits on the session's budget.

## Laws

- [spec/README.md](spec/README.md) numbers what each part of Eukhe must do. A spec file restates a requirement in Bend without calling the shipped code, and a law is a theorem that the core meets it.
- The core is written in [Bend](https://bend-lang.com) and compiled into the binary you install. Rust does the IO and calls the core wherever a requirement has a law.
- `bend PROOF.bend` checks the proof of every law. `LAWS.lock` holds a hash of each law and spec file, and the pre-push hook rejects a push that changes one without the lock.

## SDK

- In your process: the [`eukhe-sdk`](crates/eukhe-sdk/) Rust crate runs sessions inside your program (`open_session`, `prompt`, `watch`).
- Through the daemon: the [`eukhe-client`](crates/eukhe-client/) Rust crate connects to `eukhe --mode daemon` over its socket, as the terminal UI and the dashboard do. A program in any language starts `eukhe --mode rpc`, `json` or `acp` and talks to it over stdio.
- The two have separate APIs today. One API for both, where configuration picks the place, is planned ([spec/contract/SPEC.md](spec/contract/SPEC.md)).

## Components

- [Budget](spec/budget/) keeps one ledger per task tree, so a budget you set is never exceeded.
- [Verified](spec/verified/) checks a claim of "done" against the checks you set and labels the result.
- [Once](spec/once/) keeps a journal per effect, so a restart neither repeats an effect nor reports one it can't confirm.
- [Loop](spec/loop/) repeats a prompt until a command shows its condition is met, within its bounds.
- [Durable](spec/durable/) syncs every write of the session log to disk before acknowledging it, so `eukhe --continue` reopens a session after a crash.
- [Tokens](crates/eukhe-tokens/) counts with the model's own tokenizer, and `o200k_base` for a model without a known one.
- [Memory](spec/memory/) never deletes a message. A request holds the newest messages in full and a one-line summary of each older one, which the agent can open back to the full text.
- [RLM](spec/rlm/) (recursive language model) gives the agent a Python REPL in which the conversation is a variable. It starts a subagent with a function call, and Eukhe refuses a call that gives no reason.
- [Autoresearch](spec/autoresearch/) improves a number you can measure, such as speed or size, and keeps a change only if the benchmark shows it improved.
- Planned and not built: capability security, a replayable record, orchestration at scale, a stable SDK contract ([spec/PILLARS.md](spec/PILLARS.md)).

## Limitations

- Runs model-written Python and shell with your permissions. No sandbox. Trusted repositories only.
- No Windows.
- A budget counts money from the provider's prices and tokens with each model's tokenizer. A plan's usage window ("80% of my quota") is not a budget dimension yet.
- Verified completion judges the final state, not how the agent got there. Checks the agent never sees and a review of its process for gaming are planned.
- The SDK crates are Rust only and are not on crates.io. Their API may change with any release.
- The proofs cover the Bend core and say nothing about what the model writes. The Bend compiler, the C shim that links the core into the binary and the Rust IO are trusted without proof ([spec/README.md](spec/README.md#trust)).

## Credits

- Fork of Prime Intellect's [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent), built on Mario Zechner's [pi](https://github.com/earendil-works/pi).
- Victor Taelin: the chat memory design, OptChat, and its predecessor [OptMem](https://github.com/VictorTaelin/OptMem).
- [oh-my-pi](https://github.com/can1357/oh-my-pi): the edit tools, the tokenizers and the harness design.
- Sander Land's [ctok](https://github.com/sanderland/ctok): the measured Claude tokenizer vocabulary.
- Not affiliated with Prime Intellect, Victor Taelin or Earendil.
- Made by [Gil Rodrigues](https://gildrb.com). Notices: [THIRD-PARTY-NOTICES](THIRD-PARTY-NOTICES).

## License

MIT. See [LICENSE](LICENSE).
