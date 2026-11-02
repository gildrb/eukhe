# eukhe

Coding agent with a memory of all things. εὐχή: a wish, a prayer.

eukhe works in a Python REPL, spawns subagents, and keeps each session as its own thread: the newest turns verbatim, the older history as one-line summaries, the full log on disk.

## Install

```sh
curl -fsSL https://eukhe.com/install | sh  # macOS (Apple Silicon), Linux (x64, arm64); rerun to update
eukhe kernel install                       # one time: the Python kernel of the REPL tool (needs uv)
```

|Method|Command|
|---|---|
|Nix|`nix run github:gildrb/eukhe`|
|Home Manager|`programs.eukhe.enable = true;` (module `inputs.eukhe.homeManagerModules.default`)|
|mise|`"github:gildrb/eukhe" = { version = "latest", version_prefix = "eukhe-v" }`|
|Source|`cargo build --release --locked -p eukhe-cli`|

- The chat memory needs git; `eukhe kernel install` needs uv. The Nix package supplies both.
- Nothing downloads on its own: only `eukhe kernel install` and `eukhe tiny-models download` fetch files.

## Use

```sh
cd /path/to/project
eukhe                 # start; run /login at the first start
eukhe -p "message"    # one answer, then exit
eukhe agents          # find and open sessions
eukhe gateway         # connect Signal on your phone to the session
eukhe dashboard       # open the session in a browser
eukhe help <command>  # help for one command
```

- Settings: `~/.eukhe/settings.json` (global), `.eukhe/settings.json` (project). `/settings` opens the menu. `/set [--global] <id> <value>` sets one value.

## Memory

> γραμμάτων τε συνθέσεις, μνήμην ἁπάντων, μουσομήτορ᾽ ἐργάνην.
> And the joining of letters: memory of all things, the Muses' mother, a worker. (Aeschylus, Prometheus Bound 460-461)

- `memory.chat` (default on): each root session logs to its own chat, `~/.eukhe/chat/sessions/<session-id>/`. The log is append-only and committed with git.
- A request holds the newest turns verbatim and the view: one-line summaries (a binary tree over the log) of the older history of the same thread, the part that scrolled out of the transcript. The agent zooms into a line to read its messages. No session reads the chat of another session.
- A subagent gets the view one time, at spawn, and logs nothing.
- `memory.chat` off: the plain transcript, compacted when it fills.
- `memory.model` (global): the model that writes the summaries. Unset: `modelRoles.all`, then `auxiliaryModel`.
- `/memory`: the memory as a dated tree. `/memory model`: select the model.
- `eukhe chat view|status|browse|import`: the shared chat `~/.eukhe/chat/` of earlier versions and of `chat import`.
- Design: Victor Taelin's [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449).

> οὔκουν μνήμης ἀλλὰ ὑπομνήσεως φάρμακον ηὗρες.
> Not a drug for memory, but for reminding, have you found. (Plato, Phaedrus 275a)

Plato's Thamus says it of writing. eukhe keeps both: the log of each thread is the memory (μνήμη), the view lines are its reminders (ὑπομνήματα).

## Agents

- `rlm.spawn` in the agent's Python REPL starts subagents.
- An agent sends messages only to its parent and to its own children. A busy target gets the message when idle; a parked target wakes.
- `@name message` at the start of your prompt: message an agent of the session. `/agents`: list and open them.
- `/dynamic-workflow <request>`: one script fans out many subagents in phases (`workflow.size`: `small`, `medium` (default), `large`).
- `/autoresearch <goal>`: an experiment loop on an `autoresearch/*` branch; it commits only measured improvements. `/autoresearch off|status|clear`.

## Stops

- A reply with no tool call is a candidate stop. Directors examine it in this sequence:
  - LengthStop: the reply hit the output limit. The run continues.
  - EmptyStop: the reply has no text. The run continues with a note, at most 3 times.
  - MarkupStop: the reply holds tool-call markup that eukhe cannot read. The run continues.
  - PendingWork: jobs, children or workflow runs still run. The stop is a pause; their ends wake the session.
- Any other reply is the answer, whatever its text says. eukhe sends no further request for it.
- `/goal`, `/autonomous`, `/remind`, `/force` add Directors that continue the run.

## Tools

- `read` shows PNG and JPEG images (at most 1568 px per side and 500 KB) to a model with vision. For a larger image, the agent uses `attach_image`, which resizes it.
- The `bash` tool gives each step effects: `read`, `write`, `exec`, `net`, `outside` (outside the workspace), `protected` (eukhe config and credentials, `.git`, `.eukhe`, a PATH directory), `secret`.
- `shell.autoEffects`: the effects that run without a question. Default: all. Remove an effect to get a question before each step with it. A project cannot set it.
- The phone gateway shows no question: it refuses a write to a `protected` path when the auto set does not hold `protected`.
- `ssh://` reads go only to the hosts in `ssh.hosts` (default empty: all refused).

## Prompt

- The system prompt and the tool schemas of a default root request stay below 21,300 bytes. A test holds this budget.
- `eukhe prompt`: print the assembled prompt and its layers. `/system-prompt`: the prompt of the session.

## Privacy

- `privacy.anonymizeRemote` (default off). On, a remote provider gets tokens (`PERSON_1`, `IP_2`) for your terms, email addresses, phone numbers, IP addresses and US social security numbers. eukhe maps the tokens back in the answer, so the transcript and the tool calls see the real text. Credentials (API keys and tokens, private keys, card numbers, IBANs) are hashed one way.
- The detectors match only well-formed values: code passes unchanged (`a::before`, `std::fmt`, versions, hashes). Paths and domains pass.
- Loopback providers (`localhost`, `127.*`, `::1`) get the raw text. The chat memory always keeps the raw text.
- `privacy.terms`: your phrases. Example for `~/.eukhe/settings.json`: `"privacy": { "anonymizeRemote": true, "terms": ["Your Name", "yourdomain.tld"] }`.

## Gateway

- `eukhe gateway` runs signal-cli and relays Signal messages into the newest session. Settings: `gateway.signal.account`, `gateway.signal.allow`, `gateway.signal.cliPath`, `gateway.signal.cwd`, `gateway.signal.model`.
- Phone commands: `/help`, `/sessions`, `/use N`, `/latest`, `/new`, `/stop`, `/status`, `/memory`, `/model`, `/reasoning`. Other slash commands go to the session.
- `gateway.rootHeartbeat` (global; default unset: off): a heartbeat schedule (`every 30 minutes`, a cron expression). When set, the phone talks to one persistent session named `root`, made when missing and found again after a restart. Each gateway start creates or replaces its heartbeat; a beat waits while the session is busy. `/latest` returns to `root`.
- Home Manager: `programs.eukhe.gateway.enable` runs the gateway as a systemd user service (Linux).

## Dashboard

- `eukhe dashboard` serves a web app on 127.0.0.1: chat, model, thinking, queue, compaction, approvals, saved sessions, the memory tree.
- The printed URL holds a pairing token after `#token=`. `--rotate-token` replaces it.
- `--allow-host <name>`: also answer to a forwarder name, for example from `tailscale serve`.

## Schedules

- `/heartbeat`: a persistent prompt on a schedule. `/heartbeats`: list all heartbeats.
- `eukhe schedule list|add|cancel`: prompts that run later or on a recurring schedule.

## Local models

- `eukhe tiny-models`: list the pinned local models (text, speech to text, text to speech). `eukhe tiny-models download <id|all>`: install, checked against its sha256.
- `eukhe translate`, `eukhe say`, `eukhe transcribe` use them. `stt.enabled` (default off): dictation into the editor.

## Extensions

- `eukhe mcp add|list|get|remove`, `/mcp`: MCP servers.
- `eukhe package install|remove|list|update`: skills, prompts and themes from npm or git.
- `factory.enabled` (default off), `/factory`, `eukhe factory`: share and run factory machines.
- `/refine`, `autoRefine.enabled` (default on): refine prompt notes, skills, subagents and memory.

## Laws

- The rules of eukhe are [Bend 2](https://github.com/bendlang/bend) models, compiled into the binary. Rust holds no copy of a rule.
- `LAWS.bend` states the laws, `PROOF.bend` proves them, `LAWS.lock` freezes them. See [spec/README.md](spec/README.md).

```sh
bend PROOF.bend            # check every law
bend PROOF.bend --verdict  # the same, with the Lean-proven BendTT kernel
make lock                  # after a law change: check the proofs it reaches, then write LAWS.lock
```

## Bench

- Real models on generated repositories, graded by scripts. Each run makes paid model calls. See [bench/README.md](bench/README.md).

```sh
make bench-quick  # build, then one task once with claude-haiku-5-5
make bench        # build, then every task once with eukhe, then the table
```

## References

|Topic|Reference|
|---|---|
|Spec, laws, requirements|[spec/README.md](spec/README.md)|
|Benchmark|[bench/README.md](bench/README.md)|
|Contributor rules|[AGENTS.md](AGENTS.md)|
|Security reports|[SECURITY.md](SECURITY.md)|
|Third-party notices|[THIRD-PARTY-NOTICES](THIRD-PARTY-NOTICES)|
|Chat memory design|[OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449)|
|Harness design|[omp²](https://github.com/can1357/oh-my-pi/blob/omp2/PHILOSOPHY.md)|
|RLM agent design|[Prime Agent](https://www.primeintellect.ai/blog/prime-agent)|

## Limitations

- Runs model-written Python and shell with your permissions. No sandbox; by default no effect asks. Trusted repositories only.
- No Windows.
- The privacy scrubber is off by default. On, it detects only well-formed values and your terms.
- `eukhe chat` reads only the shared chat, not the chat of a session.

## Attribution

- Fork of Prime Intellect's [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent), which ports Mario Zechner's TypeScript agent.
- Chat memory design: Victor Taelin's [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449) and [OptMem](https://github.com/VictorTaelin/OptMem).
- Not affiliated with Prime Intellect, Victor Taelin or Earendil.
- Made by [Gil Rodrigues](https://gildrb.com).
- Copyright and license notices: [THIRD-PARTY-NOTICES](THIRD-PARTY-NOTICES).

## License

MIT. See [LICENSE](LICENSE).
