# eukhe

This package is a library that embeds the [Eukhe](https://github.com/gildrb/eukhe) coding agent in your application; the `eukhe` command-line agent itself is installed with `npx eukhe install`.

Eukhe works in a project directory and reports what it changed and which irreversible effects ran. The client starts the agent (`eukhe acp`, the [Agent Client Protocol](https://agentclientprotocol.com)) and streams each prompt turn as typed events.

## Install

```sh
npm install eukhe
npx eukhe install
```

`npx eukhe install` downloads the Eukhe release for macOS (Apple Silicon) or Linux (x64, arm64), checks it against the release's SHA256SUMS, and installs it to `~/.local/share/eukhe` with a launcher at `~/.local/bin/eukhe`. A specific release: `npx eukhe install 0.10.81`.

The client needs Eukhe 0.10.81 or newer (`MINIMUM_EUKHE_VERSION`), the first release with `eukhe acp`. Update an older Eukhe with `eukhe update`. `Eukhe.start` runs `eukhe --version` first and throws `TooOld` for an older release instead of starting it.

Eukhe needs one model provider login per machine: `eukhe login <provider>` (for example `eukhe login openai-codex`; an API key: `printf %s "$KEY" | eukhe login openai`). `eukhe login --json` lists the providers and which are logged in.

## Use

```ts
import { Eukhe, EukheError } from "eukhe";

const eukhe = await Eukhe.start({ cwd: "/path/to/project" });
try {
  const session = await eukhe.session(); // or { model: "anthropic/claude-sonnet-4-5" }
  for await (const event of session.prompt("Add a --verbose flag to the CLI")) {
    if (event.$ === "Text") process.stdout.write(event.text);
    if (event.$ === "ToolCallStart") console.error(`> ${event.title}`);
    if (event.$ === "RunReport") console.error(event.report.label, event.report.ran);
  }
} catch (error) {
  if (error instanceof EukheError) console.error(`${error.$}: ${error.message}`); // error.$ narrows: see Errors
  else throw error;
} finally {
  await eukhe.close();
}
```

`session.cancel()` stops the running turn; its stream then ends with `TurnEnd` `cancelled`. Leaving the `for await` loop early cancels the turn too.

Runnable examples: [examples/cli.ts](examples/cli.ts) (a terminal command) and [examples/sse-server.ts](examples/sse-server.ts) (an HTTP server streaming turns as Server-Sent Events).

## Events

`session.prompt(text)` yields `EukheEvent`; switch on `$`:

```ts
type EukheEvent =
  | { $: "Text"; text: string }                       // a piece of the answer
  | { $: "Thinking"; text: string }                   // a piece of the model's reasoning
  | { $: "ToolCallStart"; id: string; title: string; kind: ToolKind | null; input: unknown }
  | { $: "ToolCallUpdate"; id: string; title: string | null; content: ToolCallContent[] | null; output: unknown }
  | { $: "ToolCallEnd"; id: string; outcome: "completed" | "failed"; content: ToolCallContent[] | null; output: unknown }
  | { $: "Plan"; entries: PlanEntry[] }               // the whole current plan
  | { $: "RunReport"; report: RunReport }             // once per turn, just before TurnEnd
  | { $: "TurnEnd"; stopReason: StopReason };         // always last
```

`RunReport` holds the final `answer`, the acceptance `label` (`verified`, `failed`, `unverified`, ...) and `checks`, `ran` (the irreversible effects that ran this turn: pushes, network calls, ...), `unknown` (steps a crash left unknown, treated as not run) and `left` (work the run found left).

## Session

| Call | Result |
|---|---|
| `session.prompt(text)` | the turn's events |
| `session.cancel()` | stops the running turn |
| `session.budget.get()` / `.set(limits, "run" \| "standing")` / `.add(amounts)` | the budget report (`costMicros`, `tokens`, `timeMs`, `toolCalls`, `requests`), or `null` |
| `session.acceptance.get()` / `.set(checks)` | the checks a turn must pass before Eukhe calls it done |
| `session.diff("turn" \| "all")` | `{ diff, paths, skipped }` of the last turn or the whole session |
| `session.undo()` | restores the files the last turn changed; `notUndone` lists effects no undo reverses |
| `session.effects()` | every irreversible effect that ran in the session |
| `session.close()` | ends the session's agent process |

Each session runs in its own `eukhe acp` process; `eukhe.close()` ends them all.

## Errors

Every error the client throws is an `EukheError`. `error instanceof EukheError` narrows `error` to the `EukheFailure` union, so a `switch` on `error.$` reaches each failure's fields without a cast:

```ts
import { Eukhe, EukheError } from "eukhe";

try {
  const eukhe = await Eukhe.start({ cwd: process.cwd() });
  await eukhe.close();
} catch (error) {
  if (!(error instanceof EukheError)) throw error;
  switch (error.$) {
    case "NotInstalled":
      console.error(`install eukhe: ${error.installCommand}`);
      break;
    case "TooOld":
      console.error(`eukhe ${error.found} is older than ${error.minimum}; run ${error.updateCommand}`);
      break;
    case "NotLoggedIn":
      console.error(`log in once: ${error.login.command}`);
      break;
    case "UnknownModel":
      console.error(`models: ${error.available.join(", ")}`);
      break;
    default:
      console.error(`${error.$}: ${error.message}`);
  }
}
```

`error instanceof TooOld` (or any failure class) narrows to that class.

| `$` | Meaning | Fields |
|---|---|---|
| `NotInstalled` | no `eukhe` binary found | `installCommand` (`npx eukhe install`), `searched` |
| `TooOld` | the binary is a release older than `MINIMUM_EUKHE_VERSION`; `eukhe acp` was not started | `found`, `minimum`, `updateCommand` (`eukhe update`) |
| `NotLoggedIn` | no model provider login | `login.command` (the command to run), `login.slashCommand` (the same inside `eukhe`, or `null`), `login.instructions` |
| `Unsupported` | the agent lacks an Eukhe extension (an older Eukhe, or another ACP agent) | `feature` |
| `UnknownModel` | `session({ model })` names a model the agent does not offer | `model`, `available` |
| `TurnInProgress` | `prompt` while the session's turn still runs | |
| `AgentFailed` | the agent answered with a JSON-RPC error | `method`, `code`, `data` |
| `AgentExited` | the agent process ended | `exitCode`, `signal`, `stderr` |

## Binary lookup

`Eukhe.start({ bin })` uses `bin`, else `EUKHE_BIN`, else the first `eukhe` on `PATH`, else `~/.local/bin/eukhe`, then checks its `--version` (a source build's `X.Y.Z-dev` passes). `env` adds variables to the agent's environment. `npx eukhe <args>` runs the found binary with `<args>`.

## Protocol

The client speaks ACP protocol version 1 plus Eukhe's `_eukhe/*` extension methods. Any ACP client can use them: [crates/eukhe-sdk/README.md](https://github.com/gildrb/eukhe/blob/main/crates/eukhe-sdk/README.md#acp) is the reference, [crates/eukhe-sdk/acp.schema.json](https://github.com/gildrb/eukhe/blob/main/crates/eukhe-sdk/acp.schema.json) the JSON Schema.

## Limitations

- macOS on Apple Silicon and Linux (x64, arm64) only.
- Irreversible effects run without asking the host; `RunReport.ran` and `session.effects()` list them.
- Login is a step a person runs once (`eukhe login <provider>`); the client reports its absence as `NotLoggedIn`.

## License

MIT
