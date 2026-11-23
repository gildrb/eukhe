# SDK

The npm package `eukhe` embeds Eukhe in a Node.js (>= 22) process. It starts the local agent, opens sessions in one project directory, and streams each prompt turn as typed events, ending with a run report: the answer, the acceptance checks and the irreversible effects that ran.

For another language or a separate process, see [ACP](#acp). For sessions inside a Rust process, see [Rust](#rust).

Platforms: macOS (Apple Silicon), Linux (x64, arm64).

```sh
npm install eukhe && npx eukhe install
```

```ts
import { Eukhe } from "eukhe";

const eukhe = await Eukhe.start({ cwd: "/path/to/project" });
try {
  const session = await eukhe.session();
  for await (const event of session.prompt("What files are in the current directory?")) {
    if (event.$ === "Text") process.stdout.write(event.text);
  }
} finally {
  await eukhe.close();
}
```

This uses the installed Eukhe, its model provider login and its default model. Install, events, session calls, errors and binary lookup: [ts/README.md](ts/README.md).

## Login

Eukhe needs one model provider login per machine:

```sh
eukhe login openai-codex                    # a subscription: sign-in URL on stderr, opened in the browser
printf %s "$KEY" | eukhe login openai    # an API key from stdin
eukhe login                              # the providers and their login state
```

Without a login, `eukhe.session()` throws `NotLoggedIn` with `login.command`; over ACP, `session/new` answers `-32000` with `data.login.command`.

## Rust

`eukhe-sdk` opens sessions in the host's own process, without the daemon: `open_session`, `prompt`, `watch`, the budget, the run reports and the irreversible effects. It is not on crates.io; its API may change with any release.

```rust
use eukhe_sdk::{context::BACKGROUND_CONTEXT, open_session, SessionConfig, SessionStorage};

let cx = &*BACKGROUND_CONTEXT;
let config = SessionConfig::new("/home/me/.eukhe", "/home/me/project", eukhe_sdk::new_session_id(), SessionStorage::Memory);
let session = open_session(config, cx).await?;
let conversation = session.main();
eukhe_sdk::prompt(&session, &conversation, "Summarize README.md", cx).await?;
session.close(cx).await?;
```

Run the example: `cargo run -p eukhe-sdk --example prompt -- <agent dir> <cwd> <provider/model> <prompt>`. API: `cargo doc -p eukhe-sdk --open`.

## ACP

Any language embeds Eukhe through `eukhe acp`, an [Agent Client Protocol](https://agentclientprotocol.com) (ACP) agent that reads and writes JSON-RPC 2.0 lines on stdio. Budget, checks, undo, diff and irreversible effects are `_eukhe/` extension methods beside the standard ACP methods.

1. Install Eukhe: `curl -fsSL https://eukhe.com/install | sh`.
2. Start `eukhe acp` in the project directory and speak ACP protocol version 1 over its stdin and stdout, with the language's ACP client library or plain JSON lines.
3. `initialize`, `session/new`, then `session/prompt` per turn; `_eukhe/run_report` arrives before each `session/prompt` response.

Sessions run in the Eukhe daemon, which starts when none runs. A plain ACP client never sees the `_eukhe/` methods. JSON Schema of the `_eukhe/` methods and the login error: [acp.schema.json](acp.schema.json).

### Launch

```
eukhe acp                 # same as eukhe --mode acp
eukhe acp --no-session    # sessions end with the connection
eukhe acp --resume <id>   # the first session/new opens this saved session
```

Session flags (`--model`, `--provider`, `--thinking`, `--budget-*`, `--accept-*`, `--daemon-socket`) apply to every session of the connection.

### Handshake

```json
{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":1,"clientCapabilities":{}}}
{"jsonrpc":"2.0","id":1,"result":{"protocolVersion":1,
  "agentCapabilities":{"loadSession":true,
    "promptCapabilities":{"image":true,"audio":false,"embeddedContext":true},
    "mcpCapabilities":{"http":true,"sse":false},
    "sessionCapabilities":{"close":{},"list":{},"resume":{},"delete":{}},
    "_meta":{"eukhe":{"version":"1.0","features":["run_report","session_info","budget","acceptance","undo","diff","effects"]}}},
  "authMethods":[{"id":"eukhe-login","name":"Log in to a model provider","description":"..."}],
  "agentInfo":{"name":"eukhe","title":"Eukhe","version":"..."}}}
```

- A `terminal` auth method (`eukhe-terminal-login`, runs `eukhe`, where `/login` logs in) is listed only when `clientCapabilities.auth.terminal` is true. Outside the client, `eukhe login <provider>` logs in (`eukhe login` lists the providers).
- `_meta.eukhe.version` is `major.minor`; a minor only adds.

### Served methods

| Method | Notes |
|---|---|
| `session/new` | `sessionId` is the durable eukhe session id |
| `session/load` | streams the history as `session/update`, then answers |
| `session/resume` | attaches a saved session by id, no history |
| `session/list` | saved top-level sessions; `cwd` filters |
| `session/delete` | removes a saved session (the hosted one when idle) |
| `session/prompt`, `session/cancel` | one turn at a time |
| `session/close` | ends the attachment; the session stays resumable |
| `session/set_config_option` | `model`, `thought_level` |
| `authenticate` | `{}` once a model provider is logged in, else `-32000` |

- One session per connection at a time; start another process for a second.
- Updates: message and thought chunks, `tool_call` (human `title`, tool `name`, `rawInput`, absolute `locations`) and streamed `tool_call_update`, `plan` (the session's acceptance checks), `usage_update`, `available_commands_update` (`compact`, prompt templates, `skill:<name>`), `config_option_update`, `session_info_update` (title).
- `session/request_permission` asks before an irreversible effect runs; a client answering `-32601` is not asked again and the effect runs.
- No model provider logged in: `session/new|load|resume` answer `-32000` with `data.login` (`{"command":"eukhe login <provider>","slashCommand":"/login","instructions":"..."}`) and `data.authMethods`.
- Unknown session id: `-32002` with `data.sessionId`.

### Extensions

Every `_eukhe/` request takes the ACP `sessionId`. Unknown `_eukhe/` methods answer `-32601`; bad params `-32602` (`data.reason`); a daemon refusal `-32603` (`data.details`, `data.code` such as `nothing_to_undo`, `nothing_to_diff`, `run_in_progress`).

#### `_eukhe/run_report` (notification)

Sent once per prompt turn, before its `session/prompt` response, for finished, cancelled and failed turns.

```json
{"jsonrpc":"2.0","method":"_eukhe/run_report","params":{"sessionId":"019a...","promptTurnId":1,
  "stopReason":"end_turn","answer":"Done: tests pass.",
  "label":"checks_passed_unconfined","certified":true,
  "checks":[{"kind":"command","text":"`cargo test` passes","verdict":"confirmed","summary":"exited with code 0"}],
  "ran":[{"id":"e1","key":"...","run":1,"kind":"shellStep","command":"git push origin main","classes":["exec","net"],"sessionId":"019a...","atMs":1790000000000}],
  "unknown":[],"left":[]}}
```

- `stopReason` is `null` and `error` is set when the turn failed.
- `ran`: irreversible effects that ran in the turn; `unknown`: steps a restart treated as not run; `left`: work the run found left.
- `unreadable` lists parts that could not be read (`acceptance`, `effects`, `left`).

#### `_eukhe/session_info` (notification)

Eukhe-only session state (budget, loop, compaction, subagents, the turn's response boundary and quiescence) as a `session_info_update` body under `_meta["com.eukhe"]`; `eventSequence` counts across it and `session/update`.

#### Requests

```json
{"jsonrpc":"2.0","id":7,"method":"_eukhe/budget/get","params":{"sessionId":"019a..."}}
{"jsonrpc":"2.0","id":7,"result":{"budget":{"sessionId":"019a...","limits":{"tokens":200000},"spent":{"tokens":1500,"costMicros":0,"timeMs":0,"toolCalls":0,"requests":1},"phase":"working","...":"..."}}}
```

| Method | Params (beside `sessionId`) | Result |
|---|---|---|
| `_eukhe/budget/get` | | `{budget}` (`null` without one) |
| `_eukhe/budget/set` | `limits: {costMicros?,tokens?,timeMs?,toolCalls?,requests?: number or "unlimited"}`, `standing?` | `{budget}` |
| `_eukhe/budget/add` | `amounts: {costMicros?,tokens?,timeMs?,toolCalls?,requests?}` | `{budget}` |
| `_eukhe/acceptance/get` | | `{acceptance}` |
| `_eukhe/acceptance/set` | `checks: [{kind:"command",command}, {kind:"judge",condition}, {kind:"until",command}, {kind:"intent"}]`, `maxReturns?`, `intent?` | `{acceptance}` |
| `_eukhe/undo` | | `{restored, turn, left, notUndone}` |
| `_eukhe/diff` | `scope?: "turn" or "all"` | `{diff, paths, skipped}` |
| `_eukhe/effects` | | `{ran, unknown}` |

```json
{"jsonrpc":"2.0","id":8,"method":"_eukhe/undo","params":{"sessionId":"019a..."}}
{"jsonrpc":"2.0","id":8,"result":{"restored":["src/lib.rs"],"turn":2,"left":1,"notUndone":[]}}
```

## Agent skill

[SKILL.md](SKILL.md) tells a coding agent asked to add Eukhe to a project what to do per stack; the npm package ships it too. Install it in an Agent Skills host:

```sh
npx skills add https://github.com/gildrb/eukhe/tree/main/crates/eukhe-sdk
```
