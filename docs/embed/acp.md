# eukhe acp

`eukhe acp` is eukhe as an Agent Client Protocol agent (ACP protocolVersion 1): JSON-RPC 2.0, one JSON object per line on stdin/stdout. Sessions run in the eukhe daemon, which starts when none runs. Eukhe-only features ride `_eukhe/` methods, described by [eukhe-acp.schema.json](eukhe-acp.schema.json); a plain ACP client never sees them.

## Launch

```
eukhe acp                 # same as eukhe --mode acp
eukhe acp --no-session    # sessions end with the connection
eukhe acp --resume <id>   # the first session/new opens this saved session
```

Session flags (`--model`, `--provider`, `--thinking`, `--budget-*`, `--accept-*`, `--daemon-socket`) apply to every session of the connection.

## Handshake

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

## Served methods

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

## Extensions

Every `_eukhe/` request takes the ACP `sessionId`. Unknown `_eukhe/` methods answer `-32601`; bad params `-32602` (`data.reason`); a daemon refusal `-32603` (`data.details`, `data.code` such as `nothing_to_undo`, `nothing_to_diff`, `run_in_progress`).

### `_eukhe/run_report` (notification)

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

### `_eukhe/session_info` (notification)

Eukhe-only session state (budget, loop, compaction, subagents, the turn's response boundary and quiescence) as a `session_info_update` body under `_meta["com.eukhe"]`; `eventSequence` counts across it and `session/update`.

### Requests

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
