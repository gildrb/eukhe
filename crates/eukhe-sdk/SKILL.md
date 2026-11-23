---
name: embed-eukhe
description: Adds the Eukhe coding agent to a project - the npm package `eukhe` for Node.js and TypeScript, `eukhe acp` over stdio for any other language, or a provider instance in T3 Code. Use when asked to add, embed or integrate Eukhe in an app, service, CLI or editor.
---

# Embed Eukhe

Eukhe runs inside another program as `eukhe acp`: an Agent Client Protocol (ACP) agent, JSON-RPC 2.0 lines on stdin and stdout, its sessions in the local Eukhe daemon. Each turn ends with a run report: the answer, the checks and the irreversible effects that ran.

## 1. Pick the route

| The project | Route |
|---|---|
| `package.json`, Node.js >= 22 or TypeScript | section 2, the npm package `eukhe` |
| Python, Go, Rust, any other language | section 3, `eukhe acp` over stdio |
| The user runs T3 Code and wants Eukhe in it | section 4, settings |

Platforms: macOS (Apple Silicon), Linux (x64, arm64). On Windows, stop and report that Eukhe does not run there.

## 2. Node.js and TypeScript

1. Add the package with the project's package manager (the lockfile decides): `npm install eukhe`, `pnpm add eukhe` or `yarn add eukhe`.
2. Binary: when `eukhe --version` runs, keep that one. Else `npx eukhe install` (checks SHA256SUMS, installs `~/.local/bin/eukhe`, no root).
3. Code: start one `Eukhe` per process at startup, one session per conversation, close both on shutdown.

```ts
import { Eukhe, NotLoggedIn } from "eukhe";

const eukhe = await Eukhe.start({ cwd: projectDir }); // the directory the agent works in
try {
  const session = await eukhe.session(); // or { model: "anthropic/claude-sonnet-4-5" }
  for await (const event of session.prompt(task)) {
    switch (event.$) {
      case "Text": process.stdout.write(event.text); break;
      case "ToolCallStart": console.error(`> ${event.title}`); break;
      case "RunReport": console.error(event.report.label, event.report.ran); break;
      case "TurnEnd": console.error(event.stopReason); break;
    }
  }
} catch (error) {
  if (error instanceof NotLoggedIn) console.error(`run once: ${error.login.command}`);
  else throw error;
} finally {
  await eukhe.close();
}
```

- Events (`event.$`): `Text`, `Thinking`, `ToolCallStart`, `ToolCallUpdate`, `ToolCallEnd`, `Plan`, `RunReport`, then always `TurnEnd` last.
- `Eukhe.start` throws `NotInstalled` (with `installCommand`) when no binary is found; `eukhe.session()` throws `NotLoggedIn` without a login.
- Leaving the `for await` loop cancels the turn; `session.cancel()` does too.
- HTTP server streaming turns: copy the shape of https://github.com/gildrb/eukhe/blob/main/crates/eukhe-sdk/ts/examples/sse-server.ts (Server-Sent Events, one session per request, cancel on disconnect).
- Session calls: `session.budget`, `session.acceptance`, `session.undo()`, `session.diff()`, `session.effects()`. Read `node_modules/eukhe/README.md` before using them.
- A model id that the agent lacks throws `UnknownModel` with `available`; pick from that list.

## 3. Any other language: ACP over stdio

1. Install: `curl -fsSL https://eukhe.com/install | sh` (or `nix run github:gildrb/eukhe`).
2. Use the language's ACP client library when the project already has one or one exists for the language (agentclientprotocol.com); else plain JSON lines as below.
3. Spawn `eukhe acp` with the project directory as cwd. Messages are one JSON object per line.

```python
import json, subprocess

agent = subprocess.Popen(["eukhe", "acp"], cwd=project, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

def send(message):
    agent.stdin.write(json.dumps(message) + "\n")
    agent.stdin.flush()

def request(id, method, params, on_update=print):
    send({"jsonrpc": "2.0", "id": id, "method": method, "params": params})
    for line in agent.stdout:
        message = json.loads(line)
        if message.get("id") == id and "method" not in message:
            if "error" in message:
                raise RuntimeError(message["error"])  # code -32000: data.login.command
            return message["result"]
        if message.get("method") in ("session/update", "_eukhe/run_report"):
            on_update(message)
        elif "method" in message and "id" in message:  # a request to the client
            send({"jsonrpc": "2.0", "id": message["id"], "error": {"code": -32601, "message": "unsupported"}})

request(1, "initialize", {"protocolVersion": 1, "clientCapabilities": {}})
session = request(2, "session/new", {"cwd": project, "mcpServers": []})["sessionId"]
result = request(3, "session/prompt", {"sessionId": session, "prompt": [{"type": "text", "text": task}]})
```

- Answer text: `session/update` with `params.update.sessionUpdate == "agent_message_chunk"`, text in `params.update.content.text`.
- `_eukhe/run_report` arrives once per turn, before the `session/prompt` response (`stopReason`).
- `session/request_permission` asks before an irreversible effect; answering `-32601` lets every effect run without asking again.
- `session/cancel` (a notification) stops the turn; the prompt then answers `stopReason: "cancelled"`.
- One session per process at a time; start another `eukhe acp` for a second.
- Every method, update and `_eukhe/` extension (budget, acceptance, undo, diff, effects): https://github.com/gildrb/eukhe/blob/main/crates/eukhe-sdk/README.md#acp. JSON Schema: https://github.com/gildrb/eukhe/blob/main/crates/eukhe-sdk/acp.schema.json.

## 4. T3 Code

Merge into `providerInstances` of `userdata/settings.json` in the T3 home (`~/.t3` by default); `commandPath` is the absolute path `command -v eukhe` prints:

```json
"providerInstances": {"eukhe": {"driver":"acpRegistry","displayName":"Eukhe","config":{"source":"local","commandPath":"<path to eukhe>","commandArgs":["--mode","acp"]}}}
```

Install Eukhe first (section 3, step 1). Eukhe is not in the ACP registry.

## Login

A model provider login is a step for a person, once per machine: `eukhe login <provider>` (a browser sign-in), or an API key on stdin (`printf %s "$KEY" | eukhe login openai`). `eukhe login --json` lists the providers and which are logged in.

- Check `eukhe login --json`; when nothing is logged in, finish the integration and end the final answer with the exact `eukhe login <provider>` command.
- Never write an API key into code, config or the repository, and never ask for one in chat.

## Done when

- The project builds and its existing tests pass.
- A smoke run prompts `Reply with exactly: OK` and sees the text `OK`, a run report and `end_turn`; without a login, it sees `NotLoggedIn` (TypeScript) or `-32000` with `data.login` (ACP), and the final answer names the login command.
- The final answer lists the files added and the commands a person still runs (install, login).
