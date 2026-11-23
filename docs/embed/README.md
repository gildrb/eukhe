# Embedding Eukhe

Eukhe runs inside another program as `eukhe acp`: an [Agent Client Protocol](https://agentclientprotocol.com) (ACP) agent that reads and writes JSON-RPC 2.0 lines on stdio and runs its sessions in the local Eukhe daemon. Budget, checks, undo, diff and irreversible effects are `_eukhe/` extension methods beside the standard ACP methods.

- Node.js or TypeScript: the npm package `eukhe`
- Any other language: `eukhe acp` over stdio
- T3 Code: a local ACP provider instance

Platforms: macOS (Apple Silicon), Linux (x64, arm64).

## TypeScript

```sh
npm install eukhe && npx eukhe install
```

```ts
import { Eukhe } from "eukhe";

const eukhe = await Eukhe.start({ cwd: "/path/to/project" });
const session = await eukhe.session();
for await (const event of session.prompt("Add a --verbose flag to the CLI")) {
  if (event.$ === "Text") process.stdout.write(event.text);
  if (event.$ === "RunReport") console.log(event.report.label, event.report.ran);
}
await eukhe.close();
```

`npx eukhe install` installs the Eukhe release to `~/.local/bin/eukhe` after checking it against the release's SHA256SUMS. Events, session calls and errors: [sdk/typescript/README.md](../../sdk/typescript/README.md).

## Other languages

1. Install Eukhe: `curl -fsSL https://eukhe.com/install | sh`.
2. Start `eukhe acp` in the project directory and speak ACP protocol version 1 over its stdin and stdout, with the language's ACP client library or plain JSON lines.
3. `initialize`, `session/new`, then `session/prompt` per turn; `_eukhe/run_report` arrives before each `session/prompt` response.

Reference: [acp.md](acp.md). JSON Schema of the `_eukhe/` methods and the login error: [eukhe-acp.schema.json](eukhe-acp.schema.json).

## T3 Code

Eukhe is not in the ACP registry. T3 Code runs it as a local command from its settings file, `userdata/settings.json` in the T3 home (`~/.t3` by default); the settings form hides `commandArgs`:

```json
"providerInstances": {"eukhe": {"driver":"acpRegistry","displayName":"Eukhe","config":{"source":"local","commandPath":"<path to eukhe>","commandArgs":["--mode","acp"]}}}
```

`<path to eukhe>` is the absolute path `command -v eukhe` prints. Untested against a running T3 Code server.

## Login

Eukhe needs one model provider login per machine:

```sh
eukhe login anthropic                    # a subscription: sign-in URL on stderr, opened in the browser
printf %s "$KEY" | eukhe login openai    # an API key from stdin
eukhe login                              # the providers and their login state
```

Without a login, `session/new` answers `-32000` with `data.login.command` (`eukhe login <provider>`); the TypeScript client throws `NotLoggedIn` with the same data.

## Agent skill

[skills/embed-eukhe/SKILL.md](skills/embed-eukhe/SKILL.md) tells a coding agent asked to add Eukhe to a project what to do per stack. Install it in an Agent Skills host:

```sh
npx skills add https://github.com/gildrb/eukhe/tree/main/docs/embed/skills/embed-eukhe
```
