# Signal gateway

`eukhe gateway` connects Signal on your phone to the session you use in the CLI.

- A Signal message goes to the newest root session (the one the CLI shows), as a `[signal]` row.
- The agent replies in short ASD-STE100 English, to Signal. Signal shows "typing" while it works.
- Typing in the CLI keeps replies in the CLI; the next Signal message routes them to Signal again.
- Daemon stopped by `eukhe shutdown`: the gateway does not restart it; it reattaches when a daemon starts, or starts one at the next Signal message.
- Daemon stopped otherwise: the gateway restarts it and reattaches; messages wait.

## Setup

```nu
nix profile install nixpkgs#signal-cli  # or Home Manager programs.eukhe.gateway.enable (see Service)
eukhe gateway                           # follow its steps
```

- No linked account: it shows a QR code. Phone: Signal > Settings > Linked devices > Link new device; scan.
- Service installed: starts the service and exits. Else runs in the foreground (Ctrl+C stops).
- Then send a message to Note to Self. No settings needed; uses the only signal-cli account.

[signal-cli](https://github.com/AsamK/signal-cli).

## Service

Home Manager (Linux), starts with the computer:

```nix
programs.eukhe.gateway.enable = true;
```

|Option|Default|Effect|
|---|---|---|
|`gateway.command`|`lib.getExe programs.eukhe.package`|eukhe executable; set when `package` is `null` (mise: `~/.local/share/mise/shims/eukhe`)|
|`gateway.signalCli`|`pkgs.signal-cli`|signal-cli package|
|`gateway.path`|`[]`|Extra PATH dirs, also for tools of a daemon it starts|
|`gateway.environment`|`{}`|Extra env vars, for the gateway and a daemon it starts|

- Starts only after linking (needs `~/.local/share/signal-cli/data/accounts.json`); restarts after a crash.
- On reconnect to a daemon not older than its build (an upgrade), the gateway exits; the service restarts it on the new build. It never replaces a daemon.
- Boot start needs linger: `loginctl enable-linger $USER`.

```nu
journalctl --user -u eukhe-gateway -f  # log
```

## Other people (dedicated number)

Your own number: only Note to Self works. For other senders, give the gateway a second number:

```nu
signal-cli -a +15557654321 register         # captcha asked: add --captcha <token> (https://signalcaptchas.org/registration/generate.html)
signal-cli -a +15557654321 verify 123456    # SMS code
```

Then add senders to `allow`; with two accounts also set `account`.

## Settings

Optional, global only (`~/.eukhe/settings.json`); project settings cannot set `gateway`. Home Manager: `programs.eukhe.settings.gateway` (activation replaces `~/.eukhe/settings.json`).

```json
{
  "gateway": {
    "signal": {
      "account": "+15557654321",
      "allow": ["+15551234567"],
      "cliPath": "signal-cli",
      "cwd": "~/work",
      "model": "elpis-fast/qwen3.8-27b"
    }
  }
}
```

|Key|Default|Effect|
|---|---|---|
|`account`|The only signal-cli account|signal-cli account|
|`allow`|`[]`|Numbers or ACIs allowed to send; Note to Self always accepted|
|`cliPath`|`signal-cli` on `PATH`|signal-cli executable|
|`cwd`|`$HOME`|Folder of a new session|
|`model`|The session model|Model for Signal messages (`provider/model-id`, see `eukhe model list`); `/model gateway` sets or clears it ([settings.md](settings.md#model-roles))|

`--daemon-socket <path>`: daemon on another socket.

## Model

`model` runs Signal messages on one model, e.g. a local one.

- Before each Signal message, the gateway switches the session to `model` if different; the shared CLI then uses it too.
- The switch also makes `model` the default, as the `chat` role of CLI `/model` does.
- Switch fails (unknown model, provider not signed in): message not sent; Signal gets `Error: ...`.
- `/status` shows the session's model.

## Phone commands

Whole message, case-insensitive.

|Command|Effect|
|---|---|
|`/help`|Show the commands|
|`/sessions`|9 newest root sessions: number, name or first message, folder, age; `*` marks the open one|
|`/use N`|Next messages go to session `N` of the last `/sessions` list|
|`/latest`|Next messages go to the newest session (default)|
|`/new`|New session in `cwd`, used next|
|`/stop`|Stop the current turn|
|`/status`|Session name, folder, model, mode, busy state|

Other text, including session commands such as `/compact`, goes to the agent.

## Replies

- Signal gets each final agent message: text, `Error: ...`, or `Stopped.`; also `Error: ...` when a turn fails before the model answers (e.g. no model set).
- No thinking, tool calls, or tool output.
- Later turns (e.g. after a subagent report) also reply to Signal, until you type in the CLI.

## Security

> [!WARNING]
> A Signal message runs tools on this machine with your user permissions.
> No approval step: with only the gateway attached, each step that would
> ask for approval runs at once.

- Only Note to Self and `allow` reach the agent; other senders are ignored.
- Steps that write eukhe's own files (config, credentials, a `.git` or `.eukhe` dir, a `PATH` dir) or read or write a secret (ssh keys, credential stores) never run from the phone: the agent gets an immediate refusal and can ask you to run it from the TUI or dashboard. If the TUI or dashboard is attached to the session, it gets the approval question instead (docs/tools.md G5).
- Keep `allow` short: each number can run commands here.
- Lock the phone screen: an open phone can use the agent.
- Network: only signal-cli to the Signal service, only while `eukhe gateway` runs.

## Limits

- Images only, at most 4 per message; other attachments are ignored and the agent is told.
- Group messages ignored.
- One session at a time for all senders.
- Replies over 2000 characters arrive split.
