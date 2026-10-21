# Signal gateway

`eukhe gateway` connects the Signal app on your phone to the eukhe session
that you use in the CLI.

- Send a message in Signal. It goes into the newest root session, the same
  session that the CLI shows. The CLI shows it as a `[signal]` row.
- The agent replies in short ASD-STE100 English. The reply comes back to
  Signal.
- Signal shows "typing" while the agent works.
- When you type in the CLI, the replies stay in the CLI. The next Signal
  message sends the replies to Signal again.
- If the daemon stops on request (`eukhe shutdown`), the gateway does not
  start it. It attaches again when a new daemon starts, or starts one at the
  next Signal message.
- If the daemon stops for another reason, the gateway starts it again and
  attaches again. Messages wait until the session is back.

## Setup

1. Install [signal-cli](https://github.com/AsamK/signal-cli). Home Manager
   users: `programs.eukhe.gateway.enable` installs it (see
   [Service](#service)).

   ```nu
   nix profile install nixpkgs#signal-cli
   ```

2. Run the gateway in a terminal and do the steps that it shows:

   ```nu
   eukhe gateway
   ```

   - No linked account: it shows a QR code. On the phone, open Signal >
     Settings > Linked devices > Link new device. Scan the code.
   - With the service installed: it starts the service and stops. Else it
     runs in the foreground (stop with Ctrl+C).

3. In Signal, send a message to Note to Self.

No settings are necessary. The gateway uses the only signal-cli account.

## Service

Home Manager (Linux) starts the gateway with the computer:

```nix
programs.eukhe.gateway.enable = true;
```

|Option|Default|Effect|
|---|---|---|
|`gateway.command`|`lib.getExe programs.eukhe.package`|The eukhe executable. Set it when `package` is `null` (mise: `~/.local/share/mise/shims/eukhe`)|
|`gateway.signalCli`|`pkgs.signal-cli`|The signal-cli package|
|`gateway.path`|`[]`|More PATH directories. A daemon that the gateway starts uses this PATH for tools|
|`gateway.environment`|`{}`|More environment variables, for the gateway and a daemon that it starts|

- The service starts only after the link (it needs
  `~/.local/share/signal-cli/data/accounts.json`).
- The service restarts after a crash.
- When the gateway connects again and finds a daemon that is not older than
  its own build (an upgrade), the gateway stops. The service starts it again
  on the new build. The gateway never replaces a daemon.
- User services start at boot only with linger:
  `loginctl enable-linger $USER`.

Log:

```nu
journalctl --user -u eukhe-gateway -f
```

## Other people (dedicated number)

With your own number, only Note to Self works. To let other numbers send to
the agent, use a second number for the gateway:

1. Register the number. If Signal asks for a captcha, add
   `--captcha <token>` (from https://signalcaptchas.org/registration/generate.html).

   ```nu
   signal-cli -a +15557654321 register
   ```

2. Verify with the SMS code:

   ```nu
   signal-cli -a +15557654321 verify 123456
   ```

3. Add the senders to `allow`. With two accounts, also set `account`.

## Settings

All keys are optional. Set them in the global settings,
`~/.eukhe/settings.json`. Project settings cannot set `gateway`.

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
|`account`|The only signal-cli account|The signal-cli account|
|`allow`|`[]`|Numbers or ACIs that can send to the agent. Note to Self is always accepted|
|`cliPath`|`signal-cli` on `PATH`|The signal-cli executable|
|`cwd`|`$HOME`|The folder of a new session|
|`model`|The session model|The model (`provider/model-id`, see `eukhe model list`) for Signal messages|

With Home Manager, set `programs.eukhe.settings.gateway`. Activation
replaces `~/.eukhe/settings.json`.

Use `--daemon-socket <path>` for a daemon on another socket.

## Model

Set `model` to run Signal messages on one model, for example a local one.

- Before each Signal message, the gateway switches the session to `model`
  if the session uses a different model.
- The CLI shares the session. After a Signal message, the CLI also uses
  `model`.
- The switch also sets `model` as the default model, as `/model` in the
  CLI does.
- If the switch fails (unknown model, provider not signed in), the message
  does not go to the agent. Signal gets `Error: ...`.
- `/status` shows the model of the session.

## Phone commands

Send the command as the full message. Case is not important.

|Command|Effect|
|---|---|
|`/help`|Show the commands|
|`/sessions`|Show the 9 newest root sessions: number, name or first message, folder, age. `*` marks the open session|
|`/use N`|Send the next messages to session `N` of the last `/sessions` list|
|`/latest`|Send the next messages to the newest session (default)|
|`/new`|Start a new session in `cwd` and use it|
|`/stop`|Stop the current turn|
|`/status`|Show the session name, folder, model, mode, and busy state|

Other text goes to the agent. Session commands such as `/compact` also go to
the agent.

## Replies

- After a Signal message, Signal gets each final agent message: text,
  `Error: ...`, or `Stopped.`.
- A turn that fails before the model answers (for example, no model is
  set) also sends `Error: ...`.
- Signal does not get thinking, tool calls, or tool output.
- Replies to later turns also go to Signal, for example after a subagent
  report.
- A message that you type in the CLI stops the replies to Signal.

## Security

> [!WARNING]
> A Signal message runs tools on this machine with your user permissions.
> There is no approval step: while only the gateway is attached to the
> session, each step that would ask for approval runs at once.

- Only Note to Self and the numbers in `allow` reach the agent. The gateway
  ignores all other senders.
- A step that writes eukhe's own files (its config and credentials, a `.git`
  or `.eukhe` dir, a `PATH` dir) or reads or writes a secret (ssh keys,
  credential stores) never runs from the phone. The agent gets a refusal at
  once and can tell you to run the step from the TUI or the dashboard. When
  the TUI or the dashboard is attached to the same session, it gets the
  approval question instead (docs/tools.md G5).
- Keep `allow` short. Each number in it can run commands on this machine.
- Protect the phone with a screen lock. Anyone with the open phone can use
  the agent.
- The gateway uses the network only through signal-cli, to the Signal
  service, while `eukhe gateway` runs.

## Limits

- Images only. The gateway ignores other attachments and tells the agent.
  At most 4 images per message.
- Group messages are ignored.
- One session at a time for all senders.
- A reply longer than 2000 characters arrives as more than one message.
