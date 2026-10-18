# Web dashboard

`eukhe dashboard` serves a web app for the eukhe session that you use in the
CLI. It works on a phone and on a desktop.

- Chat with the newest root session, or with a session that you select.
  The CLI, the Signal gateway and each dashboard tab use the same session.
- See the turn as it runs: phases, tool calls, tool output, speed.
- Control the session: model, thinking level, service tier, queue,
  compaction, retry, settings (cvars), and `bash` approvals.
- Manage saved sessions: rename, fork, export, delete, new session.
- Browse the chat memory as a tree of dated lines, down to each message.

The app is in the eukhe binary. It does not load files from the network.
The fonts are in the binary too (Inter and Ioskeley Mono, SIL Open Font
License; the license texts are at `fonts/inter-OFL.txt` and
`fonts/IoskeleyMono-OFL.txt`).

## Change the app

The source is in `crates/eukhe-dashboard/ui` (TypeScript, Preact with
Radix primitives, StyleX, Vite+). `vp build` writes the app into
`crates/eukhe-dashboard/web`, which is committed: `build.rs` embeds every
file there, so cargo and Nix builds need no Node.

1. Edit the source under `ui/src` (files that are copied as they are, such
   as fonts and icons, are under `ui/public`).
2. Run `make dashboard-ui`. It installs the locked packages, runs
   `vp check` (format, lint, types) and `vp build`.
3. Commit `ui/` and `web/` together. CI rebuilds the app and fails when
   `web/` differs from the build.

To see changes without a Rust build, run `npx vp dev` in `ui/` with
`EUKHE_DASHBOARD=127.0.0.1:<port>` naming a running dashboard: the dev
server proxies `api/ws` to it.

## Run

```nu
eukhe dashboard
```

The command prints the URL and opens it in the browser. Stop it with Ctrl+C.

|Option|Effect|
|---|---|
|`--port <port>`|Listen on this port. Default: a free port|
|`--no-open`|Print the URL. Do not open the browser|
|`--allow-host <name>`|Also accept requests for this host name. You can give it more than one time|
|`--daemon-socket <path>`|Use the daemon on this socket|

If no daemon runs, the dashboard starts one.

## Phone (tailscale serve)

The dashboard listens on `127.0.0.1` only. To use it on a phone, use
[`tailscale serve`](https://tailscale.com/docs/features/tailscale-serve). It
gives HTTPS on your tailnet name, and only the devices of your tailnet can
connect.

1. Start the dashboard on a fixed port. Give it your tailnet name:

   ```nu
   eukhe dashboard --no-open --port 8377 --allow-host box.tail1234.ts.net
   ```

2. Forward HTTPS to it:

   ```nu
   tailscale serve --bg 8377
   ```

   To share the name with other services, mount the dashboard at a path
   (`tailscale serve --bg --set-path /eukhe 8377`). The app uses relative
   URLs only, so it works under a path.

3. On the phone, open `https://box.tail1234.ts.net/` (or `/eukhe/`). To
   install it as an app, use "Add to Home Screen".

Use the name that `tailscale status` shows for this computer, without
`https://` and without a port. Without `--allow-host`, the dashboard refuses
the requests that come through `tailscale serve`.

### Phone (poros)

[poros](https://github.com/gildrb/poros) runs the dashboard and gives it its
own HTTPS link on your tailnet. It needs no `--allow-host`:

```nu
poros eukhe dashboard
```

Open the `Poros URL` that it prints. poros sends each request to the
dashboard with `Host` set to the local address, and it names the HTTPS link in
`X-Forwarded-Host`.

## Security

> [!WARNING]
> The dashboard has no login. A person who can open it can send messages to
> the agent, and the agent runs tools on this computer with your user
> permissions.

- The server listens on `127.0.0.1` only. Other computers cannot connect
  directly.
- Each request must name a permitted host in its `Host` header:
  `127.0.0.1`, `localhost`, `[::1]` (any port), or a name that you give with
  `--allow-host`. Other requests get `403`. This stops DNS rebinding: a web
  page on a name that points to `127.0.0.1` cannot read the app or use the
  socket.
- The WebSocket must come from a page of the dashboard. Its `Origin` header
  must have the same host and port as its `Host` header, or as the last
  `X-Forwarded-Host` header that a forwarder adds (poros). An upgrade with no
  `Origin`, or with another origin, gets `403`. This stops other web pages
  in your browser from using the socket: a web page cannot add
  `X-Forwarded-Host` to a WebSocket upgrade.
- The content security policy permits only the app's own files: scripts,
  styles, fonts, workers, the manifest and the socket. Images can also be
  `data:` and `blob:` URLs. There is no inline script or style.
- Give `--allow-host` only for a forwarder that you control, such as
  `tailscale serve`. A forwarder must keep the `Host` header of the request.
  `tailscale serve` keeps it.
- Use `tailscale serve`, not `tailscale funnel`. Funnel makes the dashboard
  public on the internet.
- The socket refuses daemon commands that belong to the bridge or to the
  daemon itself (see [Protocol](#protocol)).

## Caching

- Each file has an entity tag. The browser checks each file at each load
  (`Cache-Control: no-cache`) and gets `304` when the file did not change.
- There is no service worker. A browser that has the service worker of an
  older build removes the worker and its cache at the next load.

## Protocol

The page and the server talk over one WebSocket (`api/ws`, relative to the
page). Each frame is one JSON text message. This is protocol 2.

### Server frames

|Frame|When|
|---|---|
|`hello {protocol: 2, build, ops}`|First frame on each socket. `build` changes with the eukhe build or a web file|
|`reply {id, data}`|A request succeeded|
|`failure {id, error}`|A request failed. A frame that is not valid gets a failure too (`id` 0 when the frame has no `id`)|
|`event {event, cursor?}`|One event of the bound session. `cursor` is `{generation, sequence}` when the daemon gives a sequence|
|`approval {request}`|The `bash` tool of the bound session asks if one step can run. `request` is `{requestId, step, command, effect}`|
|`resync {reason}`|The bound session closed, moved to a new worker, or lost its worker link. Open it again|
|`unavailable {error}`|The daemon is not available. The server closes the socket next|

### Requests

A request is `{id, op, ...fields}`. The server runs requests at the same time
and answers each one with its `id`. Events do not wait for requests.

|Op|Fields|Reply data|
|---|---|---|
|`sessions`|none|The saved root sessions, newest first: `[{id, path, cwd, title, modified}]`|
|`open`|`sessionId?` or `path?`, `resume?`|`{session: {id, path}, state, summary, messages, cursor, replay}`|
|`new`|`cwd?` (an absolute folder)|As `open`|
|`prompt`|`text`, `mode` (`steer` or `followUp`), `admissionId?`, `images?: [{data, mimeType}]`|`null`|
|`abort`|none|`null`|
|`memory`|`node?: {id, count}`|One level of the chat memory tree|
|`run`|`command`|The data of the daemon's answer|
|`export`|`format` (`html` or `jsonl`)|`{name, mimeType, data}`: the file of the bound session, `data` in base64|
|`delete`|`sessionId`|`{deleted}`: the id of the deleted saved root session|
|`rename`|`sessionId`, `name`|`{renamed, name}`: the worker that hosts the session renames it; with no worker, the saved file is renamed|

- `open` with no `sessionId` and no `path` opens the newest root session. If
  there is no session, it makes a new one.
- `resume` is the `cursor` of the last event that the page has. Then
  `replay` is `complete`, `partial` or `unavailable`. With `complete`,
  `messages` is `null`: the page has all of it. Without `resume`, `replay`
  is `null`.
- The server sends the `open` reply before the events that come after the
  snapshot. It does not send an event that the snapshot already has.
- `prompt` with the same `admissionId` is sent only one time. The server
  makes an id when the page does not send one.
- `export` tells the daemon to write the file into a new private folder
  (mode `0700`) in the temporary folder, reads the file, and removes the
  folder.
- `delete` refuses a session that another client (another tab, the CLI,
  the Signal gateway) has open: `the chat is open in another window: close
  it there first`. Otherwise it stops the worker of the session, if one
  hosts it, and deletes the session. When the tab is bound to the session,
  the tab lets it go first: open another session next.

### `run`

`command` is a daemon command: `type` in snake case and the fields in camel
case, without `activeSessionId`. The server adds the id of the bound session.
It replaces a value that the page sends.

The server runs these commands: the controls and the inspection of the bound
session (model, thinking, service tier, steering and follow-up modes,
auto-compaction, auto-retry, cvars, compaction, retry, queue, `bash` approval
answers, session name, fork, trees, prompts, memory, statistics), and the
catalog commands (`list_saved_sessions`, `rename_saved_session`,
`cron_list`, `heartbeats_list`). The server sends a catalog command without
a session id, so that the daemon answers for all sessions. The list is in
`crates/eukhe-dashboard/src/command_policy.rs`.

The server refuses the other commands with the failure
`the dashboard does not run <type>`. These are the commands that the bridge
does itself (`create`, `attach`, `detach`, `prompt`; `export_html` and
`export_jsonl`, which write to any path that `outputPath` names, so use the
`export` op; `delete_saved_session`, which cannot stop the worker of the
session, so use the `delete` op), worker and supervisor commands, and daemon
commands such as `shutdown`.
