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
   `vp check` (format, lint, types), `vp test run` and `vp build`.
3. Commit `ui/` and `web/` together. CI rebuilds the app and fails when
   `web/` differs from the build.

To see changes without a Rust build, run `npx vp dev` in `ui/` with
`EUKHE_DASHBOARD=127.0.0.1:<port>` naming a running dashboard: the dev
server proxies `api/ws` to it.

### Tokens

Each presentation value has one source: `ui/src/tokens.stylex.ts`. This
includes colors, lengths, radii, type, weights, opacities, layers and
motion.

- Each color has one value in `lightPalette` and one in `darkPalette`.
  `colors`, `shadows` and `page` pair them with `light-dark()`. The root's
  `color-scheme` selects the value.
- Other files use the tokens. Do not write a value again. The lint rule
  `eukhe/token-literals` (`ui/lint/tokens.mjs`) fails `vp check` when a
  file under `ui/src` contains one of these literals: a color, a length that
  is not zero, a duration, an easing, or a number for a z-index, a font
  weight, an opacity, a line height or a Radix offset. The message gives
  the file and the line.
- `global.css` styles the document root, the selection and the scroll bars.
  It uses the `page` variables (`--page-*`). `src/tokens.test.ts` fails when
  `global.css` contains a literal.
- `index.html`, `public/manifest.webmanifest` and `public/theme.js` cannot
  read CSS. They contain the theme color again. `src/tokens.test.ts` makes
  sure that this color is the palette's `bg`.
- `bend/tokens.bend` holds the same tables. `laws/dashboard_tokens.bend`
  (T2) states the rules for them:
  - each color token has a light value and a dark value;
  - in both modes, each text color and the ground under it have a minimum
    contrast (4.5:1 for text, 3:1 for captions on fills);
  - the layers are in a strict order;
  - the spacing scale, the type sizes and the line heights go up.

  `src/tokens.test.ts` runs `bend/bridge_tokens.bend` and makes sure that
  its tables are the same as `tokens.stylex.ts`. When `bend` is not
  installed, the test is skipped, unless `EUKHE_REQUIRE_BEND` is set.

## Run

```nu
eukhe dashboard
```

The command prints the URL and opens it in the browser. Stop it with Ctrl+C.
The URL ends with `#token=<64 hex digits>`: this is the pairing token (see
[Pairing](#pairing)).

|Option|Effect|
|---|---|
|`--port <port>`|Listen on this port. Default: a free port|
|`--no-open`|Print the URL. Do not open the browser|
|`--allow-host <name>`|Also accept requests for this host name. You can give it more than one time|
|`--rotate-token`|Make a new pairing token before the dashboard starts. All earlier links stop working|
|`--daemon-socket <path>`|Use the daemon on this socket|

If no daemon runs, the dashboard starts one.

## Pairing

A browser must have the pairing token before the dashboard does an action
for it. Without the token, a page cannot send a message, approve a `bash`
step, change a setting, or read a chat.

- The token is 32 random bytes (256 bits), written as 64 hex digits. It is
  in the file `dashboard-token` in the agent folder (`~/.eukhe`), with mode
  `0600`. The token stays the same when you start the dashboard again, so a
  bookmark of the link continues to work.
- The URL that `eukhe dashboard` prints has the token in its fragment
  (`#token=…`). A browser does not send the fragment to a server, so the
  token is not in a request line, a forwarder log, or a `Referer` header.
- The page reads the token, keeps it in the storage of the browser for
  this site, and removes it from the address bar. The page does not show
  the token.
- To open the browser, the command writes a small page (mode `0600`) that
  goes to the URL, and opens that page. The token is thus not in the
  arguments of a process, which other users of the computer can see.
- If a page has no token, or the dashboard refuses its token, the page
  shows "Pairing needed". Open the link that `eukhe dashboard` prints, or
  paste the link (or only the token) in the field and select **Pair**.

To make a new token, for example after you lose a phone that has the link:

```nu
eukhe dashboard --rotate-token
```

All earlier tokens stop working at once, also in a dashboard that runs at
that time: its open pages get `unpaired` at their next request and show
"Pairing needed".

## Phone (tailscale serve)

The dashboard listens on `127.0.0.1` only. To use it on a phone, use
[`tailscale serve`](https://tailscale.com/docs/features/tailscale-serve). It
gives HTTPS on your tailnet name, and only the devices of your tailnet can
connect.

1. Start the dashboard on a fixed port. Give it your tailnet name:

   ```nu
   eukhe dashboard --no-open --port 8377 --allow-host box.tail1234.ts.net
   ```

   It prints the link for that name too, with the token.

2. Forward HTTPS to it:

   ```nu
   tailscale serve --bg 8377
   ```

   To share the name with other services, mount the dashboard at a path
   (`tailscale serve --bg --set-path /eukhe 8377`). The app uses relative
   URLs only, so it works under a path.

3. On the phone, open `https://box.tail1234.ts.net/#token=…` (or
   `/eukhe/#token=…`) with the token that the dashboard printed. To install
   it as an app, use "Add to Home Screen". An app on the home screen can
   have its own storage: if it shows "Pairing needed", paste the link in
   its field.

Use the name that `tailscale status` shows for this computer, without
`https://` and without a port. Without `--allow-host`, the dashboard refuses
the requests that come through `tailscale serve`.

### Phone (poros)

[poros](https://github.com/gildrb/poros) runs the dashboard and gives it its
own HTTPS link on your tailnet. It needs no `--allow-host`:

```nu
poros eukhe dashboard
```

Open the `Poros URL` that it prints, and add the `#token=…` part of the
dashboard's link to it. poros sends each request to the dashboard with
`Host` set to the local address, and it names the HTTPS link in
`X-Forwarded-Host`. The fragment stays in the browser, so poros does not
see the token.

## Security

> [!WARNING]
> A person who has the pairing link can send messages to the agent, and
> the agent runs tools on this computer with your user permissions. Keep
> the link private. If you think that another person has it, run
> `eukhe dashboard --rotate-token`.

- Each WebSocket must pair first: its first frame must hold the current
  token. A socket that sends another frame first, no token, or a token
  that is not current gets `unpaired` and closes. The dashboard does not
  start a daemon, connect to it, or run a command for that socket.
- The dashboard examines the token again before each frame of a paired
  socket. After a rotation, the next frame of an old socket gets
  `unpaired`, and the socket closes.
- The comparison takes the same time for each token of the correct length.
  The token is not in a log line, an error, or the page.
- The HTTP routes only send the files of the app. They do no actions.
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
- `laws/dashboard_auth.bend` states the rules of the pairing gate, and
  `PROOF.bend` proves them on the model `bend/dash.bend`. The bridge test
  `pairing::tests::the_gate_pairs_as_its_model` runs the real server and
  the model on the same events and compares the results.

## Caching

- Each file has an entity tag. The browser checks each file at each load
  (`Cache-Control: no-cache`) and gets `304` when the file did not change.
- There is no service worker. A browser that has the service worker of an
  older build removes the worker and its cache at the next load.

## Protocol

The page and the server talk over one WebSocket (`api/ws`, relative to the
page). Each frame is one JSON text message. This is protocol 3.

### Pairing frames

The first frame of the page must be `{op: "pair", token}`, with the token
from the link. The server answers with one of these frames:

|Frame|When|
|---|---|
|`hello {protocol: 3, build, ops}`|The token is current. Requests can follow|
|`unpaired {error}`|The first frame is not a pairing, has no token, or has a token that is not current. The server closes the socket next. Nothing ran|

The page has 10 seconds to send the pairing frame. Later, a frame of the
page while its token is not current also gets `unpaired`, and the server
closes the socket.

### Server frames

|Frame|When|
|---|---|
|`hello {protocol: 3, build, ops}`|First frame after the pairing. `build` changes with the eukhe build or a web file|
|`reply {id, data}`|A request succeeded|
|`failure {id, error}`|A request failed. A frame that is not valid gets a failure too (`id` 0 when the frame has no `id`)|
|`event {event, cursor?}`|One event of the bound session. `cursor` is `{generation, sequence}` when the daemon gives a sequence|
|`approval {request}`|The `bash` tool of the bound session asks if one step can run. `request` is `{requestId, step, command, effects}`; `effects` is the list of the step's effects (`read`, `write`, `exec`, `net`, `outside`, `protected`, `secret`)|
|`resync {reason}`|The bound session closed, moved to a new worker, or lost its worker link. Open it again|
|`unavailable {error}`|The daemon is not available. The server closes the socket next|
|`unpaired {error}`|The token of the socket is not current any more (a rotation). Nothing ran. The server closes the socket next|

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
