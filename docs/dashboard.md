# Web dashboard

`eukhe dashboard` serves a web app (phone and desktop) for the session you use in the CLI.

- Chat with the newest root session or a selected one; CLI, Signal gateway and each tab share it.
- Live turn: phases, tool calls, tool output, speed.
- Controls: model, thinking level, service tier, queue, compaction, retry, settings (cvars), `bash` approvals.
- Saved sessions: rename, fork, export, delete, new.
- Chat memory as a tree of dated lines, down to each message.

The app and fonts are in the binary; no network loads. Fonts: Inter, Ioskeley Mono (SIL Open Font License; `fonts/inter-OFL.txt`, `fonts/IoskeleyMono-OFL.txt`).

## Change the app

Source: `crates/eukhe-dashboard/ui` (TypeScript, Preact + Radix primitives, StyleX, Vite+). `vp build` writes `crates/eukhe-dashboard/web`, which is committed; `build.rs` embeds every file there, so cargo and Nix builds need no Node.

1. Edit `ui/src` (verbatim files such as fonts, icons: `ui/public`).
2. `make dashboard-ui`: installs locked packages, runs `vp check` (format, lint, types), `vp test run`, `vp build`.
3. Commit `ui/` and `web/` together. CI rebuilds and fails if `web/` differs.

```sh
EUKHE_DASHBOARD=127.0.0.1:<port> npx vp dev  # in ui/: dev server, proxies api/ws to a running dashboard; no Rust build
```

### Tokens

One source for every presentation value: `ui/src/tokens.stylex.ts` (colors, lengths, radii, type, weights, opacities, layers, motion).

- Each color: one value in `lightPalette`, one in `darkPalette`; `colors`, `shadows`, `page` pair them with `light-dark()`; the root's `color-scheme` selects.
- Never repeat a value. Lint rule `eukhe/token-literals` (`ui/lint/tokens.mjs`) fails `vp check` (file, line) on a literal under `ui/src`: color, non-zero length, duration, easing, or a number for z-index, font weight, opacity, line height, Radix offset.
- `global.css` (document root, selection, scroll bars) uses `page` variables (`--page-*`); `src/tokens.test.ts` fails on a literal there.
- `index.html`, `public/manifest.webmanifest`, `public/theme.js` cannot read CSS and repeat the theme color; `src/tokens.test.ts` checks it equals the palette's `bg`.
- `bend/tokens.bend` holds the same tables. `laws/tokens.bend` (T2):
  - each color token has a light and a dark value;
  - both modes: text color vs ground meets minimum contrast (4.5:1 text, 3:1 captions on fills);
  - layers strictly ordered;
  - spacing scale, type sizes, line heights ascend.

  `src/tokens.test.ts` runs `bend/bridge_tokens.bend` and checks its tables equal `tokens.stylex.ts`; skipped without `bend` unless `EUKHE_REQUIRE_BEND` is set.

## Run

```nu
eukhe dashboard  # print the URL, open the browser; Ctrl+C stops; starts a daemon if none runs
```

The URL ends with `#token=<64 hex digits>`: the pairing token ([Pairing](#pairing)).

|Option|Effect|
|---|---|
|`--port <port>`|Listen port. Default: a free port|
|`--no-open`|Print the URL only|
|`--allow-host <name>`|Also accept this host name. Repeatable|
|`--rotate-token`|New pairing token before start; earlier links stop working|
|`--daemon-socket <path>`|Use the daemon on this socket|

## Pairing

No token, no action: a page cannot send a message, approve a `bash` step, change a setting, or read a chat.

- Token: 32 random bytes (256 bits), 64 hex digits, file `dashboard-token` in the agent folder (`~/.eukhe`), mode `0600`. Stable across restarts, so bookmarks work.
- In the URL fragment (`#token=…`), which browsers never send: not in request lines, forwarder logs, or `Referer`.
- The page stores the token in this site's browser storage, removes it from the address bar, never shows it.
- To open the browser, the command writes a small redirect page (mode `0600`) and opens it: the token is not in process arguments visible to other users.
- No or refused token: "Pairing needed". Open the printed link, or paste the link (or token) in the field and select **Pair**.

```nu
eukhe dashboard --rotate-token  # new token, e.g. after losing a phone with the link
```

All earlier tokens die at once, also in a running dashboard: open pages get `unpaired` at their next request and show "Pairing needed".

## Phone (tailscale serve)

The dashboard listens on `127.0.0.1` only. [`tailscale serve`](https://tailscale.com/docs/features/tailscale-serve) gives HTTPS on your tailnet name, reachable only by your tailnet's devices.

```nu
eukhe dashboard --no-open --port 8377 --allow-host box.tail1234.ts.net  # also prints the link for that name
tailscale serve --bg 8377                                              # forward HTTPS
tailscale serve --bg --set-path /eukhe 8377                            # or: mount at a path (app uses relative URLs)
```

- On the phone open `https://box.tail1234.ts.net/#token=…` (or `/eukhe/#token=…`). "Add to Home Screen" installs it; a home-screen app can have its own storage: on "Pairing needed", paste the link.
- `--allow-host` takes the name `tailscale status` shows, without `https://` or port. Without it, requests through `tailscale serve` are refused.

### Phone (poros)

[poros](https://github.com/gildrb/poros) runs the dashboard with its own HTTPS tailnet link; no `--allow-host`:

```nu
poros eukhe dashboard
```

Open the printed `Poros URL` plus the `#token=…` part of the dashboard link. poros sets `Host` to the local address and names the HTTPS link in `X-Forwarded-Host`. The fragment stays in the browser; poros never sees the token.

## Security

> [!WARNING]
> Anyone with the pairing link can message the agent, which runs tools
> with your user permissions. Keep it private; if leaked, run
> `eukhe dashboard --rotate-token`.

- Each WebSocket pairs first: first frame holds the current token. Other first frame, no token, or stale token: `unpaired`, close; no daemon start, connect or command.
- Token rechecked before each frame of a paired socket; after rotation an old socket's next frame gets `unpaired` and closes.
- Constant-time comparison for tokens of the correct length. Token never in a log line, error, or page.
- HTTP routes only serve app files; no actions.
- Listens on `127.0.0.1` only.
- `Host` must be `127.0.0.1`, `localhost`, `[::1]` (any port) or an `--allow-host` name; else `403`. Stops DNS rebinding.
- WebSocket `Origin` must match host and port of `Host`, or of the last `X-Forwarded-Host` a forwarder adds (poros); missing or other origin: `403`. Web pages cannot add `X-Forwarded-Host` to an upgrade, so other pages cannot use the socket.
- CSP: only the app's own scripts, styles, fonts, workers, manifest, socket; images also `data:`, `blob:`. No inline script or style.
- `--allow-host` only for a forwarder you control that keeps `Host` (`tailscale serve` does).
- `tailscale serve`, never `tailscale funnel` (public internet).
- The socket refuses bridge and daemon-internal commands ([Protocol](#protocol)).
- `laws/dash.bend`: pairing gate rules; `PROOF.bend` proves them on `bend/dash.bend`. Bridge test `pairing::tests::the_gate_pairs_as_its_model` runs real server and model on the same events.

## Caching

- Entity tag per file; `Cache-Control: no-cache`: checked each load, `304` if unchanged.
- No service worker; an older build's worker and cache are removed at the next load.

## Protocol

One WebSocket (`api/ws`, relative to the page); each frame one JSON text message. Protocol 3.

### Pairing frames

Page's first frame: `{op: "pair", token}` (token from the link). Answer:

|Frame|When|
|---|---|
|`hello {protocol: 3, build, ops}`|Token current; requests can follow|
|`unpaired {error}`|First frame not a pairing, no token, or stale token. Socket closes next. Nothing ran|

10 seconds to pair. Later, any frame with a stale token gets `unpaired`; socket closes.

### Server frames

|Frame|When|
|---|---|
|`hello {protocol: 3, build, ops}`|First frame after pairing. `build` changes with the eukhe build or a web file|
|`reply {id, data}`|Request succeeded|
|`failure {id, error}`|Request failed; also an invalid frame (`id` 0 if none)|
|`event {event, cursor?}`|One bound-session event. `cursor` = `{generation, sequence}` when the daemon gives a sequence|
|`approval {request}`|Bound session's `bash` asks to run one step. `request` = `{requestId, step, command, effects}`; `effects` ⊆ `read`, `write`, `exec`, `net`, `outside`, `protected`, `secret`|
|`resync {reason}`|Bound session closed, moved worker, or lost its worker link. Reopen|
|`unavailable {error}`|Daemon unavailable. Socket closes next|
|`unpaired {error}`|Token rotated. Nothing ran. Socket closes next|

### Requests

`{id, op, ...fields}`. Requests run concurrently; each answer carries its `id`. Events never wait for requests.

|Op|Fields|Reply data|
|---|---|---|
|`sessions`|none|Saved root sessions, newest first: `[{id, path, cwd, title, modified}]`|
|`open`|`sessionId?` or `path?`, `resume?`|`{session: {id, path}, state, summary, messages, cursor, replay}`|
|`new`|`cwd?` (absolute folder)|As `open`|
|`prompt`|`text`, `mode` (`steer` or `followUp`), `admissionId?`, `images?: [{data, mimeType}]`|`null`|
|`abort`|none|`null`|
|`memory`|`node?: {id, count}`|One level of the chat memory tree|
|`run`|`command`|The daemon answer's data|
|`export`|`format` (`html` or `jsonl`)|`{name, mimeType, data}`: bound session's file, `data` base64|
|`delete`|`sessionId`|`{deleted}`: id of the deleted saved root session|
|`rename`|`sessionId`, `name`|`{renamed, name}`: the hosting worker renames it; with no worker, the saved file is renamed|

- `open` without `sessionId`/`path`: newest root session; none exists: a new one.
- `resume` = cursor of the page's last event; then `replay` is `complete` (`messages` `null`), `partial` or `unavailable`. Without `resume`, `replay` is `null`.
- The `open` reply precedes post-snapshot events; events in the snapshot are not resent.
- `prompt` with the same `admissionId` is sent once; the server makes an id if the page sends none.
- `export`: the daemon writes into a new private temp folder (mode `0700`); the server reads the file, removes the folder.
- `delete` refuses a session open in another client (tab, CLI, Signal gateway): `the chat is open in another window: close it there first`. Else stops its worker, if any, and deletes it. A tab bound to it releases it first; open another session next.

### `run`

`command`: a daemon command, `type` in snake case, fields in camel case, no `activeSessionId` (the server sets the bound session's id, overriding the page).

Allowed (list: `crates/eukhe-dashboard/src/command_policy.rs`):

- bound-session controls and inspection: model, thinking, service tier, steering and follow-up modes, auto-compaction, auto-retry, cvars, compaction, retry, queue, `bash` approval answers, session name, fork, trees, prompts, memory, statistics;
- catalog commands `list_saved_sessions`, `rename_saved_session`, `cron_list`, `heartbeats_list`, sent without session id (daemon answers for all sessions).

Refused with `the dashboard does not run <type>`:

- bridge-owned: `create`, `attach`, `detach`, `prompt`;
- `export_html`, `export_jsonl` (write to any `outputPath`; use `export`);
- `delete_saved_session` (cannot stop the worker; use `delete`);
- worker, supervisor and daemon commands such as `shutdown`.
