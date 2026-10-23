# Settings

## Files and layers

Each setting is a console variable (cvar); id = dotted key in `settings.json`. Layers, higher wins:

1. Default.
2. `~/.eukhe/settings.json`, then project `.eukhe/settings.json`.
3. `~/.eukhe/config.cfg`, then project `.eukhe/config.cfg`.
4. Agent profile: root `~/.eukhe/agents/main.cfg`; subagent `~/.eukhe/subagent.cfg`, then `~/.eukhe/agents/<name>.cfg`.
5. The agent's runtime sets (`/set`, `/toggle`).

Project files obey project trust and never set a global setting.

cfg: one command list per line; `;` separates; double quotes keep spaces; `#` comments.

```sh
set compaction.keepRecentTokens 60000
toggle titles.generate
alias quiet "set terminal.streamPace.lag 0; set titles.generate false"
```

Binds: `~/.eukhe/binds.cfg`. First bind of a key wins; user binds precede defaults; an empty bind removes a default.

```sh
bind ctrl+e "action app.tools.expand"
bind ctrl+o ""
```

|Key|Action|Effect|
|---|---|---|
|Shift+Tab|`app.thinking.cycleForward`|Next thinking level of the model; wraps to the first|
|Shift+Alt+Tab|`app.thinking.cycleBackward`|Previous level; wraps to the last|

- Prompt only; an open menu or picker takes Shift+Tab first (settings menu: previous tab).
- Model with fewer than two levels: level kept; status row shows `Current model offers no other thinking level`.
- `/effort` lists the model's levels, current marked.

|Command|Effect|
|---|---|
|`/set [--global] <id> <value>`|Set for this session; `--global` writes `~/.eukhe/config.cfg`|
|`/toggle <id>`|Flip a boolean|
|`/alias <name> "<commands>"`|`<name>` runs the commands|
|`/cvar`|Settings clients see|
|`/cvar save`|Write the session's sets to `~/.eukhe/agents/<name>.cfg`|
|`/reload`|Reread `binds.cfg`|

More settings:

|Key|Default|Effect|
|---|---|---|
|`shell.autoEffects`|`["read", "write", "exec", "net"]`|Effects of a `bash` step (an `ipython` cell is `exec`) that run without approval. Always ask: write outside the workspace, protected write, secret read or write. Effect not listed: asks the attached client; no answer = deny. Only the phone gateway attached: runs at once, but protected or secret steps are refused. Not settable by an agent or untrusted project|
|`kernelTransport`|none|Python kernel via a wrapper, e.g. `{"argvPrefix":["docker","exec","-i","box"],"pathMap":[{"sandbox":"/work","host":"/home/me/project"}]}`; `"command":"shell"` for ssh; none = local process. Not settable by an agent or untrusted project|
|`ssh.hosts`|`[]`|Hosts `ssh://host/path` reads may reach, as in the URL (`box`, `user@box`); read-only, via your `ssh` and `~/.ssh/config` (global only)|
|`titles.generate`|`true`|Title from the first message via the `tiny` role; a name you gave stays|
|`terminal.streamPace.minChars`|`2`|Min streamed characters per frame; `0` = 1|
|`terminal.streamPace.lag`|`3`|Each frame shows backlog / (`1 + lag`)|
|`terminal.showSpeed`|`true`|Status-line speed: `prefill <elapsed>s` (or `prefill p/n tokens` from llama.cpp), `decode N tok/s`, after the reply `prefill X tok/s (TTFT Ys) · decode Z tok/s`|
|`terminal.fullscreen`|`true`|Alternate screen (transcript window above the dock, wheel scrolling); `false` = inline, transcript in scrollback|
|`terminal.pinnedAgents`|`collapsed`|Agents block above the composer while a subagent or job runs: `off`, `collapsed` (three rows + `... N more`), `full`. Dock focused (Alt+A): Space expands/collapses; Enter (or Alt+A) opens the agents view|
|`terminal.stuckAfterSecs`|`60`|Seconds without activity (event, token, tool output) before a running subagent's row shows `no activity for ...` in warning color; `0` off|

## Agents and providers

|Key|Default|Effect|
|---|---|---|
|`subagentMaxConcurrency`|`32`|Concurrent subagents; `0` no limit|
|`workflow.size`|`medium`|Default `/dynamic-workflow` size: `small`, `medium`, `large` ([workflows.md](workflows.md)); `/workflow-size` sets it|
|`subagentStallMs`|`600000`|No progress this long: subagent stopped, reported stalled; `0` default|
|`subagentDefaultModel`|parent model|Model of a subagent spawned without `model`|
|`rlmMaxDepth`|`2`|Max subagent depth (global only)|
|`providerMaxInFlight`|none|`{"<provider>": n}` concurrent model requests per provider; `0` no limit (global only)|
|`providerMaxQueued`|`64`|Waiting requests per provider; the next fails (global only)|
|`retry.provider.streamIdleTimeoutMs`|`300000`|Stream silent this long fails as stalled; retry gets a note and twice the deadline; `0` no limit|
|`retry.provider.maxRetryDelayMs`|`60000`|Longest server-requested wait (`Retry-After`) a retry honors; longer fails at once naming the server's time (quota failure parks the session instead)|
|`retry.failover.maxRetries`|`8`|Switches per request to other providers of the same model with credentials (login, stored or configured API key, provider key in env); no credentials = never called; each provider tried once before returning to one. All backups fail (error, or deferred `pending`): error = first provider's latest error + `(failover to <provider/model> failed too: <error>; ...)`; only the first provider's quota block parks the session|
|`retry.failover.baseDelayMs`|`1000`|Wait before returning to a left provider; doubles per return; never below that provider's server wait|
|`retry.failover.maxDelayMs`|`30000`|Max such wait; a provider asking longer is not retried in that request|
|`memory.settleTimeoutMs`|`20000`|Turn waits this long for memory summaries; then unsummarized lines show their message cut to 512 bytes; `0` default|
|`maxToolRounds`|`250`|Tool rounds per turn; at the cap the turn fails; `0` default|
|`compaction.keepRecentTokens`|`40000`|Recent tokens compaction keeps; capped per model at half the compaction threshold|
|`compaction.providerTokenCount`|`false`|Use the provider's token counter before the compaction check (one more request per generation); no counter = local estimate|
|`retry.provider.streamRepeatLimit`|`64`|Stream whose last N lines repeat one line, or a block up to N/4 lines, stops and retries; `0` default|
|`directors.stackCap`|`8`|Reminders and forced calls the Director stack holds; `0` default|
|`directors.maxSteps`|`200`|Continuations per run; new user input resets; `0` default|
|`directors.stallSteps`|`3`|Consecutive goal continuations without a tool call with a new result; at the cap the goal pauses and the transcript says why; new user input or resume resets; `0` default|

Provider limits are daemon-wide across sessions. Roster: waiting request `queued`, running `generating`.

## Directors

After each final answer a Director stack can continue the run: goal, autonomous run, reminders, forced tool calls.

|Command|Effect|
|---|---|
|`/remind <text>`|Put `<text>` first in the next continuation; does not start one|
|`/force <tool> [--tries <n>]`|Next requests must call `<tool>` until one does; after `n` misses (default `1`) the generation fails|
