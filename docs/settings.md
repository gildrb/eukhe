# Settings

## Files and layers

Each setting is a console variable (cvar). Its id is the dotted key in
`settings.json`. The value comes from layers. A higher layer wins:

1. The default.
2. `~/.eukhe/settings.json`, then the project `.eukhe/settings.json`.
3. `~/.eukhe/config.cfg`, then the project `.eukhe/config.cfg`.
4. The agent profile: `~/.eukhe/agents/main.cfg` for the root session;
   `~/.eukhe/subagent.cfg`, then `~/.eukhe/agents/<name>.cfg`, for a
   subagent.
5. The sets of the agent while it runs (`/set`, `/toggle`).

The project files obey project trust. A project file never sets a global
setting.

A cfg file has one command list on each line. A `;` separates two
commands. Double quotes keep spaces. `#` starts a comment.

```sh
set compaction.keepRecentTokens 60000
toggle titles.generate
alias quiet "set terminal.streamPace.lag 0; set titles.generate false"
```

Key binds are in `~/.eukhe/binds.cfg`. The first bind of a key wins. User
binds come before the defaults. An empty bind removes a default bind:

```sh
bind ctrl+e "action app.tools.expand"
bind ctrl+o ""
```

|Key|Action|Effect|
|---|---|---|
|Shift+Tab|`app.thinking.cycleForward`|Set the next thinking level that the model offers; after the last level, go to the first|
|Shift+Alt+Tab|`app.thinking.cycleBackward`|Set the previous thinking level that the model offers; before the first level, go to the last|

These keys operate at the prompt only. An open menu or picker uses Shift+Tab
first (the settings menu goes to the previous tab). A model with fewer than
two levels keeps its level, and the status row shows `Current model offers no
other thinking level`. `/effort` shows the levels that the model offers and
marks the current level.

|Command|Effect|
|---|---|
|`/set [--global] <id> <value>`|Set a value for this session; `--global` writes it to `~/.eukhe/config.cfg`|
|`/toggle <id>`|Flip a true/false setting|
|`/alias <name> "<commands>"`|Make `<name>` run the commands|
|`/cvar`|Show the settings that clients see|
|`/cvar save`|Write the session's sets to `~/.eukhe/agents/<name>.cfg`|
|`/reload`|Read `binds.cfg` again|

More settings:

|Key|Default|Effect|
|---|---|---|
|`shell.autoEffects`|`["read", "write", "exec", "net"]`|Effects of a `bash` tool step (and of an `ipython` cell, which is `exec`) that run without approval: `read`, `write`, `exec`, `net`; a write outside the workspace, a protected write and a read or write of a secret always ask; a step with an effect not in the list asks the attached client; no answer is a denial; with only the phone gateway attached it runs at once, but a protected or secret step is refused (no agent or untrusted project can set it)|
|`kernelTransport`|none|Run the Python kernel through a wrapper, e.g. `{"argvPrefix":["docker","exec","-i","box"],"pathMap":[{"sandbox":"/work","host":"/home/me/project"}]}`; `"command":"shell"` for ssh; none runs it as a local process (no agent or untrusted project can set it)|
|`ssh.hosts`|`[]`|Hosts that `ssh://host/path` reads can go to, as written in the URL (`box` or `user@box`); reads only, through your `ssh` and `~/.ssh/config` (global only)|
|`titles.generate`|`true`|Make a session title from the first message with the `tiny` role; a name you gave stays|
|`terminal.streamPace.minChars`|`2`|Fewest streamed characters that one frame shows; `0` reads as 1|
|`terminal.streamPace.lag`|`3`|How far the screen stays behind the stream: each frame shows the backlog divided by `1 + lag`|
|`terminal.showSpeed`|`true`|Show the generation speed on the status line: `prefill <elapsed>s` (or `prefill p/n tokens` from a llama.cpp server), `decode N tok/s`, then `prefill X tok/s (TTFT Ys) · decode Z tok/s` after the reply|
|`terminal.fullscreen`|`true`|Run the interactive surfaces in the alternate screen (a transcript window above the dock, wheel scrolling); `false` runs them inline, with the transcript in the terminal's scrollback|
|`terminal.pinnedAgents`|`collapsed`|The agents block above the composer, shown while a subagent or a job runs: `off`, `collapsed` (three rows and `... N more`), or `full`; with the dock focused (Alt+A), Space expands or collapses it and Enter (or Alt+A again) opens the agents view|
|`terminal.stuckAfterSecs`|`60`|Seconds a running subagent may go without a word (no event, no streamed token, no tool output) before its row in the agents block shows `no activity for ...` in the warning color; `0` turns it off|

## Agents and providers

|Key|Default|Effect|
|---|---|---|
|`subagentMaxConcurrency`|`32`|Subagents that run at one time; `0` is no limit|
|`workflow.size`|`medium`|Default size of a `/dynamic-workflow` run: `small`, `medium` or `large` (see [workflows.md](workflows.md)); `/workflow-size` sets it|
|`subagentStallMs`|`600000`|A subagent with no progress for this long is stopped and reported stalled; `0` takes the default|
|`subagentDefaultModel`|parent model|Model of a subagent spawned without `model`|
|`rlmMaxDepth`|`2`|Maximum subagent depth (global only)|
|`providerMaxInFlight`|none|`{"<provider>": n}`: model requests at one time per provider; `0` is no limit (global only)|
|`providerMaxQueued`|`64`|Requests that wait per provider; the next one fails (global only)|
|`retry.provider.streamIdleTimeoutMs`|`300000`|A model stream with no event for this long fails as stalled; its retry has a note and twice the deadline; `0` is no limit|
|`retry.provider.maxRetryDelayMs`|`60000`|The longest server-requested wait (`Retry-After`) a retry waits out; a longer one fails the request at once and names the server's time (a quota failure parks the session instead)|
|`retry.failover.maxRetries`|`8`|Provider switches one request may make to other providers of the same model that have credentials (a login, a stored or configured API key, or the provider's key in the environment); a provider without credentials never receives a request; each provider is tried once before the request returns to one. When the backups fail too, the error is the first provider's latest error, then `(failover failed too: <provider/model>: <error>; ...)`; only the first provider's quota block parks the session|
|`retry.failover.baseDelayMs`|`1000`|Wait before a request returns to a provider it left; it doubles with each return and is never shorter than that provider's server wait|
|`retry.failover.maxDelayMs`|`30000`|Longest wait before such a return; a provider whose server asks for longer is not tried again in that request|
|`memory.settleTimeoutMs`|`20000`|How long a turn waits for the memory's summaries; then a line not summarized yet shows its message cut to 512 bytes; `0` takes the default|
|`maxToolRounds`|`250`|Tool rounds one turn may make; at the cap the turn ends as failed; `0` takes the default|
|`compaction.keepRecentTokens`|`40000`|Tokens of recent context that compaction keeps; capped per model at half the size where compaction starts|
|`compaction.providerTokenCount`|`false`|Ask the provider's own token counter before the compaction check; one more request per generation; a provider with no counter uses the local estimate|
|`retry.provider.streamRepeatLimit`|`64`|A stream whose last this many lines repeat one line, or a block of up to a quarter of them, stops and retries; `0` takes the default|
|`directors.stackCap`|`8`|Reminders and forced calls that the Director stack holds; `0` takes the default|
|`directors.maxSteps`|`200`|Continuations that one run may make; a new user input resets the count; `0` takes the default|
|`directors.stallSteps`|`3`|Goal continuations in a row that may make no tool call with a new result; at the cap the goal pauses and the transcript tells you why; a new user input or a resume resets the count; `0` takes the default|

The daemon applies the provider limits to all sessions together. The roster
shows a waiting request as `queued` and a running one as `generating`.

## Directors

After each final answer, a stack of Directors can continue the run: the
goal, the autonomous run, reminders and forced tool calls.

|Command|Effect|
|---|---|
|`/remind <text>`|Put `<text>` first in the next continuation; a reminder does not start a continuation|
|`/force <tool> [--tries <n>]`|Make the next requests call `<tool>` until a response calls it; after `n` misses (default `1`) the generation fails|
