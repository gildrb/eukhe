# Dynamic workflows

One JavaScript orchestration script the agent writes and eukhe runs: starts many subagents at once (up to the size), waits, returns one result; eukhe shows progress.

## Use

```
/dynamic-workflow review every crate for unsafe error handling   # default size
/dynamic-workflow --size large migrate the tests to the new API     # one run, size large
/workflows size                                                     # size picker
/workflows size small                                               # set the default size
/workflows                                                          # this session's runs
```

- `/workflow` = `/dynamic-workflow`. `--size` comes first; after `--size ` the menu lists the sizes.
- Runs in the background; chat goes on. The `workflow` call returns the run id at once.
- Result arrives as `[job-settled job:workflow-<id> status:ok|error|aborted]`, which starts an agent turn.
- `/workflows`: arrows move, Enter opens the agents view, `c` then `y` cancels, Esc closes.
- Chat Esc stops the turn, not the run; cancel on `/workflows`.
- While running: activity dock shows a `workflows` count (Enter opens `/workflows`); the agents block above the composer shows the run (active phase, agents done) and each running agent (`terminal.pinnedAgents`, [settings.md](settings.md)).
- Signal gateway and dashboard send `/dynamic-workflow` as a prompt.

## Sizes

|Size|Agents at once|Agents in total|
|---|---|---|
|`small`|3|5|
|`medium`|6|10|
|`large`|12|25|

- Setting `workflow.size`, default `medium`.
- `subagentMaxConcurrency` caps agents at once; 0 = no cap.
- `agent()` past the total throws `WorkflowBudgetExhausted`; in `parallel`/`pipeline` that slot is `null`.

## Script API

Body of an async function; starts with a pure literal meta:

```js
export const meta = { name: "review", description: "Review the changed files", phases: [{ title: "Scan" }, { title: "Fix" }] };
```

|Global|Effect|
|---|---|
|`agent(prompt, opts?)`|One subagent → final message, parsed object for `schema`, or `null` on failure|
|`parallel(thunks)`|Runs `() => agent(...)` thunks at once, waits for all; a throw → `null`|
|`pipeline(items, ...stages)`|Each item through the stages in order, no waiting between items; `null` stops an item|
|`phase(title)`|Enter a `meta.phases` phase|
|`log(message)`|Line in the run log|
|`args`|Request text|
|`budget`|`{ size, concurrency, maxAgents, spawned() }`|

|`agent()` option|Effect|
|---|---|
|`label`|Name on `/workflows`|
|`phase`|Phase; default the last `phase()`|
|`schema`|JSON Schema; agent ends with a matching JSON block; mismatch: one retry, then `null`|
|`model`|Model|
|`effort`|Thinking level|
|`isolation`|`"worktree"`: copy-on-write workspace copy; changes return at the end|

- `Date` virtual, `Math.random` seeded, no I/O.
- Agents do not see the conversation: put every fact in the prompt.
- The return value goes into the result message: keep it small.

## Resume

- Worker restart resumes: finished agents from the journal, running agents reattach, a cut-off agent runs once more; one result message.
- Start answer and result name the run: `workflow run <id> (<name>)`.
- `resume: "<id>"` on a new run reuses finished agents with unchanged prompt and options; shown `↺`, not counted against the total.

## Limits

- Needs the daemon; `--no-session` refuses the tool.
- Agents are subagents: `rlmMaxDepth` limits depth.
- Agents report to the script, not the conversation.
- Dashboard shows runs, cannot cancel.
