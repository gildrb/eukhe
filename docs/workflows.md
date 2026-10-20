# Dynamic workflows

A dynamic workflow is one JavaScript orchestration script that the agent writes and eukhe runs. The script starts many subagents, waits for them, and returns one result.

PROBLEM: a task splits into many independent agent tasks. One agent does them one after another, or you start and track each subagent by hand.

SOLUTION: the agent writes the plan as a short deterministic script. eukhe runs the agents of the script at once, up to the size you select, and shows the progress.

## Use

```
/dynamic-workflow review every crate for unsafe error handling   # the default size
/dynamic-workflow --size large migrate the tests to the new API     # one run of size large
/workflow-size                                                      # open the size picker
/workflow-size small                                                # set the default size
/workflows                                                          # show the runs of this session
```

- `/workflow` is an alias of `/dynamic-workflow`.
- `--size` must come first.
- The agent answers when the script ends. The `workflow` tool call blocks the turn until then.
- On the `/workflows` page: the arrows move over the agents, Enter opens the agents view, `c` then `y` cancels the run, Esc closes.
- The activity dock shows a `workflows` count while a run runs. Enter on it opens `/workflows`.
- The Signal gateway and the dashboard send `/dynamic-workflow` to the session as a prompt.

## Sizes

|Size|Agents at once|Agents in total|
|---|---|---|
|`small`|3|5|
|`medium`|6|10|
|`large`|12|25|

- The setting is `workflow.size` (default `medium`).
- `subagentMaxConcurrency` caps the agents at once. A cap of 0 is no cap.
- An `agent()` call past the total throws `WorkflowBudgetExhausted`. In `parallel` or `pipeline` that slot is `null`.

## Script API

The script is the body of an async function. It starts with a pure literal meta:

```js
export const meta = { name: "review", description: "Review the changed files", phases: [{ title: "Scan" }, { title: "Fix" }] };
```

|Global|Effect|
|---|---|
|`agent(prompt, opts?)`|Runs one subagent. Returns its final message, the parsed object for a `schema`, or `null` on a failure|
|`parallel(thunks)`|Runs `() => agent(...)` thunks at once and waits for all. A throw gives `null`|
|`pipeline(items, ...stages)`|Runs each item through the stages in order. Items do not wait for each other between stages. `null` stops an item|
|`phase(title)`|Enters a phase of `meta.phases`|
|`log(message)`|Adds a line to the run's log|
|`args`|The request text|
|`budget`|`{ size, concurrency, maxAgents, spawned() }`|

`agent()` options:

|Option|Effect|
|---|---|
|`label`|The agent's name on `/workflows`|
|`phase`|The agent's phase. Default: the last `phase()`|
|`schema`|A JSON Schema object. The agent ends with a matching JSON block. A mismatch gets one retry, then `null`|
|`model`|The agent's model|
|`effort`|The agent's thinking level|
|`isolation`|`"worktree"`: the agent works in a copy-on-write copy of the workspace. Its changes come back when it ends|

Rules:

- `Date` is virtual. `Math.random` is seeded. The script has no I/O.
- Agents do not see the conversation. Put every fact in the prompt.
- The return value is the tool result. Keep it small.

## Resume

- A worker restart resumes the run. Finished agents come from the journal. Running agents reattach.
- The tool result names the run id: `workflow run <id> (<name>): <state>`.
- A new run with `resume: "<id>"` reuses every finished agent whose prompt and options did not change. Reused agents show `↺` and do not count against the total.

## Limits

- Dynamic workflows need the eukhe daemon. A `--no-session` run refuses the tool.
- Agents are subagents: `rlmMaxDepth` limits how deep a workflow can start one.
- Agents report to the script, not to the conversation.
- The dashboard shows runs but cannot cancel them.
