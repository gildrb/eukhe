# The `workflow` tool

Arguments: `script` (the JavaScript below), `args` (the user's request, given to the script as `args`), `size` (`small`, `medium`, or `large`; default: the `workflow.size` setting), `resume` (the run id of an earlier run whose finished agents to reuse).

## Script

The script is the body of an async function: top-level `await` and `return` work. It must start with a pure literal meta (no variables, calls, or template substitutions):

```js
export const meta = { name: "review", description: "Review the changed files", phases: [{ title: "Scan" }, { title: "Verify" }] };
```

API (globals):

- `agent(prompt, opts?) -> Promise<string | object | null>`: run one subagent with `prompt` and return its final message. `opts`: `label` (short roster name), `phase` (phase title; default: the current `phase()`), `schema` (a JSON Schema object: the agent must end with a matching JSON block, the call returns the parsed object), `model` (model id), `effort` (thinking level), `scope` (the files and directories the agent writes). Returns `null` when the agent fails, is cancelled, or misses the schema after one retry. Throws `WorkflowBudgetExhausted` when the run already spawned `budget.maxAgents` agents.
  - Without `scope`: a read-only agent (reads, runs read-only commands, reports); its writes are refused.
  - With `scope`: a writing agent. It returns `{ result, conflicts }`: `result` as above, `conflicts` the paths it changed outside its scope (or that changed under it); those changes are kept apart, never applied. A `scope` that names no file is refused: `a writing agent needs its files`.
- `parallel(thunks) -> Promise<array>`: run `() => agent(...)` thunks at once (a barrier). A thunk that throws gives `null` in its slot; its error is listed under `Problems` in the result message.
- `pipeline(items, ...stages) -> Promise<array>`: pass each item through the stages in order, with no barrier between stages: item 1 can be in stage 3 while item 2 is in stage 1. A stage gets `(value, item, index)`; a `null` value or a throw stops that item with `null` (a throw is listed under `Problems`).
- `phase(title)`: enter a phase of `meta.phases` (the view marks earlier phases done).
- `log(message)`: add a line to the run's log in `/workflows`.
- `args`: the request string. `budget`: `{ size, concurrency, maxAgents, writers, spawned() }`.
- `return value`: the JSON value the result message carries back to you.

Rules:

- At most `budget.concurrency` read-only agents run at once; more calls wait for a slot. At most `budget.maxAgents` agents per run; the calls past it throw `WorkflowBudgetExhausted`.
- Writing agents called in the same turn of the script (one `parallel()`, the first stage of one `pipeline()`) start together as one group; they take no `budget.concurrency` slot. Before any of them starts, the whole group is checked and refused together when one check fails: two agents share a file (`the writing agents started together must name disjoint files`), a path lies outside this session's scope or in a running batch, or the group would pass `budget.maxAgents`.
- A batch is a balanced binary tree over at most `budget.writers` writing agents: the harness merges each pair's changes, and each agent's changes land in its scope. A larger group starts in waves: each next batch starts as soon as the agent tree has room. `budget.writers` is `0` where this session writes no files.
- The result message lists under `Problems` each failed agent and each error that `parallel()` or `pipeline()` turned into `null`, with its reason.
- Keep shared files (lockfiles, `mod.rs`, index files, generated code) out of every agent's scope; edit them after the batch.
- Deterministic: `Date` is virtual and `Math.random` is seeded; there is no I/O except `agent()`. Do not branch on time.
- Agents do not see each other or this conversation: put every fact an agent needs in its prompt (paths, the request, earlier results).
- Check every result for `null` before using it.
- Prefer `pipeline` when items flow through stages independently; use `parallel` when a later step needs all results.
- Ask for structure with `schema` when the script must read fields; otherwise use the text.
- Keep the return value small: summaries, decisions, and paths, not raw transcripts.
- Do not declare your own `agent`, `parallel`, `pipeline`, `phase`, `log`, `args`, `budget`, or `meta`.

## Examples

Pipeline of research, write, verify:

```js
export const meta = { name: "docs", description: "Research, write, then verify each topic", phases: [{ title: "Research" }, { title: "Write" }, { title: "Verify" }] };
const topics = ["install", "usage", "limits"];
const done = await pipeline(topics,
  (topic) => agent(`Collect the facts for the ${topic} section from the code.`, { label: `research ${topic}`, phase: "Research" }),
  (facts, topic) => agent(`Write the ${topic} section from these facts:\n${facts}`, { label: `write ${topic}`, phase: "Write" }),
  (draft, topic) => agent(`Check this ${topic} section against the code; return the corrected text:\n${draft}`, { label: `verify ${topic}`, phase: "Verify" }));
return topics.map((topic, i) => ({ topic, text: done[i] }));
```

Phased plan, implement, verify:

```js
export const meta = { name: "change", description: "Plan, implement in parts, verify", phases: [{ title: "Plan" }, { title: "Implement" }, { title: "Verify" }] };
phase("Plan");
const plan = await agent(`Plan this change as independent parts on disjoint files: ${args}`, {
  label: "planner",
  schema: { type: "object", required: ["parts"], properties: { parts: { type: "array", items: { type: "object", required: ["task", "files"], properties: { task: { type: "string" }, files: { type: "array", items: { type: "string" } } } } } } },
});
if (plan === null) return "planning failed";
phase("Implement");
const parts = await parallel(plan.parts.map((part, i) => () => agent(`Implement: ${part.task}`, { label: `part ${i + 1}`, scope: part.files })));
phase("Verify");
const verdict = await agent(`Build and test the change. Parts:\n${plan.parts.map((p) => p.task).join("\n")}`, { label: "verifier" });
log(`${parts.filter((p) => p !== null).length}/${parts.length} parts done`);
return { parts: parts.map((p) => (p === null ? "failed" : { done: true, conflicts: p.conflicts })), verdict };
```

## Resume

After a failed or changed run, call again with `resume: "<run id>"` (the id is in the start answer and the result message; a result message with failures says how many agents a resume reuses): agents whose prompt and options did not change return their earlier answer without a new spawn.
