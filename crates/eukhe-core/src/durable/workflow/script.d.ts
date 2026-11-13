// What surrounds the prelude in a workflow's source (mod.rs `source`): the names the tool
// declares before it, and the `wf.*` host globals behind the script API (globals.rs). The code
// mode sandbox calls a global with one JSON argument and resolves with its JSON answer.

/** The run's `args` text (empty when the call gave none). */
declare const args: string;

/** The run's limits, from its record. */
declare const __wfLimits: Readonly<{
  size: "small" | "medium" | "large";
  concurrency: number;
  maxAgents: number;
}>;

/** The options of one agent; the host refuses other keys and empty strings (`agent_options`). */
type AgentOptions = {
  label?: string;
  phase?: string;
  /** A JSON Schema object the answer follows. */
  schema?: object;
  model?: string;
  effort?: string;
  isolation?: "shared" | "worktree" | "isolated";
};

/** One stage of `pipeline`: the previous stage's value, the item, and the item's index. */
type PipelineStage = (value: unknown, item: unknown, index: number) => unknown;

declare const wf: Readonly<{
  /** Runs (or serves from an earlier run) the agent of the `ordinal`th call. */
  agent(request: {
    ordinal: number;
    /** How many earlier calls had the same prompt and options. */
    occurrence: number;
    prompt: string;
    options: AgentOptions;
  }): Promise<{ result: unknown; cached: boolean }>;
  phase(update: { title: string }): Promise<undefined>;
  log(update: { message: string }): Promise<undefined>;
}>;
