// What surrounds the prelude in a workflow's source (mod.rs `source`): the names the tool
// declares before it, and the `wf.*` host globals behind the script API (globals.rs). The code
// mode sandbox calls a global with one JSON argument and resolves with its JSON answer.

/** The run's `args` text (empty when the call gave none). */
declare const args: string;

/** The run's limits, from its record; `writers`: the most writing agents one batch holds (0: this session writes none). */
declare const __wfLimits: Readonly<{
  size: "small" | "medium" | "large";
  concurrency: number;
  maxAgents: number;
  writers: number;
}>;

/** The options of one agent; the host refuses other keys and empty strings (`agent_options`). */
type AgentOptions = {
  label?: string;
  phase?: string;
  /** A JSON Schema object the answer follows. */
  schema?: object;
  model?: string;
  effort?: string;
  /** The files and directories a writing agent writes; none: a read-only agent. */
  scope?: string[];
};

/** One stage of `pipeline`: the previous stage's value, the item, and the item's index. */
type PipelineStage = (value: unknown, item: unknown, index: number) => unknown;

/** One `agent()` call as the host reads it. */
type AgentRequest = {
  ordinal: number;
  /** How many earlier calls had the same prompt and options. */
  occurrence: number;
  prompt: string;
  options: AgentOptions;
};

/** What the host answers for one agent. */
type AgentAnswer = { result: unknown; cached: boolean };

/** A writing agent waiting for its batch to start. */
type AgentWriter = {
  request: AgentRequest;
  resolve: (answer: AgentAnswer) => void;
  reject: (error: unknown) => void;
};

declare const wf: Readonly<{
  /**
   * Checks the writing agents called together as one group (files, scopes, `maxAgents`), all or none,
   * then starts the longest first run of them one batch of the agent tree holds. `writing`: the run's
   * writing agents still running (none: a tree without room refuses the group). `deferred`: the
   * ordinals that wait for a later wave (empty: every agent started or has its answer).
   */
  batch(request: { agents: AgentRequest[]; writing: number }): Promise<{ deferred: number[] }>;
  /** Runs (or serves from an earlier run) the agent of the `ordinal`th call. */
  agent(request: AgentRequest): Promise<AgentAnswer>;
  phase(update: { title: string }): Promise<undefined>;
  log(update: { message: string }): Promise<undefined>;
  /** Records why part of the run became `null` or threw: the run's log and its report's problems. */
  problem(update: { message: string }): Promise<undefined>;
}>;
