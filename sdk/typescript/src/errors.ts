/** An eukhe extension (`_eukhe/*`) or ACP capability the SDK calls. */
export type Feature = "run_report" | "budget" | "acceptance" | "undo" | "diff" | "effects" | "model";

/** The command that installs the eukhe release (no root). */
export const INSTALL_COMMAND = "npx eukhe install";

/** Every error the SDK throws; switch on `$`. */
export type EukheFailure =
  | NotInstalled
  | NotLoggedIn
  | Unsupported
  | UnknownModel
  | TurnInProgress
  | AgentFailed
  | AgentExited;

/** Base class of {@link EukheFailure}: `err instanceof EukheError`, then `err.$`. */
export abstract class EukheError extends Error {
  abstract readonly $: EukheFailure["$"];
}

/** No eukhe binary at the given path, EUKHE_BIN, PATH or ~/.local/bin. */
export class NotInstalled extends EukheError {
  readonly $ = "NotInstalled";
  readonly installCommand: string = INSTALL_COMMAND;
  readonly searched: readonly string[];
  constructor(searched: readonly string[]) {
    super(`eukhe is not installed (looked at ${searched.join(", ")}); install it with: ${INSTALL_COMMAND}`);
    this.searched = searched;
  }
}

/** How a person logs eukhe in to a model provider: run `command`, then type `slashCommand` in it. */
export type Login = { command: string; slashCommand: string | null; instructions: string };

/** eukhe has no model provider login; a person runs `login.command` once (then `login.slashCommand`). */
export class NotLoggedIn extends EukheError {
  readonly $ = "NotLoggedIn";
  readonly login: Login;
  constructor(login: Login) {
    const how = login.slashCommand === null ? login.command : `run ${login.command}, then type ${login.slashCommand}`;
    super(`eukhe has no model provider login; log in once: ${how}${login.instructions === "" ? "" : ` (${login.instructions})`}`);
    this.login = login;
  }
}

/** The agent does not serve `feature` (an older eukhe, or a plain ACP agent). */
export class Unsupported extends EukheError {
  readonly $ = "Unsupported";
  readonly feature: Feature;
  constructor(feature: Feature) {
    super(`the agent does not support ${feature}`);
    this.feature = feature;
  }
}

/** `session({model})` named a model the agent does not offer. */
export class UnknownModel extends EukheError {
  readonly $ = "UnknownModel";
  readonly model: string;
  readonly available: readonly string[];
  constructor(model: string, available: readonly string[]) {
    super(`unknown model ${model}; available: ${available.join(", ")}`);
    this.model = model;
    this.available = available;
  }
}

/** `prompt` was called while another turn of the same session was running. */
export class TurnInProgress extends EukheError {
  readonly $ = "TurnInProgress";
  constructor() {
    super("a turn is already running in this session; wait for it to end or cancel it");
  }
}

/** The agent answered a request with a JSON-RPC error. */
export class AgentFailed extends EukheError {
  readonly $ = "AgentFailed";
  readonly method: string;
  readonly code: number;
  readonly data: unknown;
  constructor(method: string, code: number, message: string, data: unknown) {
    super(`${method} failed (${code}): ${message}`);
    this.method = method;
    this.code = code;
    this.data = data;
  }
}

/** The agent process ended before answering; `stderr` is the end of its error output. */
export class AgentExited extends EukheError {
  readonly $ = "AgentExited";
  readonly exitCode: number | null;
  readonly signal: string | null;
  readonly stderr: string;
  constructor(exitCode: number | null, signal: string | null, stderr: string) {
    super(`eukhe exited (${exitDescription(exitCode, signal)})${stderr === "" ? "" : `: ${stderr}`}`);
    this.exitCode = exitCode;
    this.signal = signal;
    this.stderr = stderr;
  }
}

function exitDescription(exitCode: number | null, signal: string | null): string {
  if (exitCode !== null) return `code ${exitCode}`;
  if (signal !== null) return `signal ${signal}`;
  return "no exit status";
}
