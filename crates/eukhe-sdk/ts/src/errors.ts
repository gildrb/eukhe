/** An eukhe extension (`_eukhe/*`) or ACP capability the SDK calls. */
export type Feature = "run_report" | "budget" | "acceptance" | "undo" | "diff" | "effects" | "model";

/** The command that installs the eukhe release (no root). */
export const INSTALL_COMMAND = "npx eukhe install";

/** The oldest eukhe release the SDK starts: the first that serves `eukhe acp`. */
export const MINIMUM_EUKHE_VERSION = "0.10.81";

/** The command that updates an installed eukhe to the newest release. */
export const UPDATE_COMMAND = "eukhe update";

/** Every error the SDK throws; `error instanceof EukheError` narrows to it, then switch on `$`. */
export type EukheFailure =
  | NotInstalled
  | TooOld
  | NotLoggedIn
  | Unsupported
  | UnknownModel
  | TurnInProgress
  | AgentFailed
  | AgentExited;

/** Base class of {@link EukheFailure}. */
export abstract class EukheError extends Error {
  abstract readonly $: EukheFailure["$"];

  /**
   * `error instanceof EukheError` narrows to the {@link EukheFailure} union, so
   * `switch (error.$)` reaches each failure's fields; `error instanceof TooOld`
   * narrows to that one class.
   */
  static override [Symbol.hasInstance]<T>(
    this: abstract new (...args: never) => T,
    value: unknown,
  ): value is EukheError extends T ? EukheFailure : T {
    return Function.prototype[Symbol.hasInstance].call(this, value);
  }
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

/** The eukhe binary is a release older than {@link MINIMUM_EUKHE_VERSION}; the SDK did not start `eukhe acp` on it. */
export class TooOld extends EukheError {
  readonly $ = "TooOld";
  /** The version the binary reported. */
  readonly found: string;
  readonly minimum: string = MINIMUM_EUKHE_VERSION;
  readonly updateCommand: string = UPDATE_COMMAND;
  constructor(found: string) {
    super(`eukhe ${found} is older than ${MINIMUM_EUKHE_VERSION}, the first release the SDK runs; update it with: ${UPDATE_COMMAND}`);
    this.found = found;
  }
}

/** How a person logs eukhe in to a model provider, as the agent words it. */
export type Login = {
  /** The shell command to run (e.g. `eukhe login anthropic`). */
  command: string;
  /** The same inside an interactive `eukhe`, when there is one. */
  slashCommand: string | null;
  /** One sentence for people. */
  instructions: string;
};

/** eukhe has no model provider login; a person runs `login.command` once. */
export class NotLoggedIn extends EukheError {
  readonly $ = "NotLoggedIn";
  readonly login: Login;
  constructor(login: Login) {
    super(`eukhe has no model provider login: ${login.instructions === "" ? `run ${login.command}` : login.instructions}`);
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
