import { AgentProcess } from "./agent.ts";
import { findEukhe, type Env } from "./discover.ts";
import type { Extensions } from "./extensions.ts";
import { Session, type SessionOptions } from "./session.ts";

/** Options of {@link Eukhe.start}. */
export type StartOptions = {
  /** The project directory sessions work in. */
  cwd: string;
  /** The eukhe binary; EUKHE_BIN, PATH, then ~/.local/bin/eukhe otherwise. */
  bin?: string;
  /** Extra environment for the agent process (merged over process.env). */
  env?: Env;
};

/** A running eukhe agent: opens sessions in one project directory. */
export class Eukhe {
  /** The binary in use. */
  readonly bin: string;
  readonly cwd: string;
  /** eukhe's version (ACP `agentInfo.version`). */
  readonly version: string;
  /** The `_eukhe/*` extensions the agent serves. */
  readonly extensions: Extensions;
  readonly #env: Env;
  /** Agent processes: the one `start` checked, until a session takes it, and every session's. */
  readonly #processes: { spare: AgentProcess | null; live: Set<AgentProcess> };

  private constructor(options: StartOptions & { bin: string; env: Env }, first: AgentProcess) {
    this.bin = options.bin;
    this.cwd = options.cwd;
    this.#env = options.env;
    this.version = first.init.agentInfo?.version ?? "unknown";
    this.extensions = first.extensions;
    this.#processes = { spare: first, live: new Set([first]) };
  }

  /**
   * Find the eukhe binary and start its ACP agent (`eukhe acp`).
   * Throws `NotInstalled` when no binary is found.
   */
  static async start(options: StartOptions): Promise<Eukhe> {
    const env = { ...options.env };
    const bin = await findEukhe(options.bin, { ...process.env, ...env });
    const first = await AgentProcess.launch(bin, options.cwd, env);
    return new Eukhe({ ...options, bin, env }, first);
  }

  /**
   * Open a new session. Each session runs in its own agent process.
   * Throws `NotLoggedIn` when eukhe has no model provider login, `UnknownModel` for a model it does not offer.
   */
  async session(options: SessionOptions = {}): Promise<Session> {
    const agent = this.#processes.spare ?? (await AgentProcess.launch(this.bin, this.cwd, this.#env));
    this.#processes.spare = null;
    this.#processes.live.add(agent);
    try {
      return await Session.open(agent, this.cwd, options);
    } catch (error) {
      this.#processes.live.delete(agent);
      await agent.close();
      throw error;
    }
  }

  /** End every session and agent process this instance started. */
  async close(): Promise<void> {
    const processes = [...this.#processes.live];
    this.#processes.live.clear();
    this.#processes.spare = null;
    await Promise.all(processes.map((agent) => agent.close()));
  }
}
