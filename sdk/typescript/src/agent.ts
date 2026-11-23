import { spawn, type ChildProcessByStdio } from "node:child_process";
import { once } from "node:events";
import { createRequire } from "node:module";
import { Readable, Writable } from "node:stream";
import { setTimeout as sleep } from "node:timers/promises";

import {
  client,
  ndJsonStream,
  PROTOCOL_VERSION,
  RequestError,
  type AgentRequestMethod,
  type AgentRequestParamsByMethod,
  type AgentRequestResponsesByMethod,
  type ClientConnection,
  type InitializeResponse,
  type SessionNotification,
} from "@agentclientprotocol/sdk";
import { z } from "zod";

import type { Env } from "./discover.ts";
import { AgentExited, AgentFailed, NotInstalled, NotLoggedIn, type EukheFailure, type Login } from "./errors.ts";
import { extensionsOf, RunReportNotification, type Extensions, type Feature, type RunReport } from "./extensions.ts";

/** What the agent sends that a session turn consumes. */
export type Inbound =
  | { $: "Update"; notification: SessionNotification }
  | { $: "RunReport"; sessionId: string; report: RunReport };

type Exit = { exitCode: number | null; signal: string | null };

const STDERR_TAIL = 4096;
const EXIT_GRACE_MS = 3000;

/** The SDK's own version, sent as `clientInfo.version`. */
const SDK_VERSION = z
  .object({ version: z.string() })
  .parse(createRequire(import.meta.url)("../package.json")).version;

/**
 * One `eukhe acp` process and its ACP connection. eukhe's ACP agent hosts one
 * session per process, so each {@link Session} owns one of these.
 */
export class AgentProcess {
  readonly bin: string;
  readonly init: InitializeResponse;
  /** The `_eukhe/*` extensions the agent advertised in `initialize`. */
  readonly extensions: Extensions;
  readonly #child: ChildProcessByStdio<Writable, Readable, Readable>;
  readonly #connection: ClientConnection;
  readonly #exit: Promise<Exit>;
  readonly #stderr: { text: string };
  readonly #inbox: { deliver: (inbound: Inbound) => void };

  private constructor(fields: {
    bin: string;
    init: InitializeResponse;
    child: ChildProcessByStdio<Writable, Readable, Readable>;
    connection: ClientConnection;
    exit: Promise<Exit>;
    stderr: { text: string };
    inbox: { deliver: (inbound: Inbound) => void };
  }) {
    this.bin = fields.bin;
    this.init = fields.init;
    this.extensions = extensionsOf(fields.init.agentCapabilities?._meta);
    this.#child = fields.child;
    this.#connection = fields.connection;
    this.#exit = fields.exit;
    this.#stderr = fields.stderr;
    this.#inbox = fields.inbox;
  }

  /** Spawn `<bin> acp` in `cwd` and run the ACP `initialize` handshake. */
  static async launch(bin: string, cwd: string, env: Env): Promise<AgentProcess> {
    const child = spawn(bin, ["acp"], { cwd, env: { ...process.env, ...env }, stdio: ["pipe", "pipe", "pipe"] });
    const stderr = { text: "" };
    child.stderr.setEncoding("utf8");
    child.stderr.on("data", (chunk: string) => {
      stderr.text = (stderr.text + chunk).slice(-STDERR_TAIL);
    });
    const exited = Promise.withResolvers<Exit>();
    child.once("exit", (exitCode, signal) => exited.resolve({ exitCode, signal }));
    const exit = exited.promise;
    try {
      await once(child, "spawn");
    } catch (error) {
      throw spawnFailure(bin, error);
    }
    const inbox: { deliver: (inbound: Inbound) => void } = { deliver: () => {} };
    const connection = client({ name: "eukhe-sdk" })
      .onNotification("session/update", ({ params }) => inbox.deliver({ $: "Update", notification: params }))
      .onNotification("_eukhe/run_report", RunReportNotification, ({ params: { sessionId, ...report } }) =>
        inbox.deliver({ $: "RunReport", sessionId, report }),
      )
      .connect(ndJsonStream(Writable.toWeb(child.stdin), Readable.toWeb(child.stdout)));
    try {
      const init = await connection.agent.request("initialize", {
        protocolVersion: PROTOCOL_VERSION,
        clientCapabilities: {},
        clientInfo: { name: "eukhe-sdk", title: "eukhe SDK", version: SDK_VERSION },
      });
      return new AgentProcess({ bin, init, child, connection, exit, stderr, inbox });
    } catch (error) {
      const failure = await failureOf("initialize", error, { bin, exit, stderr });
      await stop(child, connection, exit);
      throw failure;
    }
  }

  /** Whether the agent serves the eukhe extension `feature`. */
  serves(feature: Feature): boolean {
    switch (this.extensions.$) {
      case "Eukhe":
        return this.extensions.features.has(feature);
      case "PlainAcp":
        return false;
      default: {
        const _: never = this.extensions;
        return _;
      }
    }
  }

  /** Route this process's session updates and run reports to `deliver`. */
  listen(deliver: (inbound: Inbound) => void): void {
    this.#inbox.deliver = deliver;
  }

  /** An ACP method on the agent; agent errors become {@link EukheFailure}s. */
  async request<M extends AgentRequestMethod>(
    method: M,
    params: AgentRequestParamsByMethod[M],
  ): Promise<AgentRequestResponsesByMethod[M]> {
    try {
      return await this.#connection.agent.request(method, params);
    } catch (error) {
      throw await this.#failure(method, error);
    }
  }

  /** An `_eukhe/*` extension method; its result is parsed with `schema`. */
  async extension<S extends z.ZodType>(method: string, params: Record<string, unknown>, schema: S): Promise<z.output<S>> {
    let result: unknown;
    try {
      result = await this.#connection.agent.request<unknown>(method, params);
    } catch (error) {
      throw await this.#failure(method, error);
    }
    const parsed = schema.safeParse(result);
    if (!parsed.success) throw new AgentFailed(method, INVALID_RESULT, z.prettifyError(parsed.error), result);
    return parsed.data;
  }

  async cancel(sessionId: string): Promise<void> {
    try {
      await this.#connection.agent.notify("session/cancel", { sessionId });
    } catch (error) {
      throw await this.#failure("session/cancel", error);
    }
  }

  /** End the process: close stdin, then SIGTERM, then SIGKILL, each after a grace period. */
  async close(): Promise<void> {
    await stop(this.#child, this.#connection, this.#exit);
  }

  #failure(method: string, error: unknown): Promise<EukheFailure> {
    return failureOf(method, error, { bin: this.bin, exit: this.#exit, stderr: this.#stderr });
  }
}

/** The typed failure of a request that threw `error`. */
async function failureOf(
  method: string,
  error: unknown,
  agent: { bin: string; exit: Promise<Exit>; stderr: { text: string } },
): Promise<EukheFailure> {
  if (error instanceof RequestError) {
    return error.code === AUTH_REQUIRED
      ? new NotLoggedIn(loginOf(error.data, error.message, agent.bin))
      : new AgentFailed(method, error.code, error.message, error.data);
  }
  const exit = await exitWithin(agent.exit);
  if (exit !== null) return new AgentExited(exit.exitCode, exit.signal, agent.stderr.text.trim());
  return new AgentFailed(method, INTERNAL_ERROR, error instanceof Error ? error.message : String(error), error);
}

const AUTH_REQUIRED = -32000;
const INTERNAL_ERROR = -32603;
/** A result that does not match the documented `_eukhe/*` shape (JSON-RPC "invalid params" is the closest code). */
const INVALID_RESULT = -32602;

/** eukhe's auth error names how to log in (`data.login`); another agent's gets its message. */
const AuthErrorData = z.object({
  login: z.object({ command: z.string(), slashCommand: z.string().nullable(), instructions: z.string() }),
});

function loginOf(data: unknown, message: string, bin: string): Login {
  const named = AuthErrorData.safeParse(data);
  return named.success ? named.data.login : { command: bin, slashCommand: null, instructions: message };
}

function spawnFailure(bin: string, error: unknown): Error {
  const code = z.object({ code: z.string() }).safeParse(error);
  if (code.success && (code.data.code === "ENOENT" || code.data.code === "EACCES")) return new NotInstalled([bin]);
  return error instanceof Error ? error : new Error(String(error));
}

async function stop(
  child: ChildProcessByStdio<Writable, Readable, Readable>,
  connection: ClientConnection,
  exit: Promise<Exit>,
): Promise<void> {
  connection.close();
  child.stdin.end();
  const signals: readonly NodeJS.Signals[] = ["SIGTERM", "SIGKILL"];
  for (const signal of signals) {
    if ((await exitWithin(exit)) !== null) return;
    child.kill(signal);
  }
  await exit;
}

/** The exit status, or null when the process still runs after the grace period. */
function exitWithin(exit: Promise<Exit>): Promise<Exit | null> {
  return Promise.race([exit, sleep(EXIT_GRACE_MS, null, { ref: false })]);
}
