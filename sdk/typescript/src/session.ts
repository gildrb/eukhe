import type { McpServer, SessionConfigOption, StopReason } from "@agentclientprotocol/sdk";

import type { AgentProcess, Inbound } from "./agent.ts";
import { TurnInProgress, UnknownModel, Unsupported } from "./errors.ts";
import { eventsOfUpdate, type EukheEvent } from "./events.ts";
import * as ext from "./extensions.ts";

/** Options of {@link Eukhe.session}. */
export type SessionOptions = {
  /** `provider/model-id` (e.g. `anthropic/claude-sonnet-4-5`); the agent's default otherwise. */
  model?: string;
  /** MCP servers the session may call, in ACP form. */
  mcpServers?: McpServer[];
};

/** What a running turn receives, in arrival order. */
type TurnItem =
  | { $: "Event"; event: EukheEvent }
  | { $: "Ended"; stopReason: StopReason }
  | { $: "Failed"; error: unknown };

/** One eukhe conversation: prompt it, cancel its turn, and read its eukhe extensions. */
export class Session {
  /** The ACP session id. */
  readonly id: string;
  readonly #agent: AgentProcess;
  /** The running turn's mailbox; the agent's listener and `prompt` share it. */
  readonly #turn: { mailbox: Mailbox | null };

  private constructor(id: string, agent: AgentProcess) {
    this.id = id;
    this.#agent = agent;
    const turn: { mailbox: Mailbox | null } = { mailbox: null };
    this.#turn = turn;
    agent.listen((inbound) => {
      for (const event of eventsOfInbound(inbound, id)) turn.mailbox?.push({ $: "Event", event });
    });
  }

  /** `session/new` on `agent` in `cwd`, then the model choice when one is given. */
  static async open(agent: AgentProcess, cwd: string, options: SessionOptions): Promise<Session> {
    const created = await agent.request("session/new", { cwd, mcpServers: options.mcpServers ?? [] });
    const session = new Session(created.sessionId, agent);
    if (options.model !== undefined) await session.#chooseModel(options.model, created.configOptions ?? []);
    return session;
  }

  /**
   * Send `text` and stream the turn's events; the last one is `TurnEnd`.
   * Leaving the loop early cancels the turn.
   */
  async *prompt(text: string): AsyncGenerator<EukheEvent, void, undefined> {
    if (this.#turn.mailbox !== null) throw new TurnInProgress();
    const mailbox = new Mailbox();
    this.#turn.mailbox = mailbox;
    this.#agent.request("session/prompt", { sessionId: this.id, prompt: [{ type: "text", text }] }).then(
      (response) => mailbox.push({ $: "Ended", stopReason: response.stopReason }),
      (error: unknown) => mailbox.push({ $: "Failed", error }),
    );
    try {
      for (;;) {
        const item = await mailbox.take();
        switch (item.$) {
          case "Event":
            yield item.event;
            break;
          case "Ended":
            this.#turn.mailbox = null;
            yield { $: "TurnEnd", stopReason: item.stopReason };
            return;
          case "Failed":
            this.#turn.mailbox = null;
            throw item.error;
          default: {
            const _: never = item;
            return _;
          }
        }
      }
    } finally {
      if (this.#turn.mailbox === mailbox) {
        await this.#agent.cancel(this.id);
        await settled(mailbox);
        this.#turn.mailbox = null;
      }
    }
  }

  /** Stop the running turn; its stream ends with `TurnEnd` `cancelled`. */
  async cancel(): Promise<void> {
    await this.#agent.cancel(this.id);
  }

  /** The session's budget (`_eukhe/budget/*`); `null` until one is set or a run starts. */
  readonly budget = {
    get: (): Promise<ext.Budget> => this.#extension("budget", "_eukhe/budget/get", {}, ext.Budget),
    /** `"run"` limits the running (or next) run; `"standing"` every later run too. */
    set: (limits: ext.BudgetLimits, scope: "run" | "standing" = "run"): Promise<ext.Budget> =>
      this.#extension("budget", "_eukhe/budget/set", { limits, standing: scope === "standing" }, ext.Budget),
    add: (amounts: ext.BudgetAmounts): Promise<ext.Budget> =>
      this.#extension("budget", "_eukhe/budget/add", { amounts }, ext.Budget),
  };

  /** The checks a turn must pass before eukhe calls it done (`_eukhe/acceptance/*`). */
  readonly acceptance = {
    get: (): Promise<ext.Acceptance> => this.#extension("acceptance", "_eukhe/acceptance/get", {}, ext.Acceptance),
    set: (checks: readonly ext.CheckSpec[], options: ext.AcceptanceOptions = {}): Promise<ext.Acceptance> =>
      this.#extension("acceptance", "_eukhe/acceptance/set", { checks, ...options }, ext.Acceptance),
  };

  /** Undo the last turn's file changes (`_eukhe/undo`). */
  undo(): Promise<ext.Undo> {
    return this.#extension("undo", "_eukhe/undo", {}, ext.Undo);
  }

  /** The file changes of the last turn, or of the whole session (`_eukhe/diff`). */
  diff(scope: "turn" | "all" = "turn"): Promise<ext.Diff> {
    return this.#extension("diff", "_eukhe/diff", { scope }, ext.Diff);
  }

  /** Every irreversible effect that ran in this session (`_eukhe/effects`). */
  effects(): Promise<ext.Effects> {
    return this.#extension("effects", "_eukhe/effects", {}, ext.Effects);
  }

  /** End the session and its agent process. */
  async close(): Promise<void> {
    await this.#agent.close();
  }

  async #extension<S extends ext.Schema>(
    feature: ext.Feature,
    method: string,
    params: Record<string, unknown>,
    schema: S,
  ): Promise<ext.Output<S>> {
    if (!this.#agent.serves(feature)) throw new Unsupported(feature);
    return this.#agent.extension(method, { sessionId: this.id, ...params }, schema);
  }

  async #chooseModel(model: string, configOptions: readonly SessionConfigOption[]): Promise<void> {
    const picker = configOptions.find((option) => option.id === "model");
    if (picker === undefined || picker.type !== "select") throw new Unsupported("model");
    const choices = picker.options
      .flatMap((entry) => ("group" in entry ? entry.options : [entry]))
      .map((choice) => ({ value: choice.value, label: modelLabel(choice.value) }));
    const match = choices.find((choice) => choice.value === model || choice.label === model);
    if (match === undefined) throw new UnknownModel(model, choices.map((choice) => choice.label));
    await this.#agent.request("session/set_config_option", { sessionId: this.id, configId: "model", value: match.value });
  }
}

/** eukhe's model values are JSON `[provider, id]` pairs; people name them `provider/id`. */
function modelLabel(value: string): string {
  const pair = ext.ModelPair.safeParse(parseJson(value));
  return pair.success ? `${pair.data[0]}/${pair.data[1]}` : value;
}

function parseJson(text: string): unknown {
  try {
    return JSON.parse(text);
  } catch {
    return null;
  }
}

function eventsOfInbound(inbound: Inbound, sessionId: string): readonly EukheEvent[] {
  switch (inbound.$) {
    case "Update":
      return inbound.notification.sessionId === sessionId ? eventsOfUpdate(inbound.notification.update) : [];
    case "RunReport":
      return inbound.sessionId === sessionId ? [{ $: "RunReport", report: inbound.report }] : [];
    default: {
      const _: never = inbound;
      return _;
    }
  }
}

/** Wait until a turn's prompt request settles, dropping its remaining events. */
async function settled(mailbox: Mailbox): Promise<void> {
  for (;;) {
    const item = await mailbox.take();
    switch (item.$) {
      case "Event":
        break;
      case "Ended":
      case "Failed":
        return;
      default: {
        const _: never = item;
        return _;
      }
    }
  }
}

/** A turn's items in arrival order, taken by its one consumer. */
class Mailbox {
  readonly #items: TurnItem[] = [];
  readonly #waiters: ((item: TurnItem) => void)[] = [];

  push(item: TurnItem): void {
    const waiter = this.#waiters.shift();
    if (waiter === undefined) this.#items.push(item);
    else waiter(item);
  }

  take(): Promise<TurnItem> {
    const { promise, resolve } = Promise.withResolvers<TurnItem>();
    const item = this.#items.shift();
    if (item === undefined) this.#waiters.push(resolve);
    else resolve(item);
    return promise;
  }
}
