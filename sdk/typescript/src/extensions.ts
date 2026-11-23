/**
 * The `_eukhe/*` ACP extension shapes (docs/embed/acp.md and
 * docs/embed/eukhe-acp.schema.json in the eukhe repository), as zod schemas
 * the SDK checks every agent payload against.
 */
import { z } from "zod";

export type { Feature } from "./errors.ts";

/** A schema an extension result is parsed with. */
export type Schema = z.ZodType;
export type Output<S extends Schema> = z.output<S>;

/** `initialize` → `agentCapabilities._meta.eukhe`: the extension set an eukhe agent serves. */
const Advertised = z.object({
  eukhe: z.object({ version: z.string(), features: z.array(z.string()) }),
});

/** What an agent advertises: eukhe's extension version and features, or nothing for a plain ACP agent. */
export type Extensions = { $: "Eukhe"; version: string; features: ReadonlySet<string> } | { $: "PlainAcp" };

export function extensionsOf(agentCapabilitiesMeta: unknown): Extensions {
  const meta = Advertised.safeParse(agentCapabilitiesMeta);
  return meta.success
    ? { $: "Eukhe", version: meta.data.eukhe.version, features: new Set(meta.data.eukhe.features) }
    : { $: "PlainAcp" };
}

/** eukhe's model picker values: a JSON `[provider, id]` pair. */
export const ModelPair = z.tuple([z.string(), z.string()]);

/** An irreversible effect that ran (`e<N>`, numbered per root session). */
export const RanEffect = z.object({
  id: z.string(),
  key: z.string(),
  run: z.number(),
  kind: z.enum(["shellStep", "documentAccess", "mcpCall"]),
  command: z.string(),
  classes: z.array(z.string()),
  agent: z.string().optional(),
  sessionId: z.string(),
  atMs: z.number(),
});
export type RanEffect = z.output<typeof RanEffect>;

/** A step a crash left of unknown outcome, treated as not run. */
export const UnknownEffect = z.object({
  id: z.string(),
  kind: z.string(),
  what: z.string(),
  at: z.number(),
  cause: z.string().optional(),
  settledRun: z.number().optional(),
  resolution: z.string().optional(),
});
export type UnknownEffect = z.output<typeof UnknownEffect>;

/** One acceptance check of a turn and its verdict. */
export const ReportCheck = z.object({
  kind: z.enum(["command", "judge", "until", "intent"]),
  text: z.string(),
  verdict: z.enum(["confirmed", "refuted", "broken", "unjudged"]).nullable(),
  summary: z.string().nullable(),
});
export type ReportCheck = z.output<typeof ReportCheck>;

/** The `_eukhe/run_report` notification, sent once per turn before its `session/prompt` response. */
export const RunReportNotification = z.object({
  sessionId: z.string(),
  promptTurnId: z.number(),
  /** null: the turn failed (`error` says why). */
  stopReason: z.enum(["end_turn", "max_tokens", "max_turn_requests", "refusal", "cancelled"]).nullable(),
  error: z.string().optional(),
  /** The final assistant text. */
  answer: z.string().nullable(),
  label: z.enum(["verified", "failed", "unverified", "checks_passed_unconfined", "checks_passed_not_certified"]),
  certified: z.boolean(),
  checks: z.array(ReportCheck),
  /** Irreversible effects that ran this turn. */
  ran: z.array(RanEffect),
  unknown: z.array(UnknownEffect),
  /** Work the run found left; empty when none. */
  left: z.array(z.string()),
});
/** A turn's end-of-run report. */
export type RunReport = Omit<z.output<typeof RunReportNotification>, "sessionId">;

/** A limit per budget dimension; `"unlimited"` lifts it. */
const Limit = z.union([z.number(), z.literal("unlimited")]);
export type BudgetLimits = {
  costMicros?: number | "unlimited";
  tokens?: number | "unlimited";
  timeMs?: number | "unlimited";
  toolCalls?: number | "unlimited";
  requests?: number | "unlimited";
};
export type BudgetAmounts = {
  costMicros?: number;
  tokens?: number;
  timeMs?: number;
  toolCalls?: number;
  requests?: number;
};

const Amounts = z.looseObject({
  costMicros: z.number(),
  tokens: z.number(),
  timeMs: z.number(),
  toolCalls: z.number(),
  requests: z.number(),
});

/** A budget as the session sees it: in each limited dimension `free + held + spent + lent == limits + over`. */
export const BudgetReport = z.looseObject({
  sessionId: z.string(),
  limits: z.looseObject({
    costMicros: Limit.optional(),
    tokens: Limit.optional(),
    timeMs: Limit.optional(),
    toolCalls: Limit.optional(),
    requests: Limit.optional(),
  }),
  free: Amounts,
  held: Amounts,
  spent: Amounts,
  lent: Amounts,
  over: Amounts,
  phase: z.enum(["working", "wrap_up", "exhausted"]),
  short: z.string().optional(),
  deadlineMs: z.number().optional(),
});
export type BudgetReport = z.output<typeof BudgetReport>;

/** `_eukhe/budget/*` result: null when the session has no budget yet. */
export const Budget = z.object({ budget: BudgetReport.nullable() }).transform((result) => result.budget);
export type Budget = z.output<typeof Budget>;

/** One acceptance check to set. */
export type CheckSpec =
  | { kind: "command"; command: string; expect?: string; timeoutMs?: number; protect?: boolean; strength?: string }
  | { kind: "judge"; condition: string; evidence?: string; model?: string }
  | { kind: "until"; command: string; timeoutMs?: number; strength?: string }
  | { kind: "intent"; model?: string };

/** The session's acceptance state. */
export const AcceptanceState = z.looseObject({
  label: z.string(),
  state: z.unknown(),
  revision: z.number(),
  checks: z.array(z.looseObject({ spec: z.looseObject({ kind: z.string() }) })),
  claimed: z.unknown(),
  tries: z.number(),
  maxReturns: z.number(),
});
export type AcceptanceState = z.output<typeof AcceptanceState>;

export const Acceptance = z.object({ acceptance: AcceptanceState }).transform((result) => result.acceptance);
export type Acceptance = z.output<typeof Acceptance>;

/** Options of `acceptance.set`: how often a refuted turn returns to work; `intent` adds an intent check. */
export type AcceptanceOptions = { maxReturns?: number; intent?: boolean };

/** `_eukhe/undo`: the files restored, the turn undone, turns left to undo, effects undo cannot reverse. */
export const Undo = z.object({
  restored: z.array(z.string()),
  turn: z.number(),
  left: z.number(),
  notUndone: z.array(RanEffect),
});
export type Undo = z.output<typeof Undo>;

/** `_eukhe/diff`: a unified diff, the paths it covers, the paths it skipped. */
export const Diff = z.object({ diff: z.string(), paths: z.array(z.string()), skipped: z.array(z.string()) });
export type Diff = z.output<typeof Diff>;

/** `_eukhe/effects`: every irreversible effect the session ran, and the crash-unknown ones. */
export const Effects = z.object({ ran: z.array(RanEffect), unknown: z.array(UnknownEffect) });
export type Effects = z.output<typeof Effects>;
