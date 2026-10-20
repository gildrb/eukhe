// PURE session state: the open reply plus every SessionEvent folded in
// (`reduce`), and `derivePhase`, the one source of the activity line, the
// sidebar status word, the document title, the badge and announcements.
// No DOM, no clock reads: callers pass `now`.

import type {
  AgentState,
  Cursor,
  Message,
  ModelRef,
  OpenReply,
  PromptProgress,
  Queue,
  SessionEvent,
  StreamUpdate,
  Summary,
} from "./types.ts";
import type { fmt as Fmt } from "./format.ts";

// The one token estimate (eukhe-types `token_estimate`, 7/2 chars per
// token); a Rust test in eukhe-dashboard pins this value to it.
const CHARS_PER_TOKEN = 3.5;
const LIVE_RATE_AFTER_MS = 250;
const BASH_TAIL_CHARS = 64_000;
const NOTE_LIMIT = 200;
const LOG_LIMIT = 400;
const SIGNAL_RULES = "[Signal reply rules:";

export type ToolStatus = "running" | "done" | "failed" | "stopped" | "waiting";

export type Tool = {
  id: string;
  name: string;
  args: unknown;
  status: ToolStatus;
  partial: unknown;
  result: unknown;
  isError: boolean;
  startedAt: number;
  endedAt: number;
  updatedAt?: number;
  durationMs?: number;
};

export type LogEntry = { at: number; kind: string; [key: string]: unknown };

export type Turn = {
  running: boolean;
  startedAt: number;
  endedAt: number;
  requestAt: number;
  firstTokenAt: number;
  prefill: PromptProgress | null;
  prefillAt: number;
  stream: "thinking" | "writing" | null;
  deltaChars: number;
  deltaStartAt: number;
  retry: {
    attempt: number;
    maxAttempts: number | null;
    delayMs: number;
    errorMessage: string;
    backupModel: string | null;
    at: number;
  } | null;
  compacting: { reason: string; at: number; summary: string } | null;
  chatWait: boolean;
  error: string | null;
  stopped: boolean;
  log: LogEntry[];
};

export type Note = {
  at: number;
  kind: string;
  text: string;
  index: number;
  summary?: string | null;
};

export type Pending = {
  admissionId: string;
  text: string;
  images: { data: string; mimeType: string; preview: string; name: string }[];
  mode: "steer" | "followUp";
  queued: boolean;
  status: "sending" | "held" | "failed";
  error: string | null;
};

export type Speed = {
  ttftMs: number | null;
  rate: number | null;
  outputTokens: number | null;
  durationMs: number | null;
};

export type Session = {
  id: string;
  path: string;
  title: string;
  state: AgentState;
  summary: Summary | null;
  cursor: Cursor | null;
  messages: Message[];
  live: Message | null;
  openIndex: number;
  tools: Record<string, Tool>;
  queue: Queue;
  turn: Turn;
  last: Speed | null;
  bash: { command: string; output: string; startedAt: number } | null;
  goal: unknown;
  serviceTier: string | null;
  memory: { stamp: number; last: unknown };
  notes: Note[];
  pending: Pending[];
};

export type Approval = {
  requestId: string;
  step: number;
  command: string;
  effect: string;
  status: "pending" | "answering" | "elsewhere";
};

/** Plain text of message content (a string, or text blocks). */
export function contentText(content: unknown): string {
  if (typeof content === "string") return content;
  if (!Array.isArray(content)) return "";
  return content
    .filter(
      (block): block is { text: string } =>
        Boolean(block) &&
        (block.type === "text" || (!block.type && typeof block.text === "string")),
    )
    .map((block) => block.text)
    .join("\n\n");
}

/** A user prompt without the Signal gateway's reply rules. */
export function withoutSignalRules(text: string): string {
  if (!text.startsWith(SIGNAL_RULES)) return text;
  const end = text.indexOf("]");
  return end < 0 ? text : text.slice(end + 1).trimStart();
}

function freshTurn(now: number): Turn {
  return {
    running: false,
    startedAt: now,
    endedAt: 0,
    requestAt: 0,
    firstTokenAt: 0,
    prefill: null,
    prefillAt: 0,
    stream: null,
    deltaChars: 0,
    deltaStartAt: 0,
    retry: null,
    compacting: null,
    chatWait: false,
    error: null,
    stopped: false,
    log: [],
  };
}

const EMPTY_QUEUE: Queue = { queuedCount: 0, steering: [], followUps: [] };

/**
 * The session state for an `open` reply. With `replay: 'complete'` and the
 * same session already in hand, the transcript is kept (the bridge replays
 * what was missed as ordinary events).
 */
export function openSession(reply: OpenReply, previous: Session | null, now: number): Session {
  const state = reply.state ?? {};
  const keep =
    previous !== null &&
    previous.id === reply.session.id &&
    reply.replay === "complete" &&
    !Array.isArray(reply.messages);
  const samePrevious = previous !== null && previous.id === reply.session.id;
  const base = keep
    ? previous
    : {
        messages: [] as Message[],
        live: null,
        openIndex: -1,
        tools: {},
        turn: freshTurn(now),
        last: null,
        bash: null,
        memory: { stamp: 0, last: null },
        notes: [],
        pending: samePrevious ? previous.pending : [],
      };
  const session: Session = {
    ...base,
    id: reply.session.id,
    path: reply.session.path,
    title: "",
    state,
    summary: reply.summary ?? null,
    cursor: reply.cursor ?? (keep ? previous.cursor : null),
    queue: state.sessionActions ?? EMPTY_QUEUE,
    goal: state.goal ?? null,
    serviceTier: state.serviceTier ?? null,
  };
  if (!keep) {
    session.messages = Array.isArray(reply.messages) ? reply.messages : [];
    session.last = lastFromMessages(session.messages);
    if (state.isStreaming) session.turn = { ...freshTurn(now), running: true };
    if (state.isCompacting) {
      session.turn = { ...session.turn, compacting: { reason: "threshold", at: now, summary: "" } };
    }
  }
  session.title = sessionTitle(session);
  return session;
}

/** The session's display title. */
export function sessionTitle(
  session: Pick<Session, "state" | "summary" | "messages">,
  fallback = "New chat",
): string {
  const name = session.state.sessionName;
  if (name) return name;
  if (session.summary?.sessionName) return session.summary.sessionName;
  const first = session.messages.find((message) => message.role === "user");
  const text = first ? withoutSignalRules(contentText(first.content)).trim() : "";
  return text ? (text.split("\n")[0] ?? "").slice(0, 80) : fallback;
}

function log(turn: Turn, entry: LogEntry): LogEntry[] {
  const next = turn.log.length >= LOG_LIMIT ? turn.log.slice(-LOG_LIMIT + 1) : turn.log.slice();
  next.push(entry);
  return next;
}

function note(
  session: Session,
  kind: string,
  text: string,
  now: number,
  extra: Partial<Note> = {},
): Note[] {
  const notes = session.notes.length >= NOTE_LIMIT ? session.notes.slice(1) : session.notes.slice();
  notes.push({ at: now, kind, text, index: session.messages.length, ...extra });
  return notes;
}

/** Exact speed of a settled assistant message, from `usage` and `timing`. */
export function messageSpeed(message: Message | undefined | null): Speed | null {
  if (!message || message.role !== "assistant") return null;
  const timing = message.timing ?? {};
  const output = message.usage ? message.usage.output : 0;
  const decodeMs =
    timing.lastTokenMs !== undefined && timing.firstTokenMs !== undefined
      ? timing.lastTokenMs - timing.firstTokenMs
      : 0;
  return {
    ttftMs: timing.firstTokenMs ?? null,
    rate: decodeMs > 0 && output > 0 ? output / (decodeMs / 1000) : null,
    outputTokens: output || null,
    durationMs: message.durationMs ?? timing.lastTokenMs ?? null,
  };
}

function lastFromMessages(messages: Message[]): Speed | null {
  for (let index = messages.length - 1; index >= 0; index -= 1) {
    const message = messages[index];
    if (message?.role === "assistant") {
      const speed = messageSpeed(message);
      return speed ? { ...speed, durationMs: null } : null;
    }
  }
  return null;
}

/** Live decode estimate (chars / CHARS_PER_TOKEN), once 250ms of deltas came in. */
export function liveRate(turn: Turn, now: number): number | null {
  if (!turn.deltaStartAt || turn.deltaChars <= 0) return null;
  const elapsed = now - turn.deltaStartAt;
  if (elapsed < LIVE_RATE_AFTER_MS) return null;
  return turn.deltaChars / CHARS_PER_TOKEN / (elapsed / 1000);
}

/** Prefill throughput and ETA from `prompt_progress`. */
export function prefillRate(progress: PromptProgress | null): {
  rate: number | null;
  etaMs: number | null;
} {
  if (!progress || !progress.timeMs) return { rate: null, etaMs: null };
  const fresh = progress.processed - progress.cache;
  const rate = fresh > 0 ? fresh / (progress.timeMs / 1000) : null;
  const etaMs = rate ? ((progress.total - progress.processed) / rate) * 1000 : null;
  return { rate, etaMs };
}

function reconcilePending(pending: Pending[], message: Message): Pending[] {
  if (!pending.length) return pending;
  const admissionId = message.admissionId ?? message.details?.admissionId;
  const text = withoutSignalRules(contentText(message.content)).trim();
  const index = pending.findIndex((item) =>
    admissionId ? item.admissionId === admissionId : item.text.trim() === text,
  );
  if (index < 0) return pending;
  return [...pending.slice(0, index), ...pending.slice(index + 1)];
}

function onStreamUpdate(turn: Turn, update: StreamUpdate | undefined, now: number): Turn {
  if (!update) return turn;
  switch (update.type) {
    case "text_delta":
    case "thinking_delta":
    case "toolcall_delta": {
      const stream = update.type === "thinking_delta" ? "thinking" : "writing";
      const next: Turn = {
        ...turn,
        deltaChars: turn.deltaChars + (update.delta ?? "").length,
        deltaStartAt: turn.deltaStartAt || now,
        firstTokenAt: turn.firstTokenAt || now,
        stream,
      };
      if (turn.stream !== stream) next.log = log(turn, { at: now, kind: stream });
      return next;
    }
    default:
      return turn;
  }
}

/** Fold one SessionEvent into the session. Returns a new object when anything changed. */
export function reduce(session: Session, event: SessionEvent, now: number): Session {
  const { turn } = session;
  switch (event.type) {
    case "agent_start":
      return {
        ...session,
        live: null,
        turn: { ...freshTurn(now), running: true, log: [{ at: now, kind: "start" }] },
      };
    case "agent_end": {
      const lastAssistant = session.messages.findLast((message) => message.role === "assistant");
      const speed = messageSpeed(lastAssistant);
      const stopped = lastAssistant?.stopReason === "aborted";
      const failed =
        lastAssistant?.stopReason === "error"
          ? lastAssistant.errorMessage || "The model request failed."
          : null;
      const tools = { ...session.tools };
      for (const [id, tool] of Object.entries(tools)) {
        if (tool.status === "running") {
          tools[id] = { ...tool, status: stopped ? "stopped" : "done", endedAt: now };
        }
      }
      return {
        ...session,
        live: null,
        tools,
        bash: null,
        turn: {
          ...turn,
          running: false,
          endedAt: now,
          stopped,
          error: turn.error ?? failed,
          retry: null,
          chatWait: false,
          stream: null,
          log: log(turn, { at: now, kind: "end" }),
        },
        last: {
          ttftMs: speed?.ttftMs ?? null,
          rate: speed?.rate ?? null,
          outputTokens: speed?.outputTokens ?? null,
          durationMs: now - turn.startedAt,
        },
      };
    }
    case "turn_start":
      return {
        ...session,
        turn: {
          ...turn,
          running: true,
          requestAt: now,
          firstTokenAt: 0,
          prefill: null,
          prefillAt: 0,
          stream: null,
          deltaChars: 0,
          deltaStartAt: 0,
          log: log(turn, { at: now, kind: "turn" }),
        },
      };
    case "turn_end":
      if (!event.error) return session;
      return {
        ...session,
        turn: {
          ...turn,
          error: event.error,
          log: log(turn, { at: now, kind: "error", text: event.error }),
        },
        notes: note(session, "error", event.error, now),
      };
    case "prompt_progress":
      return {
        ...session,
        turn: {
          ...turn,
          prefill: event.progress,
          prefillAt: turn.prefillAt || now,
          log: turn.prefill ? turn.log : log(turn, { at: now, kind: "prefill" }),
        },
      };
    case "message_start": {
      const { message } = event;
      if (message.role === "assistant") {
        return {
          ...session,
          live: message,
          turn: onStreamUpdate(
            { ...turn, deltaChars: 0, deltaStartAt: 0, stream: null },
            event.assistantMessageEvent,
            now,
          ),
        };
      }
      const pending =
        message.role === "user" ? reconcilePending(session.pending, message) : session.pending;
      return {
        ...session,
        messages: [...session.messages, message],
        openIndex: session.messages.length,
        pending,
      };
    }
    case "message_update":
      return {
        ...session,
        live: event.message,
        turn: onStreamUpdate(turn, event.assistantMessageEvent, now),
      };
    case "message_end": {
      const { message } = event;
      if (message.role === "assistant") {
        const speed = messageSpeed(message);
        return {
          ...session,
          live: null,
          messages: [...session.messages, message],
          turn: { ...turn, stream: null },
          last: speed ? { ...speed, durationMs: null } : null,
        };
      }
      const messages = session.messages.slice();
      const open = session.openIndex >= 0 ? messages[session.openIndex] : undefined;
      if (open && open.role === message.role) messages[session.openIndex] = message;
      else messages.push(message);
      const pending =
        message.role === "user" ? reconcilePending(session.pending, message) : session.pending;
      const next = { ...session, messages, openIndex: -1, pending };
      next.title = sessionTitle(next);
      return next;
    }
    case "tool_execution_start":
      return {
        ...session,
        tools: {
          ...session.tools,
          [event.toolCallId]: {
            id: event.toolCallId,
            name: event.toolName,
            args: event.args,
            status: "running",
            partial: null,
            result: null,
            isError: false,
            startedAt: now,
            endedAt: 0,
            updatedAt: now,
          },
        },
        turn: {
          ...turn,
          stream: null,
          log: log(turn, { at: now, kind: "tool", id: event.toolCallId, name: event.toolName }),
        },
      };
    case "tool_execution_update": {
      const tool: Tool = session.tools[event.toolCallId] ?? {
        id: event.toolCallId,
        name: event.toolName,
        args: event.args,
        status: "running",
        partial: null,
        result: null,
        isError: false,
        startedAt: now,
        endedAt: 0,
      };
      return {
        ...session,
        tools: {
          ...session.tools,
          [event.toolCallId]: { ...tool, partial: event.partialResult, updatedAt: now },
        },
      };
    }
    case "tool_execution_end": {
      const tool: Tool = session.tools[event.toolCallId] ?? {
        id: event.toolCallId,
        name: event.toolName,
        args: null,
        status: "running",
        partial: null,
        result: null,
        isError: false,
        startedAt: now,
        endedAt: 0,
      };
      return {
        ...session,
        tools: {
          ...session.tools,
          [event.toolCallId]: {
            ...tool,
            status: event.isError ? "failed" : "done",
            result: event.result,
            isError: event.isError,
            endedAt: now,
            updatedAt: now,
          },
        },
        turn: {
          ...turn,
          log: log(turn, {
            at: now,
            kind: "toolEnd",
            id: event.toolCallId,
            name: event.toolName,
            failed: event.isError,
          }),
        },
      };
    }
    case "auto_retry_start":
      return {
        ...session,
        turn: {
          ...turn,
          retry: {
            attempt: event.attempt,
            maxAttempts: event.maxAttempts ?? null,
            delayMs: event.delayMs,
            errorMessage: event.errorMessage,
            backupModel: event.backupModel ?? null,
            at: now,
          },
          log: log(turn, {
            at: now,
            kind: "retry",
            attempt: event.attempt,
            text: event.errorMessage,
          }),
        },
      };
    case "auto_retry_end":
      return {
        ...session,
        turn: {
          ...turn,
          retry: null,
          error: event.success ? turn.error : event.finalError || "Retries ran out.",
          log: log(turn, { at: now, kind: "retryEnd", success: event.success }),
        },
        notes: event.success
          ? session.notes
          : note(
              session,
              "error",
              `Retries ran out: ${event.finalError || "the request kept failing."}`,
              now,
            ),
      };
    case "compaction_start":
      return {
        ...session,
        turn: {
          ...turn,
          compacting: { reason: event.reason, at: now, summary: "" },
          log: log(turn, { at: now, kind: "compaction", reason: event.reason }),
        },
      };
    case "compaction_summary_delta":
      if (!turn.compacting) return session;
      return {
        ...session,
        turn: {
          ...turn,
          compacting: { ...turn.compacting, summary: turn.compacting.summary + event.delta },
        },
      };
    case "compaction_end": {
      let text: string;
      let kind = "note";
      if (event.aborted) text = "Compaction cancelled.";
      else if (event.errorMessage) {
        text = `Compaction failed: ${event.errorMessage}`;
        kind = "error";
      } else text = "Earlier messages compacted.";
      return {
        ...session,
        turn: {
          ...turn,
          compacting: null,
          log: log(turn, { at: now, kind: "compactionEnd", aborted: event.aborted }),
        },
        notes: note(session, kind, text, now, { summary: event.result?.summary ?? null }),
      };
    }
    case "session_info_changed": {
      const next = { ...session, state: { ...session.state, sessionName: event.name ?? null } };
      next.title = sessionTitle(next);
      return next;
    }
    case "service_tier_changed":
      return {
        ...session,
        serviceTier: event.serviceTier,
        state: { ...session.state, serviceTier: event.serviceTier },
      };
    case "session_action_update":
      return { ...session, queue: event.actions };
    case "goal_update":
      return { ...session, goal: event.goal };
    case "chat_turn_wait":
      return {
        ...session,
        turn: {
          ...turn,
          chatWait: event.waiting,
          log: event.waiting ? log(turn, { at: now, kind: "wait" }) : turn.log,
        },
      };
    case "memory_update":
      return { ...session, memory: { stamp: session.memory.stamp + 1, last: event.update } };
    case "agent_relay":
      return {
        ...session,
        notes: note(session, "relay", `${event.from} → ${event.to}: ${event.text}`, now),
      };
    case "bash_start":
      return { ...session, bash: { command: event.command, output: "", startedAt: now } };
    case "bash_output": {
      if (!session.bash) return session;
      const output = (session.bash.output + event.chunk).slice(-BASH_TAIL_CHARS);
      return { ...session, bash: { ...session.bash, output } };
    }
    case "bash_end":
      return {
        ...session,
        bash: null,
        notes: event.errorMessage
          ? note(session, "error", `Shell command failed: ${event.errorMessage}`, now)
          : session.notes,
      };
    case "refine_complete":
      return { ...session, notes: note(session, "note", "Refinement applied.", now) };
    case "refine_failed":
      return {
        ...session,
        notes: note(session, "error", `Refinement failed: ${event.error}`, now),
      };
    case "ipython_sent_agent_message":
      return {
        ...session,
        notes: note(session, "note", "The Python kernel sent the agent a message.", now),
      };
    default:
      return session;
  }
}

const EFFECT_WORDS: Record<string, string> = {
  read: "Reads files",
  write: "Changes files",
  exec: "Runs a program",
  net: "Uses the network",
};

/** A shell effect as words. */
export function effectWords(effect: string): string {
  return EFFECT_WORDS[effect] ?? "Runs a command";
}

/** One line naming what a tool call acts on (`cargo test`, `src/main.rs`). */
export function toolTarget(args: unknown): string {
  if (!args || typeof args !== "object") return typeof args === "string" ? args : "";
  const record = args as Record<string, unknown>;
  for (const key of [
    "command",
    "cmd",
    "path",
    "file_path",
    "filePath",
    "pattern",
    "query",
    "url",
    "code",
    "description",
  ]) {
    const value = record[key];
    if (typeof value === "string" && value) return value.split("\n")[0] ?? "";
  }
  const values = Object.values(record);
  const only = values[0];
  if (values.length === 1 && typeof only === "string") return only.split("\n")[0] ?? "";
  const json = JSON.stringify(args);
  return json === "{}" ? "" : json;
}

/** A model's display name (`Faux Model`). */
export function modelName(model: ModelRef | string | null | undefined): string {
  if (!model) return "";
  if (typeof model === "string") return model;
  return model.name || model.id || "";
}

/** The last path segment (`/home/gil/eukhe` → `eukhe`). */
export function basename(path: string | null | undefined): string {
  if (!path) return "";
  const parts = path.split("/").filter(Boolean);
  return parts.length ? (parts[parts.length - 1] ?? "/") : "/";
}

export type PhaseName =
  | "none"
  | "approval"
  | "retrying"
  | "compacting"
  | "bash"
  | "tool"
  | "tools"
  | "memory"
  | "writing"
  | "thinking"
  | "prefill"
  | "admission"
  | "waiting"
  | "sending"
  | "failed"
  | "stopped"
  | "idle";

export type Phase = {
  phase: PhaseName;
  label: string;
  running: boolean;
  urgent: boolean;
  action: null | "cancelRetry" | "cancelCompaction";
  announce: string;
};

function phase(kind: PhaseName, label: string, extra: Partial<Phase> = {}): Phase {
  return {
    phase: kind,
    label,
    running: false,
    urgent: false,
    action: null,
    announce: "",
    ...extra,
  };
}

/**
 * The one live status of the bound session (the activity line, the
 * sidebar status word, the document title, announcements). `fmt` is
 * format.ts, injected to keep this module pure.
 */
export function derivePhase(
  state: { session: Session | null; approvals: Approval[] },
  now: number,
  fmt: typeof Fmt,
): Phase {
  const { session, approvals } = state;
  if (!session) return phase("none", "");
  const { turn } = session;
  const waiting = approvals.filter((item) => item.status !== "elsewhere");
  const first = waiting[0];
  if (first) {
    return phase("approval", "Waiting for your approval", {
      running: true,
      urgent: true,
      announce: `Needs your approval: ${first.command}`,
    });
  }
  if (turn.retry) {
    const left = Math.max(0, turn.retry.at + turn.retry.delayMs - now);
    return phase("retrying", left > 0 ? `Retrying in ${fmt.seconds(left)}` : "Retrying", {
      running: true,
      action: "cancelRetry",
      announce: "Retrying",
    });
  }
  if (turn.compacting) {
    return phase("compacting", "Compacting the context", {
      running: true,
      action: "cancelCompaction",
      announce: "Compacting the context",
    });
  }
  if (session.bash) {
    return phase("bash", `Running a command ${fmt.clock(now - session.bash.startedAt)}`, {
      running: true,
    });
  }
  const tools = Object.values(session.tools).filter((tool) => tool.status === "running");
  const only = tools[0];
  if (turn.running && tools.length === 1 && only) {
    return phase("tool", `Running ${only.name} ${fmt.clock(now - only.startedAt)}`, {
      running: true,
      announce: `Running ${only.name}`,
    });
  }
  if (turn.running && tools.length > 1) {
    const since = Math.min(...tools.map((tool) => tool.startedAt));
    return phase("tools", `Running ${fmt.num(tools.length)} tools ${fmt.clock(now - since)}`, {
      running: true,
      announce: `Running ${tools.length} tools`,
    });
  }
  if (turn.running && turn.chatWait)
    return phase("memory", "Waiting for memory", { running: true });
  if (turn.running && turn.stream === "writing") {
    const rate = liveRate(turn, now);
    return phase("writing", rate ? `Writing ${fmt.rate(rate)}` : "Writing", {
      running: true,
      announce: "Writing",
    });
  }
  if (turn.running && turn.stream === "thinking") {
    return phase("thinking", "Thinking", { running: true, announce: "Thinking" });
  }
  if (turn.running && turn.prefill && !turn.firstTokenAt && turn.prefill.total) {
    return phase(
      "prefill",
      `Reading the prompt ${fmt.num(turn.prefill.processed)} of ${fmt.num(turn.prefill.total)} tokens`,
      { running: true, announce: "Reading the prompt" },
    );
  }
  if (turn.running && session.summary?.admission === "queued" && !turn.requestAt) {
    return phase("admission", "Waiting for a model slot", { running: true });
  }
  if (turn.running) return phase("waiting", "Thinking", { running: true, announce: "Thinking" });
  if (session.pending.some((item) => item.status === "sending")) return phase("sending", "Sending");
  if (turn.error)
    return phase("failed", "Failed", { urgent: true, announce: `Failed: ${turn.error}` });
  if (turn.stopped) return phase("stopped", "Stopped", { announce: "Stopped" });
  return phase("idle", "", { announce: turn.endedAt ? "Done" : "" });
}
