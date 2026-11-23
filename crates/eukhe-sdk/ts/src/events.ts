import type { PlanEntry, SessionUpdate, StopReason, ToolCallContent, ToolKind } from "@agentclientprotocol/sdk";

import type { RunReport } from "./extensions.ts";

/** One event of a prompt turn; switch on `$`. The last event of a turn is `TurnEnd`. */
export type EukheEvent =
  /** A piece of the assistant's answer. */
  | { $: "Text"; text: string }
  /** A piece of the model's reasoning. */
  | { $: "Thinking"; text: string }
  /** A tool call began. `input` is the tool's raw arguments. */
  | { $: "ToolCallStart"; id: string; title: string; kind: ToolKind | null; input: unknown }
  /** A running tool call changed; `null` fields are unchanged. */
  | {
      $: "ToolCallUpdate";
      id: string;
      title: string | null;
      content: readonly ToolCallContent[] | null;
      output: unknown;
    }
  /** A tool call finished. */
  | {
      $: "ToolCallEnd";
      id: string;
      outcome: "completed" | "failed";
      content: readonly ToolCallContent[] | null;
      output: unknown;
    }
  /** The agent's whole current plan (replaces the previous one). */
  | { $: "Plan"; entries: readonly PlanEntry[] }
  /** The end-of-turn report: answer, checks, irreversible effects that ran, what is left. */
  | { $: "RunReport"; report: RunReport }
  /** The turn ended; `stopReason` is `cancelled` after {@link Session.cancel}. */
  | { $: "TurnEnd"; stopReason: StopReason };

/** The SDK events of one ACP `session/update` (none for updates the SDK does not surface). */
export function eventsOfUpdate(update: SessionUpdate): readonly EukheEvent[] {
  switch (update.sessionUpdate) {
    case "agent_message_chunk":
      return update.content.type === "text" ? [{ $: "Text", text: update.content.text }] : [];
    case "agent_thought_chunk":
      return update.content.type === "text" ? [{ $: "Thinking", text: update.content.text }] : [];
    case "tool_call":
      return [
        {
          $: "ToolCallStart",
          id: update.toolCallId,
          title: update.title,
          kind: update.kind ?? null,
          input: update.rawInput,
        },
      ];
    case "tool_call_update":
      return [toolCallProgress(update)];
    case "plan":
      return [{ $: "Plan", entries: update.entries }];
    case "user_message_chunk":
    case "plan_update":
    case "plan_removed":
    case "available_commands_update":
    case "current_mode_update":
    case "config_option_update":
    case "session_info_update":
    case "usage_update":
    case "notice":
    case "compaction_update":
    case "compaction_summary_chunk":
    case "subagent_update":
    case "session_message":
    case "session_message_chunk":
      return [];
    default: {
      const _: never = update;
      return _;
    }
  }
}

function toolCallProgress(update: Extract<SessionUpdate, { sessionUpdate: "tool_call_update" }>): EukheEvent {
  const content = update.content ?? null;
  switch (update.status) {
    case "completed":
    case "failed":
      return { $: "ToolCallEnd", id: update.toolCallId, outcome: update.status, content, output: update.rawOutput };
    case "pending":
    case "in_progress":
    case null:
    case undefined:
      return {
        $: "ToolCallUpdate",
        id: update.toolCallId,
        title: update.title ?? null,
        content,
        output: update.rawOutput,
      };
    default: {
      const _: never = update.status;
      return _;
    }
  }
}
