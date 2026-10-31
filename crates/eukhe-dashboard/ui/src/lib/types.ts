// Wire shapes of the bridge and of the
// daemon's session values, as far as the app reads them. Daemon JSON is
// open-ended: unknown fields pass through untouched.

export type Json = null | boolean | number | string | Json[] | { [key: string]: Json };

export type Cursor = { generation: string; sequence: number };

export type ModelRef = { provider: string; id: string; name?: string; modelId?: string };

export type TextBlock = { type: "text"; text: string };
export type ThinkingBlock = { type: "thinking"; thinking: string };
export type ImageBlock = { type: "image"; data: string; mimeType: string };
export type ToolCallBlock = { type: "toolCall"; id: string; name: string; arguments: unknown };
export type ContentBlock = TextBlock | ThinkingBlock | ImageBlock | ToolCallBlock;
export type Content = string | ContentBlock[];

export type Usage = { input: number; output: number; cacheRead?: number; cacheWrite?: number };
export type Timing = { firstTokenMs?: number; lastTokenMs?: number };

export type Message = {
  role:
    | "user"
    | "assistant"
    | "toolResult"
    | "custom"
    | "bashExecution"
    | "compactionSummary"
    | "branchSummary";
  content?: Content;
  timestamp?: number | string;
  // assistant
  usage?: Usage;
  timing?: Timing;
  durationMs?: number;
  stopReason?: string;
  errorMessage?: string;
  model?: string;
  responseModel?: string;
  // user
  admissionId?: string;
  details?: { admissionId?: string };
  // toolResult
  toolCallId?: string;
  isError?: boolean;
  // custom
  customType?: string;
  display?: boolean;
  // bashExecution
  command?: string;
  output?: string;
  exitCode?: number;
  cancelled?: boolean;
  // summaries
  summary?: string;
};

export type QueueItem = { text: string };
export type Queue = { queuedCount: number; steering: QueueItem[]; followUps: QueueItem[] };

export type ContextUsage = { tokens: number; contextWindow: number; percent?: number };

/** The daemon's AgentConnectionState (`get_connection_state`). */
export type AgentState = {
  cwd?: string;
  model?: ModelRef | null;
  thinkingLevel?: string;
  availableThinkingLevels?: string[];
  /** The tiers the model honors, as the CLI's /tier lists them (`["default"]` without any). */
  availableServiceTiers?: string[];
  serviceTier?: string | null;
  isStreaming?: boolean;
  isCompacting?: boolean;
  steeringMode?: string;
  followUpMode?: string;
  sessionName?: string | null;
  autoCompactionEnabled?: boolean;
  sessionActions?: Queue;
  scopedModels?: { model: ModelRef }[];
  contextUsage?: ContextUsage;
  goal?: unknown;
  [key: string]: unknown;
};

export type Summary = { sessionName?: string; admission?: string; [key: string]: unknown };

export type OpenReply = {
  session: { id: string; path: string };
  state: AgentState | null;
  summary: Summary | null;
  messages: Message[] | null;
  cursor: Cursor | null;
  replay: "complete" | "partial" | "unavailable" | null;
};

export type SessionRow = { id: string; path: string; cwd: string; title: string; modified: string };

export type PromptProgress = { processed: number; total: number; cache: number; timeMs: number };

export type StreamUpdate = { type: string; delta?: string };

/** The 27 SessionEvent types the reducer folds. */
export type SessionEvent =
  | { type: "agent_start" }
  | { type: "agent_end" }
  | { type: "turn_start" }
  | { type: "turn_end"; error?: string }
  | { type: "prompt_progress"; progress: PromptProgress }
  | { type: "message_start"; message: Message; assistantMessageEvent?: StreamUpdate }
  | { type: "message_update"; message: Message; assistantMessageEvent?: StreamUpdate }
  | { type: "message_end"; message: Message }
  | { type: "tool_execution_start"; toolCallId: string; toolName: string; args: unknown }
  | {
      type: "tool_execution_update";
      toolCallId: string;
      toolName: string;
      args: unknown;
      partialResult: unknown;
    }
  | {
      type: "tool_execution_end";
      toolCallId: string;
      toolName: string;
      result: unknown;
      isError: boolean;
    }
  | {
      type: "auto_retry_start";
      attempt: number;
      maxAttempts?: number;
      delayMs: number;
      errorMessage: string;
      backupModel?: string;
    }
  | { type: "auto_retry_end"; success: boolean; finalError?: string }
  | { type: "compaction_start"; reason: string }
  | { type: "compaction_summary_delta"; delta: string }
  | {
      type: "compaction_end";
      aborted?: boolean;
      errorMessage?: string;
      result?: { summary?: string };
    }
  | { type: "session_info_changed"; name?: string | null }
  | { type: "service_tier_changed"; serviceTier: string }
  | { type: "session_action_update"; actions: Queue }
  | { type: "goal_update"; goal: unknown }
  | { type: "chat_turn_wait"; waiting: boolean }
  | { type: "memory_update"; update: unknown }
  | { type: "agent_relay"; from: string; to: string; text: string }
  | { type: "bash_start"; command: string }
  | { type: "bash_output"; chunk: string }
  | { type: "bash_end"; errorMessage?: string }
  | { type: "refine_complete" }
  | { type: "refine_failed"; error: string }
  | { type: "ipython_sent_agent_message" };

/** `effects`: every effect of the step, by name (read, write, exec, net, outside, protected, secret). */
export type ApprovalRequest = {
  requestId: string;
  step: number;
  command: string;
  effects: string[];
};

export type ServerFrame =
  | { type: "hello"; protocol: number; build: string; ops: string[] }
  | { type: "reply"; id: number; data: unknown }
  | { type: "failure"; id: number; error: string }
  | { type: "event"; event: SessionEvent; cursor?: Cursor }
  | { type: "approval"; request: ApprovalRequest }
  | { type: "approval_settled"; requestId: string }
  | { type: "resync"; reason: string }
  | { type: "unavailable"; error: string }
  | { type: "unpaired"; error: string };

export type Model = { provider: string; id: string; name?: string };

export type Image = { data: string; mimeType: string; preview: string; name: string };
