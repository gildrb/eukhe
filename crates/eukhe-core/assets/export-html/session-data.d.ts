// The session data an HTML export embeds: the JSON template.ts decodes from the `session-data`
// script element. Each type mirrors the Rust item named in its doc comment, as serde writes it:
// an `Option` with `skip_serializing_if` is an optional key, an `Option` without one is `| null`.
//
// Two producers write the entries: a legacy session file (`session_data_from_file`, the
// `eukhe_types::session::FileEntry` rows with `eukhe_types::ai` messages) and a durable storage
// (`eukhe_core::durable::export::export_rows`: `message`, `compaction`, `custom_message` and
// `branch_summary` rows with `eukhe_types::pi_ai` messages). Where the two differ, a type is the
// union of both.
//
// Not modeled, though Rust can emit them: `FileEntry::Unknown` (an entry of an unknown `type`, or
// a known `type` whose payload failed validation, written verbatim) and
// `eukhe_types::ai::UserContentBlock::Raw` (a content block without a known `type`, written
// verbatim). Their shapes are arbitrary JSON; the template reads them as if they were the known
// kinds. `#[serde(flatten)] rest` maps (unknown extra keys kept by the legacy types) are left out
// too: extra keys do not change what the template reads.

/** `serde_json::Value`. */
type JsonValue = string | number | boolean | null | JsonValue[] | JsonObject;

/** `serde_json::Map<String, Value>` (`eukhe_types::JsonMap`, `eukhe_types::pi_ai::JsonObject`). */
type JsonObject = { [key: string]: JsonValue };

/** `eukhe_core::export_html::SessionExportData`. */
type SessionExportData = {
  header: SessionHeader;
  entries: SessionEntry[];
  /** The last entry's id; null when there are no entries. */
  leafId: string | null;
  /** Written by the daemon's live export only. */
  systemPrompt?: string;
  /** Written by the daemon's live export only. */
  tools?: ExportTool[];
  /** `eukhe_core::export_html::pre_render_custom_tools` output; no exporter writes it yet. */
  renderedTools?: RenderedTools;
};

/**
 * `eukhe_types::session::SessionHeader` under `FileEntry::Header` (legacy), or
 * `eukhe_core::durable::export::export_header` (durable: `type`, `version`, `id`, `timestamp`,
 * `cwd` only).
 */
type SessionHeader = {
  /**
   * Always "session"; optional here because `downloadSessionJson` writes `{ type: 'header',
   * ...header }`, as if a header could lack one.
   */
  type?: "session";
  version?: number;
  id: string;
  /** ISO-8601. */
  timestamp: string;
  cwd: string;
  parentSession?: string;
  rlmDepth?: number;
  git?: GitContext;
};

/** `eukhe_types::session::GitContext`. */
type GitContext = { repoUrl?: string; commit?: string; branch?: string };

/**
 * `eukhe_types::session::EntryBase` (legacy), or the `id`/`parentId`/`timestamp` keys
 * `export_rows` puts on every durable row.
 */
type EntryBase = {
  /**
   * `Option<String>` in Rust: null only on v1 lines, whose ids the load migration
   * (`migrate_v1_to_v2`) fills before the export reads them.
   */
  id: string;
  /** Null at the root of the tree. */
  parentId: string | null;
  /** ISO-8601; null on legacy lines written without one. */
  timestamp: string | null;
};

/** `FileEntry::Message`, or a durable `message` row. */
type MessageEntry = EntryBase & { type: "message"; message: AgentMessage };

/** `FileEntry::ThinkingLevelChange` (`eukhe_types::session::ThinkingLevelChangeEntry`); legacy only. */
type ThinkingLevelChangeEntry = EntryBase & { type: "thinking_level_change"; thinkingLevel: string };

/** `FileEntry::ServiceTierChange` (`eukhe_types::session::ServiceTierChangeEntry`); legacy only. */
type ServiceTierChangeEntry = EntryBase & { type: "service_tier_change"; serviceTier: ServiceTier | null };

/** `eukhe_types::ai::ServiceTier`. */
type ServiceTier = "auto" | "default" | "flex" | "scale" | "priority";

/** `FileEntry::ModelChange` (`eukhe_types::session::ModelChangeEntry`); legacy only. */
type ModelChangeEntry = EntryBase & { type: "model_change"; provider: string; modelId: string };

/**
 * `FileEntry::Compaction` (`eukhe_types::session::CompactionEntry`), or a durable `compaction`
 * row (`summary`, `firstKeptEntryId`, and `tokensBefore`: the context size the last assistant
 * reply before it reported).
 */
type CompactionEntry = EntryBase & {
  type: "compaction";
  summary: string;
  firstKeptEntryId: string;
  tokensBefore: number;
  details?: JsonValue;
  fromHook?: boolean;
  customInstructions?: string;
  usage?: Usage;
};

/**
 * `FileEntry::BranchSummary` (`eukhe_types::session::BranchSummaryEntry`), or a durable
 * `branch_summary` row (`eukhe_core::durable::entries::BranchSummaryData` without `timestamp`).
 */
type BranchSummaryEntry = EntryBase & {
  type: "branch_summary";
  fromId: string;
  summary: string;
  details?: JsonValue;
  fromHook?: boolean;
  usage?: Usage;
};

/** `FileEntry::Custom` (`eukhe_types::session::CustomEntry`); legacy only. */
type CustomEntry = EntryBase & { type: "custom"; customType: string; data?: JsonValue };

/** `FileEntry::ChildUsageAttributed` (`eukhe_types::session::ChildUsageAttributionEntry`); legacy only. */
type ChildUsageAttributedEntry = EntryBase & {
  type: "child_usage_attributed";
  targetId: string;
  childUsage: Usage;
  aggregateUsage: Usage;
  origin?: "spawn_task" | "agent_message" | "direct_user";
};

/** `FileEntry::Label` (`eukhe_types::session::LabelEntry`); legacy only. */
type LabelEntry = EntryBase & { type: "label"; targetId: string; label?: string };

/** `FileEntry::SessionInfo` (`eukhe_types::session::SessionInfoEntry`); legacy only. */
type SessionInfoEntry = EntryBase & { type: "session_info"; name?: string };

/** `FileEntry::SessionState` (`eukhe_types::session::SessionStateEntry`); legacy only. */
type SessionStateEntry = EntryBase & {
  type: "session_state";
  state: { status: "active" | "archived" | "crash" };
};

/** `FileEntry::GitState` (`eukhe_types::session::GitStateEntry`); legacy only. */
type GitStateEntry = EntryBase & { type: "git_state"; git: GitContext };

/**
 * `FileEntry::CustomMessage` (`eukhe_types::session::CustomMessageEntry`), or a durable
 * `custom_message` row (`eukhe_core::durable::export::file_entry`), whose `content` is null when
 * `custom_entry_content` finds none.
 */
type CustomMessageEntry = EntryBase & {
  type: "custom_message";
  customType: string;
  content: UserContent | null;
  details?: JsonValue;
  display: boolean;
};

/** A non-header `eukhe_types::session::FileEntry`, or a durable export row. */
type SessionEntry =
  | MessageEntry
  | ThinkingLevelChangeEntry
  | ServiceTierChangeEntry
  | ModelChangeEntry
  | CompactionEntry
  | BranchSummaryEntry
  | CustomEntry
  | ChildUsageAttributedEntry
  | LabelEntry
  | SessionInfoEntry
  | SessionStateEntry
  | GitStateEntry
  | CustomMessageEntry;

/**
 * `eukhe_types::session::AgentMessage` (legacy), or a durable message: the entry's first
 * `eukhe_types::pi_ai::Message` (user, assistant, tool result) or a `bashExecution` built from
 * `eukhe_core::durable::entries::BashEntryData`.
 */
type AgentMessage =
  | UserMessage
  | AssistantMessage
  | ToolResultMessage
  | BashExecutionMessage
  | CustomMessage
  | BranchSummaryMessage
  | CompactionSummaryMessage;

/** `eukhe_types::pi_ai::UserMessage`, `eukhe_types::ai::UserMessage`. */
type UserMessage = {
  role: "user";
  content: UserContent;
  /** Unix milliseconds. */
  timestamp: number;
};

/** `eukhe_types::pi_ai::AssistantMessage`, `eukhe_types::ai::AssistantMessage`. */
type AssistantMessage = {
  role: "assistant";
  content: AssistantContentBlock[];
  api: string;
  provider: string;
  model: string;
  responseModel?: string;
  responseId?: string;
  /** pi_ai only. */
  providerThinkingLevel?: string;
  /** pi_ai only (`eukhe_types::pi_ai::ModelThinkingLevel`). */
  thinkingLevel?: string;
  /** `eukhe_types::pi_ai::AssistantMessageDiagnostic`s. */
  diagnostics?: JsonObject[];
  usage: Usage;
  stopReason: StopReason;
  /** pi_ai only (`eukhe_types::pi_ai::DeferredHandle`). */
  deferred?: JsonObject;
  errorMessage?: string;
  /** pi_ai only. */
  rawStopReason?: string;
  /** Legacy only. */
  stopReasonRaw?: string;
  /** pi_ai only. */
  endTurn?: boolean;
  /** Unix milliseconds. */
  timestamp: number;
  /** pi_ai only. */
  durationMs?: number;
  /** `eukhe_types::pi_ai::ResponseTiming`. */
  timing?: JsonObject;
};

/** `eukhe_types::pi_ai::StopReason`; legacy `eukhe_types::ai::StopReason` lacks `pending` and `deferred`. */
type StopReason = "pending" | "stop" | "length" | "toolUse" | "error" | "aborted" | "deferred";

/** `eukhe_types::pi_ai::ToolResultMessage`, `eukhe_types::ai::ToolResultMessage`. */
type ToolResultMessage = {
  role: "toolResult";
  toolCallId: string;
  /** Absent on legacy rows written without a name (`skip_serializing_if = "String::is_empty"`). */
  toolName?: string;
  content: UserContentBlock[];
  /** The tool's own details JSON (null when written as null). */
  details?: ToolResultDetails | null;
  /** pi_ai only. */
  usage?: Usage;
  /** pi_ai only (`eukhe_types::pi_ai::NestedToolCalls`). */
  nestedCalls?: JsonObject;
  isError: boolean;
  /** Unix milliseconds. */
  timestamp: number;
  /** pi_ai only. */
  durationMs?: number;
};

/**
 * A tool result's `details`: whatever the tool serialized, an object for every product tool. The
 * template reads the edit tool's `diff` (`eukhe_docs::hashline` numbered diff) only.
 */
type ToolResultDetails = { diff?: string };

/** `eukhe_types::session::BashExecutionMessage`, or `BashEntryData` with `role` and `timestamp`. */
type BashExecutionMessage = {
  role: "bashExecution";
  content?: never;
  command: string;
  output: string;
  /** Absent while the command is still running (Rust's doc), and on a run that never got one. */
  exitCode?: number;
  cancelled: boolean;
  /** `eukhe_types::output::OmittedOutput`. */
  omitted?: JsonObject;
  artifact?: string;
  /** Unix milliseconds. */
  timestamp: number;
  excludeFromContext?: boolean;
};

/** `eukhe_types::session::CustomMessage`; legacy only. */
type CustomMessage = {
  role: "custom";
  customType: string;
  content: UserContent;
  display: boolean;
  details?: JsonValue;
  /** Unix milliseconds. */
  timestamp: number;
};

/** `eukhe_types::session::BranchSummaryMessage`; legacy only. */
type BranchSummaryMessage = {
  role: "branchSummary";
  content?: never;
  summary: string;
  fromId: string;
  /** Unix milliseconds. */
  timestamp: number;
};

/** `eukhe_types::session::CompactionSummaryMessage`; legacy only. */
type CompactionSummaryMessage = {
  role: "compactionSummary";
  content?: never;
  summary: string;
  tokensBefore: number;
  retainedMessageCount?: number;
  customInstructions?: string;
  /** Unix milliseconds. */
  timestamp: number;
};

/** `eukhe_types::pi_ai::UserContent`, `eukhe_types::ai::UserContent`. */
type UserContent = string | UserContentBlock[];

/** `eukhe_types::pi_ai::UserContentBlock`, `eukhe_types::ai::UserContentBlock` (but `Raw`). */
type UserContentBlock = TextContent | ImageContent;

/** `eukhe_types::pi_ai::AssistantContentBlock`, `eukhe_types::ai::AssistantContentBlock`. */
type AssistantContentBlock = TextContent | ThinkingContent | ToolCall;

/** `eukhe_types::pi_ai::TextContent`, `eukhe_types::ai::TextContent`. */
type TextContent = {
  type: "text";
  text: string;
  textSignature?: string;
  cacheBreakpoint?: "ephemeral";
};

/** `eukhe_types::pi_ai::ThinkingContent`, `eukhe_types::ai::ThinkingContent`. */
type ThinkingContent = {
  type: "thinking";
  thinking: string;
  thinkingSignature?: string;
  redacted?: boolean;
};

/** `eukhe_types::pi_ai::ImageContent`, `eukhe_types::ai::ImageContent`. */
type ImageContent = {
  type: "image";
  /** Base64. */
  data: string;
  mimeType: string;
};

/** `eukhe_types::pi_ai::ToolCall`, `eukhe_types::ai::ToolCall`. */
type ToolCall = {
  type: "toolCall";
  id: string;
  name: string;
  /** Not checked: a model can send any JSON object, whatever the tool's schema says. */
  arguments: JsonObject;
  thoughtSignature?: string;
  /** pi_ai only. */
  namespace?: string;
};

/** `eukhe_types::pi_ai::Usage`, `eukhe_types::ai::Usage`. */
type Usage = {
  input: number;
  output: number;
  cacheRead: number;
  cacheWrite: number;
  /** pi_ai only. */
  cacheWrite1h?: number;
  /** pi_ai only. */
  reasoning?: number;
  totalTokens: number;
  cost: UsageCost;
};

/** `eukhe_types::pi_ai::UsageCost`, `eukhe_types::ai::UsageCost`; dollars. */
type UsageCost = { input: number; output: number; cacheRead: number; cacheWrite: number; total: number };

/**
 * One `tools` item of `eukhe_daemon::session_export::durable::export_html`: the
 * `eukhe_types::pi_ai::Tool` fields `name`, `description`, and `parameters`
 * (`eukhe_types::pi_ai::ToolSchema`, written as its JSON schema).
 */
type ExportTool = { readonly name: string; readonly description: string; readonly parameters: ToolParametersSchema };

/**
 * A tool's JSON schema (any JSON schema object), with what the template reads: an object
 * schema's `properties` and `required`, or a schema without `properties`.
 */
type ToolParametersSchema = JsonObject &
  (
    | { readonly properties: { readonly [name: string]: ToolParameterSchema }; readonly required?: string[] }
    | { readonly properties?: undefined; readonly required?: string[] }
  );

/** One property schema of a tool's parameters (any JSON schema object). */
type ToolParameterSchema = JsonObject & {
  /** A JSON-schema type name, as template.ts reads it (a schema may also give a list of them). */
  type?: string;
  description?: string;
};

/** `renderedTools`: `eukhe_core::export_html::RenderedToolHtml` by tool-call id. */
type RenderedTools = { [toolCallId: string]: RenderedToolHtml };

/** `eukhe_core::export_html::RenderedToolHtml`. */
type RenderedToolHtml = {
  callHtml?: string;
  resultHtmlCollapsed?: string;
  resultHtmlExpanded?: string;
};
