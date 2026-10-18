//! The declaration of every cvar (docs/control.md S4): each setting of
//! `settings.json` once, by the dotted path of its key.
//!
//! Global: one value for the whole family, read from the global config
//! only (a daemon-wide limit, a security gate, a machine-level path).
//! Local: each agent may have its own value. `persist`: an agent may write
//! its sets to its cfg. `replicate`: clients see the value.
//!
//! The Global cvars are the settings eukhe read from the global document
//! only before cvars (`rlmMaxDepth`, `providerMaxInFlight`,
//! `providerMaxQueued`, `idleEvictionMinutes`, the session archive rules,
//! `allowedModels`, `factory.enabled`, `trustedProjects`, `gateway.*`,
//! `ssh.hosts`)
//! plus `memory.model` and `memory.thinking`: the chat-memory compactor is
//! one per daemon, built over the agent dir alone
//! (`memory::summarizer::configured_memory_model` and
//! `SettingsSummarizer::new` read `SettingsManager::create(agent_dir,
//! agent_dir)`), and the client's memory-model picker showed the global
//! value. Every other setting is read through a session's cwd (the merged
//! global + project document), so it stays Local: a value per agent keeps
//! that behavior. `subagentMaxConcurrency` is daemon-wide in effect but
//! read with the spawning session's cwd (`rlm_children/durable_host.rs`),
//! and `sessionDir` is read with the cwd at startup (`eukhe-cli` `lib.rs`),
//! so both stay Local.
//!
//! Persist is off for the settings an untrusted project may not set
//! (`settings::trust`: programs, commands, code sources, execution gates,
//! where sessions live) and for the ones eukhe writes itself
//! (`recentModels`, `onboardingCompleted`). Replicate is on for what a
//! client renders or reads (the TUI `ClientSettings` getters, the session
//! switches, the model and thinking defaults the client shows).
//!
//! A setting with no default of its own is Text `""`, the empty list, or
//! Json `null` (its reader takes the provider's or the Harness's default).

use super::{CvarScope, CvarType, Decl, Init};

#[cfg(test)]
mod tests;

pub(crate) const QUEUE_MODES: &[&str] = &["all", "one-at-a-time"];
pub(crate) const TRANSPORTS: &[&str] = &["auto", "sse", "web-socket", "websocket-cached"];
pub(crate) const THINKING_LEVELS: &[&str] =
    &["off", "minimal", "low", "medium", "high", "xhigh", "max"];
/// The thinking levels plus `""`: unset (the model's own default).
pub(crate) const OPTIONAL_THINKING_LEVELS: &[&str] = &[
    "", "off", "minimal", "low", "medium", "high", "xhigh", "max",
];
pub(crate) const SERVICE_TIERS: &[&str] = &["auto", "default", "flex", "scale", "priority"];
pub(crate) const TREE_FILTER_MODES: &[&str] =
    &["default", "no-tools", "user-only", "labeled-only", "all"];
pub(crate) const CHAT_DETAILS: &[&str] = &["overview", "details", "all"];
pub(crate) const MERMAID_MODES: &[&str] = &["off", "final", "streaming"];

pub const ONBOARDING_SHOWN: Decl = Decl {
    id: "onboardingShown",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(false),
};

/// The legacy first-run flag; the load migration copies it to
/// `onboardingShown` (`settings::merge::migrate`).
pub const ONBOARDING_COMPLETED: Decl = Decl {
    id: "onboardingCompleted",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: false,
    replicate: false,
    init: Init::Bool(false),
};

pub const DEFAULT_PROVIDER: Decl = Decl {
    id: "defaultProvider",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text(""),
};

pub const DEFAULT_MODEL: Decl = Decl {
    id: "defaultModel",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text(""),
};

pub const SUBAGENT_DEFAULT_MODEL: Decl = Decl {
    id: "subagentDefaultModel",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Text(""),
};

pub const RECENT_MODELS: Decl = Decl {
    id: "recentModels",
    ty: CvarType::List,
    scope: CvarScope::Local,
    persist: false,
    replicate: true,
    init: Init::EmptyList,
};

pub const AUXILIARY_MODEL: Decl = Decl {
    id: "auxiliaryModel",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Text(""),
};

pub const DEFAULT_THINKING_LEVEL: Decl = Decl {
    id: "defaultThinkingLevel",
    ty: CvarType::Choice(OPTIONAL_THINKING_LEVELS),
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text(""),
};

pub const DEFAULT_SERVICE_TIER: Decl = Decl {
    id: "defaultServiceTier",
    ty: CvarType::Choice(SERVICE_TIERS),
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text("default"),
};

pub const RLM_MAX_DEPTH: Decl = Decl {
    id: "rlmMaxDepth",
    ty: CvarType::Json,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::Null,
};

/// `{providerId: n}`: shared by every process of the agent dir.
pub const PROVIDER_MAX_IN_FLIGHT: Decl = Decl {
    id: "providerMaxInFlight",
    ty: CvarType::Json,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::Null,
};

/// `crate::admission::DEFAULT_PROVIDER_MAX_QUEUED`.
pub const PROVIDER_MAX_QUEUED: Decl = Decl {
    id: "providerMaxQueued",
    ty: CvarType::Nat,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::Nat(64),
};

pub const SUBAGENT_MAX_CONCURRENCY: Decl = Decl {
    id: "subagentMaxConcurrency",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(32),
};

/// `0` takes the default.
pub const SUBAGENT_STALL_MS: Decl = Decl {
    id: "subagentStallMs",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(600_000),
};

/// `0` takes the default.
pub const TOOL_BLOCKING_BUDGET_MS: Decl = Decl {
    id: "toolBlockingBudgetMs",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(30_000),
};

/// The Harness's `DEFAULT_MAX_TOOL_ROUNDS`; `0` takes it.
pub const MAX_TOOL_ROUNDS: Decl = Decl {
    id: "maxToolRounds",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(250),
};

/// `number | "off" | "none"`; anything else reads as the default.
pub const IDLE_EVICTION_MINUTES: Decl = Decl {
    id: "idleEvictionMinutes",
    ty: CvarType::Json,
    scope: CvarScope::Global,
    persist: false,
    replicate: true,
    init: Init::Nat(90),
};

/// `number | "off" | "none"`; anything else reads as the default.
pub const SESSION_ARCHIVE_MAX_AGE_DAYS: Decl = Decl {
    id: "sessionArchiveMaxAgeDays",
    ty: CvarType::Json,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::Nat(30),
};

/// `number | "off" | "none"` (`0` is off); anything else reads as the
/// default.
pub const SESSION_ARCHIVE_MAX_SESSIONS: Decl = Decl {
    id: "sessionArchiveMaxSessions",
    ty: CvarType::Json,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::Nat(200),
};

pub const TRANSPORT: Decl = Decl {
    id: "transport",
    ty: CvarType::Choice(TRANSPORTS),
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text("auto"),
};

pub const STEERING_MODE: Decl = Decl {
    id: "steeringMode",
    ty: CvarType::Choice(QUEUE_MODES),
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text("all"),
};

pub const FOLLOW_UP_MODE: Decl = Decl {
    id: "followUpMode",
    ty: CvarType::Choice(QUEUE_MODES),
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text("one-at-a-time"),
};

pub const THEME: Decl = Decl {
    id: "theme",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text(""),
};

pub const COMPACTION_ENABLED: Decl = Decl {
    id: "compaction.enabled",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(true),
};

/// The Harness's `DEFAULT_COMPACTION_POLICY.reserve_tokens` (TS
/// `DEFAULT_COMPACTION_SETTINGS`).
pub const COMPACTION_RESERVE_TOKENS: Decl = Decl {
    id: "compaction.reserveTokens",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(16_384),
};

/// Twice the Harness's `DEFAULT_COMPACTION_POLICY.keep_recent_tokens`
/// (20,000): the keep window counts system entries, and eukhe's system
/// prompt alone is near 20,000 tokens, so the kept tail would hold almost
/// no conversation. The Harness caps it per model at half the size where
/// compaction starts (`CompactionPolicy::keep_window`).
pub const COMPACTION_KEEP_RECENT_TOKENS: Decl = Decl {
    id: "compaction.keepRecentTokens",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(40_000),
};

pub const COMPACTION_AGENT_CALLABLE: Decl = Decl {
    id: "compaction.agentCallable",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Bool(true),
};

/// When on, the Harness asks the provider's own token counter
/// (`count_tokens`) for the input tokens of each request before the
/// compaction threshold check. This adds one request to the provider per
/// generation. A provider without a counter, or a failed count, uses the
/// local estimate, and the Harness logs it.
pub const COMPACTION_PROVIDER_TOKEN_COUNT: Decl = Decl {
    id: "compaction.providerTokenCount",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Bool(false),
};

/// `provider/model-id`; unset falls back to `auxiliaryModel`.
pub const MEMORY_MODEL: Decl = Decl {
    id: "memory.model",
    ty: CvarType::Text,
    scope: CvarScope::Global,
    persist: false,
    replicate: true,
    init: Init::Text(""),
};

pub const MEMORY_THINKING: Decl = Decl {
    id: "memory.thinking",
    ty: CvarType::Choice(THINKING_LEVELS),
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::Text("medium"),
};

/// `crate::memory::SETTLE_TIMEOUT`; `0` takes it.
pub const MEMORY_SETTLE_TIMEOUT_MS: Decl = Decl {
    id: "memory.settleTimeoutMs",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(20_000),
};

pub const AUTO_REFINE_ENABLED: Decl = Decl {
    id: "autoRefine.enabled",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Bool(true),
};

/// Clamped to at least 1 by the reader.
pub const AUTO_REFINE_TURN_INTERVAL: Decl = Decl {
    id: "autoRefine.turnInterval",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(25),
};

pub const AUTO_REFINE_COMPACT: Decl = Decl {
    id: "autoRefine.compact",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Bool(true),
};

/// Twenty minutes.
pub const AUTO_REFINE_COOLDOWN_MS: Decl = Decl {
    id: "autoRefine.cooldownMs",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(1_200_000),
};

pub const FACTORY_ENABLED: Decl = Decl {
    id: "factory.enabled",
    ty: CvarType::Bool,
    scope: CvarScope::Global,
    persist: false,
    replicate: true,
    init: Init::Bool(false),
};

/// The TS default reserve budget.
pub const BRANCH_SUMMARY_RESERVE_TOKENS: Decl = Decl {
    id: "branchSummary.reserveTokens",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(16_384),
};

pub const BRANCH_SUMMARY_SKIP_PROMPT: Decl = Decl {
    id: "branchSummary.skipPrompt",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(false),
};

pub const RETRY_ENABLED: Decl = Decl {
    id: "retry.enabled",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(true),
};

/// The Harness's `DEFAULT_RETRY_POLICY.max_retries`.
pub const RETRY_MAX_RETRIES: Decl = Decl {
    id: "retry.maxRetries",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(3),
};

/// The Harness's `DEFAULT_RETRY_POLICY.base_delay_ms`.
pub const RETRY_BASE_DELAY_MS: Decl = Decl {
    id: "retry.baseDelayMs",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(2_000),
};

/// Provider failover (another provider serving the same model takes the
/// turn when one exhausts its retries).
pub const RETRY_FAILOVER_ENABLED: Decl = Decl {
    id: "retry.failover.enabled",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Bool(true),
};

/// `durable::models::failover::MAX_TOTAL_PROVIDER_RETRIES` (also the
/// ceiling the reader clamps to).
pub const RETRY_FAILOVER_MAX_RETRIES: Decl = Decl {
    id: "retry.failover.maxRetries",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(8),
};

pub const RETRY_FAILOVER_BASE_DELAY_MS: Decl = Decl {
    id: "retry.failover.baseDelayMs",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(1_000),
};

pub const RETRY_FAILOVER_MAX_DELAY_MS: Decl = Decl {
    id: "retry.failover.maxDelayMs",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(30_000),
};

/// A whole number of ms; unset is each provider's own request timeout.
pub const RETRY_PROVIDER_TIMEOUT_MS: Decl = Decl {
    id: "retry.provider.timeoutMs",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

/// The Harness's `DEFAULT_RETRY_POLICY.max_agent_delay_ms`; also the
/// bounded-wait cap of the quota park.
pub const RETRY_PROVIDER_MAX_RETRY_DELAY_MS: Decl = Decl {
    id: "retry.provider.maxRetryDelayMs",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(60_000),
};

/// A whole number of ms (`0` disables); unset is the provider default.
pub const RETRY_PROVIDER_STREAM_IDLE_TIMEOUT_MS: Decl = Decl {
    id: "retry.provider.streamIdleTimeoutMs",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

/// A whole number (`0` takes the provider default); unset is the provider
/// default.
pub const RETRY_PROVIDER_STREAM_REPEAT_LIMIT: Decl = Decl {
    id: "retry.provider.streamRepeatLimit",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

pub const RETRY_WAIT_ENABLED: Decl = Decl {
    id: "retry.provider.waitForUsage.enabled",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

pub const RETRY_WAIT_BASE_DELAY_MS: Decl = Decl {
    id: "retry.provider.waitForUsage.baseDelayMs",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

pub const RETRY_WAIT_MAX_DELAY_MS: Decl = Decl {
    id: "retry.provider.waitForUsage.maxDelayMs",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

pub const RETRY_WAIT_MAX_ATTEMPTS: Decl = Decl {
    id: "retry.provider.waitForUsage.maxAttempts",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

pub const RETRY_WAIT_MAX_WAIT_MS: Decl = Decl {
    id: "retry.provider.waitForUsage.maxWaitMs",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

/// `durable::models::park::DEFAULT_PROVIDER_PARK_POLICY.pause_until_reset`.
pub const RETRY_WAIT_PAUSE_UNTIL_RESET: Decl = Decl {
    id: "retry.provider.waitForUsage.pauseUntilReset",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Bool(true),
};

/// `DEFAULT_PROVIDER_PARK_POLICY.max_pause_ms` (24 h).
pub const RETRY_WAIT_MAX_PAUSE_MS: Decl = Decl {
    id: "retry.provider.waitForUsage.maxPauseMs",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(86_400_000),
};

/// `DEFAULT_PROVIDER_PARK_POLICY.max_parks`.
pub const RETRY_WAIT_MAX_PARKS: Decl = Decl {
    id: "retry.provider.waitForUsage.maxParks",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(8),
};

pub const PROVIDER_BACKUP_MODEL: Decl = Decl {
    id: "providerBackupModel",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Text(""),
};

pub const IMAGE_MODEL: Decl = Decl {
    id: "imageModel",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text(""),
};

/// `number | "unlimited"`.
pub const AUTONOMOUS_MAX_CONTINUATIONS: Decl = Decl {
    id: "autonomous.maxContinuations",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

/// `number | "unlimited"`.
pub const AUTONOMOUS_MAX_TURNS: Decl = Decl {
    id: "autonomous.maxTurns",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

/// `number | "unlimited"`.
pub const AUTONOMOUS_MAX_TOKENS: Decl = Decl {
    id: "autonomous.maxTokens",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

/// `number | "unlimited"`.
pub const AUTONOMOUS_TIMEOUT_MS: Decl = Decl {
    id: "autonomous.timeoutMs",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

/// `0` takes the default.
pub const DIRECTORS_STACK_CAP: Decl = Decl {
    id: "directors.stackCap",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(8),
};

/// `0` takes the default.
pub const DIRECTORS_MAX_STEPS: Decl = Decl {
    id: "directors.maxSteps",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Nat(200),
};

pub const SHELL_PATH: Decl = Decl {
    id: "shellPath",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: false,
    replicate: false,
    init: Init::Text(""),
};

pub const QUIET_STARTUP: Decl = Decl {
    id: "quietStartup",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: false,
    replicate: true,
    init: Init::Bool(false),
};

pub const SHELL_COMMAND_PREFIX: Decl = Decl {
    id: "shellCommandPrefix",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: false,
    replicate: false,
    init: Init::Text(""),
};

pub const NPM_COMMAND: Decl = Decl {
    id: "npmCommand",
    ty: CvarType::List,
    scope: CvarScope::Local,
    persist: false,
    replicate: false,
    init: Init::EmptyList,
};

/// `{name: server}`.
pub const MCP_SERVERS: Decl = Decl {
    id: "mcpServers",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: false,
    replicate: false,
    init: Init::Null,
};

pub const MCP_CATALOG_SOURCES: Decl = Decl {
    id: "mcpCatalogSources",
    ty: CvarType::List,
    scope: CvarScope::Local,
    persist: false,
    replicate: false,
    init: Init::EmptyList,
};

/// Package sources (strings or objects).
pub const PACKAGES: Decl = Decl {
    id: "packages",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: false,
    replicate: false,
    init: Init::Null,
};

pub const SKILLS: Decl = Decl {
    id: "skills",
    ty: CvarType::List,
    scope: CvarScope::Local,
    persist: false,
    replicate: false,
    init: Init::EmptyList,
};

pub const PROMPTS: Decl = Decl {
    id: "prompts",
    ty: CvarType::List,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::EmptyList,
};

pub const THEMES: Decl = Decl {
    id: "themes",
    ty: CvarType::List,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::EmptyList,
};

pub const ENABLE_SKILL_COMMANDS: Decl = Decl {
    id: "enableSkillCommands",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(true),
};

pub const ENABLE_BUILTIN_SKILLS: Decl = Decl {
    id: "enableBuiltinSkills",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(true),
};

pub const TERMINAL_SHOW_IMAGES: Decl = Decl {
    id: "terminal.showImages",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(true),
};

pub const TERMINAL_CLEAR_ON_SHRINK: Decl = Decl {
    id: "terminal.clearOnShrink",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(false),
};

pub const TERMINAL_SHOW_TERMINAL_PROGRESS: Decl = Decl {
    id: "terminal.showTerminalProgress",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(false),
};

pub const TERMINAL_FULLSCREEN: Decl = Decl {
    id: "terminal.fullscreen",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(false),
};

/// `0` reads as 1.
pub const TERMINAL_STREAM_PACE_MIN_CHARS: Decl = Decl {
    id: "terminal.streamPace.minChars",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Nat(2),
};

pub const TERMINAL_STREAM_PACE_LAG: Decl = Decl {
    id: "terminal.streamPace.lag",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Nat(3),
};

pub const IMAGES_AUTO_RESIZE: Decl = Decl {
    id: "images.autoResize",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(true),
};

pub const IMAGES_BLOCK_IMAGES: Decl = Decl {
    id: "images.blockImages",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(false),
};

/// Model-scope patterns; empty is no filter.
pub const ENABLED_MODELS: Decl = Decl {
    id: "enabledModels",
    ty: CvarType::List,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::EmptyList,
};

/// The daemon model allowlist; empty is unrestricted.
pub const ALLOWED_MODELS: Decl = Decl {
    id: "allowedModels",
    ty: CvarType::List,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::EmptyList,
};

pub const TREE_FILTER_MODE: Decl = Decl {
    id: "treeFilterMode",
    ty: CvarType::Choice(TREE_FILTER_MODES),
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text("user-only"),
};

pub const CHAT_DETAIL: Decl = Decl {
    id: "chatDetail",
    ty: CvarType::Choice(CHAT_DETAILS),
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text("overview"),
};

pub const THINKING_BUDGET_MINIMAL: Decl = Decl {
    id: "thinkingBudgets.minimal",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

pub const THINKING_BUDGET_LOW: Decl = Decl {
    id: "thinkingBudgets.low",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

pub const THINKING_BUDGET_MEDIUM: Decl = Decl {
    id: "thinkingBudgets.medium",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

pub const THINKING_BUDGET_HIGH: Decl = Decl {
    id: "thinkingBudgets.high",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Null,
};

pub const EDITOR_PADDING_X: Decl = Decl {
    id: "editorPaddingX",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Nat(0),
};

pub const AUTOCOMPLETE_MAX_VISIBLE: Decl = Decl {
    id: "autocompleteMaxVisible",
    ty: CvarType::Nat,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Nat(5),
};

pub const SHOW_HARDWARE_CURSOR: Decl = Decl {
    id: "showHardwareCursor",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(false),
};

pub const MARKDOWN_CODE_BLOCK_INDENT: Decl = Decl {
    id: "markdown.codeBlockIndent",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text("  "),
};

pub const MARKDOWN_MERMAID: Decl = Decl {
    id: "markdown.mermaid",
    ty: CvarType::Choice(MERMAID_MODES),
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Text("streaming"),
};

pub const WARNINGS_ANTHROPIC_EXTRA_USAGE: Decl = Decl {
    id: "warnings.anthropicExtraUsage",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(true),
};

/// `~`-relative allowed; unset is `<agentDir>/sessions`.
pub const SESSION_DIR: Decl = Decl {
    id: "sessionDir",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: false,
    replicate: false,
    init: Init::Text(""),
};

pub const REQUEST_TIMING: Decl = Decl {
    id: "requestTiming",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Bool(false),
};

pub const TRUSTED_PROJECTS: Decl = Decl {
    id: "trustedProjects",
    ty: CvarType::List,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::EmptyList,
};

pub const GATEWAY_SIGNAL_ACCOUNT: Decl = Decl {
    id: "gateway.signal.account",
    ty: CvarType::Text,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::Text(""),
};

pub const GATEWAY_SIGNAL_ALLOW: Decl = Decl {
    id: "gateway.signal.allow",
    ty: CvarType::List,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::EmptyList,
};

pub const GATEWAY_SIGNAL_CLI_PATH: Decl = Decl {
    id: "gateway.signal.cliPath",
    ty: CvarType::Text,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::Text(""),
};

pub const GATEWAY_SIGNAL_CWD: Decl = Decl {
    id: "gateway.signal.cwd",
    ty: CvarType::Text,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::Text(""),
};

/// Where the session's kernel runs (S3); parsed by
/// `kernel::transport::KernelTransportSettings`. Routes code execution,
/// so an untrusted project may not set it and an agent never saves it.
pub const KERNEL_TRANSPORT: Decl = Decl {
    id: "kernelTransport",
    ty: CvarType::Json,
    scope: CvarScope::Local,
    persist: false,
    replicate: false,
    init: Init::Null,
};

pub(crate) const SHELL_EFFECTS: &[&str] = &["read", "write", "exec", "net"];

/// The effects a shell command may have without asking. An execution
/// gate: an untrusted project may not set it and an agent never saves it.
pub const SHELL_AUTO_EFFECTS: Decl = Decl {
    id: "shell.autoEffects",
    ty: CvarType::ChoiceList(SHELL_EFFECTS),
    scope: CvarScope::Local,
    persist: false,
    replicate: false,
    init: Init::List(&["read"]),
};

/// The hosts an `ssh://` read may reach (docs/tools.md S7.5): new
/// outbound traffic, so a project may not set it and an agent never
/// saves it. Empty: every `ssh://` read is rejected.
pub const SSH_HOSTS: Decl = Decl {
    id: "ssh.hosts",
    ty: CvarType::List,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::EmptyList,
};

/// `modelRoles.<role>`: the primary model of an S9 role (`local/<id>` or
/// `provider/model`); `""`: unset (`eukhe_tiny::chain`).
const fn model_role(id: &'static str) -> Decl {
    Decl {
        id,
        ty: CvarType::Text,
        scope: CvarScope::Local,
        persist: true,
        replicate: false,
        init: Init::Text(""),
    }
}

pub const MODEL_ROLE_TINY: Decl = model_role("modelRoles.tiny");
pub const MODEL_ROLE_JUDGE: Decl = model_role("modelRoles.judge");
pub const MODEL_ROLE_TRANSLATE: Decl = model_role("modelRoles.translate");
pub const MODEL_ROLE_SPEECH: Decl = model_role("modelRoles.speech");
pub const MODEL_ROLE_DICTATION: Decl = model_role("modelRoles.dictation");

/// `retry.fallbackChains.<role>`: a list of selectors; `null`: unset (the
/// role's built-in priority); `[]`: the primary only.
const fn fallback_chain(id: &'static str) -> Decl {
    Decl {
        id,
        ty: CvarType::Json,
        scope: CvarScope::Local,
        persist: true,
        replicate: false,
        init: Init::Null,
    }
}

pub const FALLBACK_CHAIN_TINY: Decl = fallback_chain("retry.fallbackChains.tiny");
pub const FALLBACK_CHAIN_JUDGE: Decl = fallback_chain("retry.fallbackChains.judge");
pub const FALLBACK_CHAIN_TRANSLATE: Decl = fallback_chain("retry.fallbackChains.translate");
pub const FALLBACK_CHAIN_SPEECH: Decl = fallback_chain("retry.fallbackChains.speech");
pub const FALLBACK_CHAIN_DICTATION: Decl = fallback_chain("retry.fallbackChains.dictation");

/// The tiny-model worker's execution device; part of its launch tag.
pub const PROVIDERS_TINY_MODEL_DEVICE: Decl = Decl {
    id: "providers.tinyModelDevice",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Text("cpu"),
};

/// The tiny-model weight precision override; `""`: the catalog's files.
pub const PROVIDERS_TINY_MODEL_DTYPE: Decl = Decl {
    id: "providers.tinyModelDtype",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Text(""),
};

/// The ONNX Runtime library the worker loads (code): Global, never saved
/// by an agent; `""`: `ORT_DYLIB_PATH`, else the loader's search path.
pub const PROVIDERS_TINY_RUNTIME_LIBRARY: Decl = Decl {
    id: "providers.tinyRuntimeLibrary",
    ty: CvarType::Text,
    scope: CvarScope::Global,
    persist: false,
    replicate: false,
    init: Init::Text(""),
};

/// Generated session titles (opt-out).
pub const TITLES_GENERATE: Decl = Decl {
    id: "titles.generate",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Bool(true),
};

/// The local text-to-speech voice.
pub const TTS_LOCAL_VOICE: Decl = Decl {
    id: "tts.localVoice",
    ty: CvarType::Text,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Text("af_heart"),
};

/// Dictation into the editor draft (the `dictation` role): off until the
/// user turns it on. Replicated: the TUI reads it at each dictation key.
pub const STT_ENABLED: Decl = Decl {
    id: "stt.enabled",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: true,
    init: Init::Bool(false),
};

pub const DECLS: &[Decl] = &[
    ONBOARDING_SHOWN,
    ONBOARDING_COMPLETED,
    DEFAULT_PROVIDER,
    DEFAULT_MODEL,
    SUBAGENT_DEFAULT_MODEL,
    RECENT_MODELS,
    AUXILIARY_MODEL,
    DEFAULT_THINKING_LEVEL,
    DEFAULT_SERVICE_TIER,
    RLM_MAX_DEPTH,
    PROVIDER_MAX_IN_FLIGHT,
    PROVIDER_MAX_QUEUED,
    SUBAGENT_MAX_CONCURRENCY,
    SUBAGENT_STALL_MS,
    TOOL_BLOCKING_BUDGET_MS,
    MAX_TOOL_ROUNDS,
    IDLE_EVICTION_MINUTES,
    SESSION_ARCHIVE_MAX_AGE_DAYS,
    SESSION_ARCHIVE_MAX_SESSIONS,
    TRANSPORT,
    STEERING_MODE,
    FOLLOW_UP_MODE,
    THEME,
    COMPACTION_ENABLED,
    COMPACTION_RESERVE_TOKENS,
    COMPACTION_KEEP_RECENT_TOKENS,
    COMPACTION_AGENT_CALLABLE,
    COMPACTION_PROVIDER_TOKEN_COUNT,
    MEMORY_MODEL,
    MEMORY_THINKING,
    MEMORY_SETTLE_TIMEOUT_MS,
    AUTO_REFINE_ENABLED,
    AUTO_REFINE_TURN_INTERVAL,
    AUTO_REFINE_COMPACT,
    AUTO_REFINE_COOLDOWN_MS,
    FACTORY_ENABLED,
    BRANCH_SUMMARY_RESERVE_TOKENS,
    BRANCH_SUMMARY_SKIP_PROMPT,
    RETRY_ENABLED,
    RETRY_MAX_RETRIES,
    RETRY_BASE_DELAY_MS,
    RETRY_FAILOVER_ENABLED,
    RETRY_FAILOVER_MAX_RETRIES,
    RETRY_FAILOVER_BASE_DELAY_MS,
    RETRY_FAILOVER_MAX_DELAY_MS,
    RETRY_PROVIDER_TIMEOUT_MS,
    RETRY_PROVIDER_MAX_RETRY_DELAY_MS,
    RETRY_PROVIDER_STREAM_IDLE_TIMEOUT_MS,
    RETRY_PROVIDER_STREAM_REPEAT_LIMIT,
    RETRY_WAIT_ENABLED,
    RETRY_WAIT_BASE_DELAY_MS,
    RETRY_WAIT_MAX_DELAY_MS,
    RETRY_WAIT_MAX_ATTEMPTS,
    RETRY_WAIT_MAX_WAIT_MS,
    RETRY_WAIT_PAUSE_UNTIL_RESET,
    RETRY_WAIT_MAX_PAUSE_MS,
    RETRY_WAIT_MAX_PARKS,
    PROVIDER_BACKUP_MODEL,
    IMAGE_MODEL,
    AUTONOMOUS_MAX_CONTINUATIONS,
    AUTONOMOUS_MAX_TURNS,
    AUTONOMOUS_MAX_TOKENS,
    AUTONOMOUS_TIMEOUT_MS,
    DIRECTORS_STACK_CAP,
    DIRECTORS_MAX_STEPS,
    SHELL_PATH,
    QUIET_STARTUP,
    SHELL_COMMAND_PREFIX,
    NPM_COMMAND,
    MCP_SERVERS,
    MCP_CATALOG_SOURCES,
    PACKAGES,
    SKILLS,
    PROMPTS,
    THEMES,
    ENABLE_SKILL_COMMANDS,
    ENABLE_BUILTIN_SKILLS,
    TERMINAL_SHOW_IMAGES,
    TERMINAL_CLEAR_ON_SHRINK,
    TERMINAL_SHOW_TERMINAL_PROGRESS,
    TERMINAL_FULLSCREEN,
    TERMINAL_STREAM_PACE_MIN_CHARS,
    TERMINAL_STREAM_PACE_LAG,
    IMAGES_AUTO_RESIZE,
    IMAGES_BLOCK_IMAGES,
    ENABLED_MODELS,
    ALLOWED_MODELS,
    TREE_FILTER_MODE,
    CHAT_DETAIL,
    THINKING_BUDGET_MINIMAL,
    THINKING_BUDGET_LOW,
    THINKING_BUDGET_MEDIUM,
    THINKING_BUDGET_HIGH,
    EDITOR_PADDING_X,
    AUTOCOMPLETE_MAX_VISIBLE,
    SHOW_HARDWARE_CURSOR,
    MARKDOWN_CODE_BLOCK_INDENT,
    MARKDOWN_MERMAID,
    WARNINGS_ANTHROPIC_EXTRA_USAGE,
    SESSION_DIR,
    REQUEST_TIMING,
    TRUSTED_PROJECTS,
    GATEWAY_SIGNAL_ACCOUNT,
    GATEWAY_SIGNAL_ALLOW,
    GATEWAY_SIGNAL_CLI_PATH,
    GATEWAY_SIGNAL_CWD,
    KERNEL_TRANSPORT,
    SHELL_AUTO_EFFECTS,
    SSH_HOSTS,
    MODEL_ROLE_TINY,
    MODEL_ROLE_JUDGE,
    MODEL_ROLE_TRANSLATE,
    MODEL_ROLE_SPEECH,
    MODEL_ROLE_DICTATION,
    FALLBACK_CHAIN_TINY,
    FALLBACK_CHAIN_JUDGE,
    FALLBACK_CHAIN_TRANSLATE,
    FALLBACK_CHAIN_SPEECH,
    FALLBACK_CHAIN_DICTATION,
    PROVIDERS_TINY_MODEL_DEVICE,
    PROVIDERS_TINY_MODEL_DTYPE,
    PROVIDERS_TINY_RUNTIME_LIBRARY,
    TITLES_GENERATE,
    TTS_LOCAL_VOICE,
    STT_ENABLED,
];
