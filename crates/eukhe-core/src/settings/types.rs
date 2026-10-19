//! Settings types (settings-manager.ts). All fields optional; JSON values of
//! the wrong type load as `None` (the TS access-time typechecks), never a
//! load error.

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum MermaidRenderingMode {
    Off,
    Final,
    Streaming,
}

/// Thinking levels in wire form ("off" | "minimal" | "low" | "medium" |
/// "high" | "xhigh" | "max").
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ThinkingLevelSetting {
    Off,
    Minimal,
    Low,
    Medium,
    High,
    Xhigh,
    Max,
}

impl ThinkingLevelSetting {
    /// The same level in the shared model vocabulary: the settings default
    /// feeds session thinking-level resolution, so callers need the
    /// eukhe-types value without re-matching this enum.
    #[must_use]
    pub fn model_level(self) -> eukhe_types::ai::ModelThinkingLevel {
        match self {
            ThinkingLevelSetting::Off => eukhe_types::ai::ModelThinkingLevel::Off,
            ThinkingLevelSetting::Minimal => eukhe_types::ai::ModelThinkingLevel::Minimal,
            ThinkingLevelSetting::Low => eukhe_types::ai::ModelThinkingLevel::Low,
            ThinkingLevelSetting::Medium => eukhe_types::ai::ModelThinkingLevel::Medium,
            ThinkingLevelSetting::High => eukhe_types::ai::ModelThinkingLevel::High,
            ThinkingLevelSetting::Xhigh => eukhe_types::ai::ModelThinkingLevel::Xhigh,
            ThinkingLevelSetting::Max => eukhe_types::ai::ModelThinkingLevel::Max,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum QueueModeSetting {
    All,
    #[serde(alias = "oneAtATime")]
    OneAtATime,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TransportSetting {
    Auto,
    Sse,
    WebSocket,
    #[serde(rename = "websocket-cached")]
    WebSocketCached,
}

/// `number | "unlimited"` autonomous limit.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum AutonomousLimitSetting {
    Number(f64),
    Unlimited(String),
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CompactionSettings {
    pub enabled: Option<bool>,
    pub reserve_tokens: Option<u64>,
    pub keep_recent_tokens: Option<u64>,
    pub agent_callable: Option<bool>,
    pub provider_token_count: Option<bool>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BranchSummarySettings {
    pub reserve_tokens: Option<u64>,
    pub skip_prompt: Option<bool>,
}

/// The chat memory's compactor (`memory`): the cheap model that builds the
/// summary tree, its reasoning effort, and how long a turn waits for it.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MemorySettings {
    /// `provider/model-id`; unset falls back to `auxiliaryModel`, then to
    /// the default model.
    pub model: Option<String>,
    /// Reasoning effort of compactor calls; unset means medium.
    pub thinking: Option<ThinkingLevelSetting>,
    /// How long a turn waits for the view's lines to be summarized before
    /// it goes on with the view as it is; unset or `0` means 20 s.
    pub settle_timeout_ms: Option<u64>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AutoRefineSettings {
    pub enabled: Option<bool>,
    pub turn_interval: Option<u64>,
    pub compact: Option<bool>,
    pub cooldown_ms: Option<u64>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProviderWaitSettings {
    pub enabled: Option<bool>,
    pub base_delay_ms: Option<u64>,
    pub max_delay_ms: Option<u64>,
    pub max_attempts: Option<u64>,
    pub max_wait_ms: Option<u64>,
    /// Park sessions for provider-reported resets beyond the bounded
    /// wait (TS #2375 `pauseUntilReset`; default true).
    pub pause_until_reset: Option<bool>,
    /// Maximum single park duration (TS `maxPauseMs`; default 24h,
    /// clamped to 7d).
    pub max_pause_ms: Option<u64>,
    /// Maximum parks per quota episode (TS `maxParks`; default 8).
    pub max_parks: Option<u64>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProviderRetrySettings {
    pub timeout_ms: Option<u64>,
    pub max_retry_delay_ms: Option<u64>,
    /// Longest silence of a model stream before the request fails as
    /// stalled and retries (default 300000; `0` disables).
    pub stream_idle_timeout_ms: Option<u64>,
    /// Equal non-blank output lines in a row (text or thinking) that cut a
    /// model stream as repeating, which then retries (default 64; `0`
    /// takes the default).
    pub stream_repeat_limit: Option<u32>,
    pub wait_for_usage: Option<ProviderWaitSettings>,
}

/// Provider-failover settings (`retry.failover`): when another configured
/// provider serves the same model, a provider that exhausts its quick
/// retries hands the turn to the next one instead of failing it.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RetryFailoverSettings {
    pub enabled: Option<bool>,
    /// Retries per provider before switching (default 5).
    pub max_retries: Option<u64>,
    /// First backoff delay, doubling each retry (default 1000ms).
    pub base_delay_ms: Option<u64>,
    /// Backoff ceiling per retry (default 30000ms).
    pub max_delay_ms: Option<u64>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RetrySettings {
    pub enabled: Option<bool>,
    pub max_retries: Option<u64>,
    pub base_delay_ms: Option<u64>,
    pub failover: Option<RetryFailoverSettings>,
    pub provider: Option<ProviderRetrySettings>,
    pub fallback_chains: Option<FallbackChainsSettings>,
}

/// `retry.fallbackChains.<role>`: the ordered model selectors a role falls
/// back to after its primary (`modelRoles.<role>`). Unset: the role's
/// built-in priority; `[]`: the primary only (S9, `eukhe_tiny::chain`).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FallbackChainsSettings {
    pub tiny: Option<Vec<String>>,
    pub judge: Option<Vec<String>>,
    pub translate: Option<Vec<String>>,
    pub speech: Option<Vec<String>>,
    pub dictation: Option<Vec<String>>,
}

/// `modelRoles.<role>`: the primary model selector of each role
/// (`local/<catalog id>` or `provider/model`; S9).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelRolesSettings {
    /// Session titles.
    pub tiny: Option<String>,
    /// Typed judgments (classification).
    pub judge: Option<String>,
    pub translate: Option<String>,
    /// Text to speech (local only).
    pub speech: Option<String>,
    /// Speech to text (local only).
    pub dictation: Option<String>,
}

/// `providers`: how the local tiny-model worker runs (S9).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProvidersSettings {
    /// `tinyModelDevice`: the execution device (default `cpu`).
    #[serde(rename = "tinyModelDevice")]
    pub device: Option<String>,
    /// `tinyModelDtype`: the weight precision override; empty: the
    /// catalog's file set.
    #[serde(rename = "tinyModelDtype")]
    pub dtype: Option<String>,
    /// `tinyRuntimeLibrary`: the ONNX Runtime shared library the worker
    /// loads; empty: `ORT_DYLIB_PATH`, else the loader's search path.
    /// Loads code, so Global and withheld from untrusted projects.
    #[serde(rename = "tinyRuntimeLibrary")]
    pub runtime_library: Option<String>,
}

/// `titles`: generated session titles.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TitleSettings {
    /// Generate a title from a top-level session's first message (default
    /// true).
    pub generate: Option<bool>,
}

/// `tts`: text to speech.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TtsSettings {
    /// The local voice id (default `af_heart`).
    pub local_voice: Option<String>,
}

/// `stt`: speech to text (dictation into the editor draft).
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SttSettings {
    /// Turn on the dictation keys (default false).
    pub enabled: Option<bool>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TerminalSettings {
    pub show_images: Option<bool>,
    pub clear_on_shrink: Option<bool>,
    pub show_terminal_progress: Option<bool>,
    /// Show the generation speed (prefill, decode) on the status line
    /// (default true).
    pub show_speed: Option<bool>,
    /// Run the interactive surfaces in the alternate screen (default
    /// inline).
    pub fullscreen: Option<bool>,
    /// How fast streamed text appears on screen.
    pub stream_pace: Option<StreamPaceSettings>,
}

/// `terminal.streamPace`: each frame reveals
/// max(`minChars`, backlog / (1 + `lag`)) characters of streamed text.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct StreamPaceSettings {
    pub min_chars: Option<u64>,
    pub lag: Option<u64>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ImageSettings {
    pub auto_resize: Option<bool>,
    pub block_images: Option<bool>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ThinkingBudgetsSettings {
    pub minimal: Option<u64>,
    pub low: Option<u64>,
    pub medium: Option<u64>,
    pub high: Option<u64>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AutonomousSettings {
    pub max_continuations: Option<AutonomousLimitSetting>,
    pub max_turns: Option<AutonomousLimitSetting>,
    pub max_tokens: Option<AutonomousLimitSetting>,
    pub timeout_ms: Option<AutonomousLimitSetting>,
}

/// The Director stack (docs/control.md S5).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DirectorSettings {
    /// The reminders and forced calls the stack may hold (default 8; `0`
    /// or unset takes the default). The goal and the autonomous run keep
    /// 2 more places.
    pub stack_cap: Option<u32>,
    /// The continuations one run may make, whatever its Directors say
    /// (default 200; `0` or unset takes the default).
    pub max_steps: Option<u64>,
    /// The goal continuations in a row that may do no new work (no tool
    /// call with a result the session did not have before) before the
    /// goal pauses with the reason (default 3; `0` or unset takes the
    /// default).
    pub stall_steps: Option<u64>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct MarkdownSettings {
    pub code_block_indent: Option<String>,
    pub mermaid: Option<MermaidRenderingMode>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct WarningSettings {
    pub anthropic_extra_usage: Option<bool>,
}

/// `factory` (the agent factory's opt-in gate): `factory.enabled` is
/// unset/false by default, and the `/factory on` client command persists
/// it. Both the daemon's `factory_activity` lane advertisement and the
/// kernel's factory gate read the same shared settings key.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FactorySettings {
    pub enabled: Option<bool>,
}

/// `shell`: the shell tool's execution gate. An untrusted project may not
/// set it (see `settings::trust`).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ShellSettings {
    /// The effects (`read`, `write`, `exec`, `net`) a shell command may
    /// have without asking; unset is `read` only.
    pub auto_effects: Option<Vec<String>>,
}

/// `ssh`: the `ssh://` reads of the `read` tool. Global-only: a read
/// reaches a remote host, new outbound traffic, so no project scope may
/// set it (see `settings::trust`).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SshSettings {
    /// The hosts (as the URL names them: `box`, `user@box`) an `ssh://`
    /// read may reach. Absent or empty: none.
    pub hosts: Option<Vec<String>>,
}

/// `gateway`: the chat gateways `eukhe gateway` runs. Global-only: a
/// gateway routes a remote party into code execution on this machine, so
/// no project scope may set it (see `settings::trust`).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct GatewaySettings {
    pub signal: Option<SignalGatewaySettings>,
}

/// `gateway.signal`: the Signal gateway (a `signal-cli` child).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SignalGatewaySettings {
    /// The `signal-cli` account (`+<country><number>`). Required.
    pub account: Option<String>,
    /// Senders (numbers or ACIs) besides Note to Self that may drive the
    /// session. Absent means none.
    pub allow: Option<Vec<String>>,
    /// The `signal-cli` executable. Absent means `signal-cli` on `PATH`.
    pub cli_path: Option<String>,
    /// The working directory of new sessions. Absent means `$HOME`.
    pub cwd: Option<String>,
}

/// User-declared MCP server (settings `mcpServers` entry).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "kebab-case")]
pub enum McpServerConfig {
    Http {
        url: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        headers: Option<serde_json::Map<String, serde_json::Value>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        bearer_token_env_var: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        oauth: Option<bool>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        enabled: Option<bool>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        enabled_tools: Option<Vec<String>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        disabled_tools: Option<Vec<String>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        startup_timeout_ms: Option<u64>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        call_timeout_ms: Option<u64>,
    },
    Stdio {
        command: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        args: Option<Vec<String>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cwd: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        env: Option<serde_json::Map<String, serde_json::Value>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        enabled: Option<bool>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        enabled_tools: Option<Vec<String>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        disabled_tools: Option<Vec<String>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        startup_timeout_ms: Option<u64>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        call_timeout_ms: Option<u64>,
    },
}

/// The settings document: every known field optional; unknown keys preserved.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", default)]
pub struct Settings {
    pub onboarding_shown: Option<bool>,
    pub onboarding_completed: Option<bool>,
    pub default_provider: Option<String>,
    pub default_model: Option<String>,
    pub subagent_default_model: Option<String>,
    pub recent_models: Option<Vec<String>>,
    pub auxiliary_model: Option<String>,
    pub default_thinking_level: Option<ThinkingLevelSetting>,
    pub default_service_tier: Option<String>,
    pub rlm_max_depth: Option<u64>,
    /// Per-provider cap on concurrent model requests across every eukhe
    /// process of this agent dir (`{providerId: n}`); an absent provider
    /// (or `0`) is unlimited. The chat-memory compactor's requests count
    /// too, but come last: they wait while a session's request to the
    /// provider runs or waits, and the next one preempts them. Read from
    /// the global settings only.
    pub provider_max_in_flight: Option<std::collections::BTreeMap<String, u32>>,
    /// How many sessions' requests may wait for a limited provider before
    /// the next one fails at once (default 64; the compactor's waiting
    /// requests do not count). Read from the global settings only.
    pub provider_max_queued: Option<u32>,
    /// How many subagents may run at once in one daemon (default 32, `0`
    /// unlimited); a spawn batch that would exceed it fails whole.
    pub subagent_max_concurrency: Option<u32>,
    /// How long a subagent may show no progress, in ms (default 600 000;
    /// `0` or unset takes the default). A child with no progress for this
    /// long is stopped and reported to its parent as stalled.
    pub subagent_stall_ms: Option<u64>,
    /// The longest a tool call may block its turn, in ms (default
    /// 30 000). A call that runs longer settles `detached` with a job
    /// reference and keeps running; its completion wakes the session
    /// (ADR 0010). Waits a cell makes on the host (`rlm.collect`,
    /// `jobs.wait`) are clamped to it.
    pub tool_blocking_budget_ms: Option<u64>,
    /// Tool rounds one turn may make before it ends as failed (default
    /// 250; `0` or unset takes the default).
    pub max_tool_rounds: Option<u32>,
    /// `number | "off" | "none"`; raw JSON because the TS getter validates at
    /// access time.
    pub idle_eviction_minutes: Option<serde_json::Value>,
    /// Session archiving age rule: sessions untouched for this many days are
    /// moved to the daemon's archive directory. `number | "off" | "none"`; raw
    /// JSON validated at access time (same grammar as `idleEvictionMinutes`).
    pub session_archive_max_age_days: Option<serde_json::Value>,
    /// Session archiving count rule: keep at most this many unarchived
    /// sessions (newest by mtime win); `0 | "off" | "none"` disables. Raw JSON
    /// validated at access time.
    pub session_archive_max_sessions: Option<serde_json::Value>,
    pub transport: Option<TransportSetting>,
    pub steering_mode: Option<QueueModeSetting>,
    pub follow_up_mode: Option<QueueModeSetting>,
    pub theme: Option<String>,
    pub compaction: Option<CompactionSettings>,
    pub memory: Option<MemorySettings>,
    pub auto_refine: Option<AutoRefineSettings>,
    pub factory: Option<FactorySettings>,
    pub branch_summary: Option<BranchSummarySettings>,
    pub retry: Option<RetrySettings>,
    pub provider_backup_model: Option<String>,
    /// Model ("provider/model-id" or a bare model id) that serves turns
    /// attaching images when the session model does not accept image
    /// input. Default: none - image turns on a text-only model fail with
    /// a configuration hint instead of silently dropping the images.
    pub image_model: Option<String>,
    pub autonomous: Option<AutonomousSettings>,
    pub directors: Option<DirectorSettings>,
    pub shell_path: Option<String>,
    pub quiet_startup: Option<bool>,
    pub shell_command_prefix: Option<String>,
    pub npm_command: Option<Vec<String>>,
    pub mcp_servers: Option<serde_json::Map<String, serde_json::Value>>,
    /// Extra local MCP service-catalog files (TS `mcpCatalogSources`;
    /// ~-relative allowed), merged after the compiled built-ins, first
    /// source wins per id, and no bundled id can be shadowed.
    pub mcp_catalog_sources: Option<Vec<String>>,
    pub packages: Option<Vec<serde_json::Value>>,
    pub skills: Option<Vec<String>>,
    pub prompts: Option<Vec<String>>,
    pub themes: Option<Vec<String>>,
    pub enable_skill_commands: Option<bool>,
    pub enable_builtin_skills: Option<bool>,
    pub terminal: Option<TerminalSettings>,
    pub images: Option<ImageSettings>,
    pub enabled_models: Option<Vec<String>>,
    /// Rust-only daemon-level model allowlist: model patterns (the
    /// `--models` CLI scope grammar) the daemon may resolve to. Enforced at
    /// the daemon's model-resolution seams (`set_model`, RLM child-model
    /// resolution, the worker startup chain); a model outside the allowlist
    /// fails loudly instead of resolving, with no fallback. `None` is
    /// unrestricted (the TS behavior).
    pub allowed_models: Option<Vec<String>>,
    pub tree_filter_mode: Option<String>,
    /// `chatDetail` (TS #2709): the conversation-detail level Ctrl+O
    /// cycles and persists ("overview"/"details"/"all"); `None` reads
    /// as the `overview` startup level (the collapse mode).
    pub chat_detail: Option<String>,
    pub thinking_budgets: Option<ThinkingBudgetsSettings>,
    pub editor_padding_x: Option<u64>,
    pub autocomplete_max_visible: Option<u64>,
    pub show_hardware_cursor: Option<bool>,
    pub markdown: Option<MarkdownSettings>,
    pub warnings: Option<WarningSettings>,
    pub session_dir: Option<String>,
    /// Log per-request provider timing phases to the diagnostic log (TS
    /// `requestTiming`; unset means OFF, exactly the TS default).
    pub request_timing: Option<bool>,
    /// Global-only: absolute directories whose projects (the directory and
    /// everything under it) may set code-execution-capable settings and
    /// load project Python skills. A project-scope value is never read
    /// (see `settings::trust`).
    pub trusted_projects: Option<Vec<String>>,
    /// Global-only: the chat gateways (`eukhe gateway`). A project-scope
    /// value is never read (see `settings::trust`).
    pub gateway: Option<GatewaySettings>,
    /// `kernelTransport`: where the session's kernel runs (S3). Absent: a
    /// local child process. Parsed by
    /// `kernel::transport::KernelTransportSettings`.
    pub kernel_transport: Option<serde_json::Value>,
    /// `shell`: the shell tool's execution gate.
    pub shell: Option<ShellSettings>,
    /// Global-only: the hosts `ssh://` reads may reach. A project-scope
    /// value is never read (see `settings::trust`).
    pub ssh: Option<SshSettings>,
    /// `modelRoles`: the primary model of each S9 role.
    pub model_roles: Option<ModelRolesSettings>,
    /// `providers`: the local tiny-model worker's settings.
    pub providers: Option<ProvidersSettings>,
    /// `titles`: generated session titles.
    pub titles: Option<TitleSettings>,
    /// `tts`: text to speech.
    pub tts: Option<TtsSettings>,
    /// `stt`: speech to text.
    pub stt: Option<SttSettings>,
    /// Unknown keys survive load/save round-trips (forward compatibility).
    #[serde(flatten, skip_serializing_if = "serde_json::Map::is_empty")]
    pub extra: serde_json::Map<String, serde_json::Value>,
}
