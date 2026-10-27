//! The settings getters: each reads its cvar through the manager's
//! [`Cvars`](super::cvar::Cvars) (the one resolver: default < config <
//! the agent's family), with its declaration from [`table`]. A default
//! lives in the declaration only; a getter parses what its setting's
//! grammar needs (`idleEvictionMinutes`' `number | "off"`) and takes the
//! declared default for anything else.

use serde::de::DeserializeOwned;
use serde_json::Value;

use super::cvar::{table, Decl, Init};
use super::manager::{IdleEviction, SessionArchivePolicy, SettingsManager};
use super::types::{
    AutoRefineSettings, QueueModeSetting, SignalGatewaySettings, ThinkingLevelSetting,
    TransportSetting,
};

/// The declared default of a Nat cvar or of a Json cvar whose default is
/// a number.
///
/// # Panics
///
/// When `decl`'s default is not a number (a getter reading the wrong
/// declaration).
pub(super) fn default_nat(decl: &Decl) -> u64 {
    match decl.init {
        Init::Nat(value) => value,
        Init::Bool(_) | Init::Text(_) | Init::EmptyList | Init::List(_) | Init::Null => {
            panic!("cvar `{}` has no number default", decl.id)
        }
    }
}

/// The declared default of a Text or Choice cvar.
///
/// # Panics
///
/// When `decl`'s default is not a text.
pub(super) fn default_text(decl: &Decl) -> &'static str {
    match decl.init {
        Init::Text(value) => value,
        Init::Bool(_) | Init::Nat(_) | Init::EmptyList | Init::List(_) | Init::Null => {
            panic!("cvar `{}` has no text default", decl.id)
        }
    }
}

/// A [`CvarType::NatOrOff`](super::cvar::CvarType::NatOrOff) value.
enum OffOrNumber {
    Off,
    Number(u64),
    /// Unset (the reader takes the default); the load names a malformed
    /// value and drops it, so it reads as unset too.
    Malformed,
}

fn off_or_number(value: &Value) -> OffOrNumber {
    match value {
        Value::String(text) if text == "off" || text == "none" => OffOrNumber::Off,
        Value::Number(number) => OffOrNumber::Number(number.as_u64().unwrap_or(0)),
        Value::Null | Value::Bool(_) | Value::String(_) | Value::Array(_) | Value::Object(_) => {
            OffOrNumber::Malformed
        }
    }
}

fn saturating_u32(value: u64) -> u32 {
    u32::try_from(value).unwrap_or(u32::MAX)
}

fn saturating_usize(value: u64) -> usize {
    usize::try_from(value).unwrap_or(usize::MAX)
}

impl SettingsManager {
    /// The value of a Choice cvar as the settings enum it names.
    ///
    /// # Panics
    ///
    /// When an option of the declaration is not a value of `T` (the
    /// table's options and the enum's serde names disagree).
    pub(super) fn choice<T: DeserializeOwned>(&self, decl: &Decl) -> T {
        let text = self.cvars().text(decl);
        match serde_json::from_value(Value::String(text.clone())) {
            Ok(value) => value,
            Err(error) => panic!("cvar `{}` option `{text}` does not parse: {error}", decl.id),
        }
    }

    /// The text of a Text cvar as written; `None` when empty (unset).
    pub(super) fn raw_text(&self, decl: &Decl) -> Option<String> {
        let text = self.cvars().text(decl);
        (!text.is_empty()).then_some(text)
    }

    /// The items of a List cvar; `None` when empty (unset).
    fn nonempty_list(&self, decl: &Decl) -> Option<Vec<String>> {
        let items = self.cvars().list(decl);
        (!items.is_empty()).then_some(items)
    }

    /// A Json cvar holding a whole number; `None` for null or any other
    /// value.
    fn json_u64(&self, decl: &Decl) -> Option<u64> {
        self.cvars().value(decl).as_u64()
    }

    /// A Nat cvar where `0` takes the declared default.
    fn nonzero_nat(&self, decl: &Decl) -> u64 {
        match self.cvars().nat(decl) {
            0 => default_nat(decl),
            value => value,
        }
    }

    /// `markdown.codeBlockIndent` (TS `getCodeBlockIndent`): the string the
    /// chat markdown renderer indents fenced code blocks by.
    #[must_use]
    pub fn get_code_block_indent(&self) -> String {
        self.cvars().text(&table::MARKDOWN_CODE_BLOCK_INDENT)
    }

    /// `terminal.showImages` (TS `getShowImages`): whether image blocks in
    /// tool results render their type/dimension metadata rows.
    #[must_use]
    pub fn get_show_images(&self) -> bool {
        self.cvars().bool(&table::TERMINAL_SHOW_IMAGES)
    }

    /// `terminal.fullscreen`: whether the interactive surfaces run in the
    /// alternate screen (the default) instead of inline.
    #[must_use]
    pub fn get_fullscreen(&self) -> bool {
        self.cvars().bool(&table::TERMINAL_FULLSCREEN)
    }

    /// `terminal.pinnedAgents`: `off`, `collapsed`, or `full`.
    #[must_use]
    pub fn get_pinned_agents(&self) -> String {
        self.cvars().text(&table::TERMINAL_PINNED_AGENTS)
    }

    /// `terminal.stuckAfterSecs`: seconds a running agent may go without
    /// a word before the pinned agents block shows it as quiet; `0` is off.
    #[must_use]
    pub fn get_stuck_after_secs(&self) -> u64 {
        self.cvars().nat(&table::TERMINAL_STUCK_AFTER_SECS)
    }

    /// `terminal.streamPace.minChars`: the fewest streamed characters a
    /// frame reveals. A 0 reads as 1, since a zero minimum would stall a
    /// small backlog.
    #[must_use]
    pub fn get_stream_pace_min_chars(&self) -> usize {
        saturating_usize(self.cvars().nat(&table::TERMINAL_STREAM_PACE_MIN_CHARS)).max(1)
    }

    /// `terminal.streamPace.lag`: how far the screen trails the stream; a
    /// frame reveals backlog / (1 + lag) characters.
    #[must_use]
    pub fn get_stream_pace_lag(&self) -> usize {
        saturating_usize(self.cvars().nat(&table::TERMINAL_STREAM_PACE_LAG))
    }

    /// `treeFilterMode` (TS `getTreeFilterMode`): the `/tree` selector's
    /// initial filter; a value outside the modes reads as the default.
    #[must_use]
    pub fn get_tree_filter_mode(&self) -> String {
        self.cvars().text(&table::TREE_FILTER_MODE)
    }

    /// `chatDetail` (TS #2709 `getChatDetail`): the conversation-detail
    /// level the chat starts at; a value outside the levels reads as the
    /// default `overview` (the collapse mode).
    #[must_use]
    pub fn get_chat_detail(&self) -> String {
        self.cvars().text(&table::CHAT_DETAIL)
    }

    /// `branchSummary.skipPrompt` (TS `getBranchSummarySkipPrompt`).
    #[must_use]
    pub fn get_branch_summary_skip_prompt(&self) -> bool {
        self.cvars().bool(&table::BRANCH_SUMMARY_SKIP_PROMPT)
    }

    /// `branchSummary.reserveTokens`: the branch summarizer's reserve.
    #[must_use]
    pub fn get_branch_summary_reserve_tokens(&self) -> u64 {
        self.cvars().nat(&table::BRANCH_SUMMARY_RESERVE_TOKENS)
    }

    /// TS `getOnboardingShown`: first run is defined by the settings alone
    /// (the load migration carries the legacy `onboardingCompleted`).
    #[must_use]
    pub fn get_onboarding_shown(&self) -> bool {
        self.cvars().bool(&table::ONBOARDING_SHOWN)
    }

    /// TS `getCompactionEnabled`: the auto-compaction toggle.
    #[must_use]
    pub fn get_compaction_enabled(&self) -> bool {
        self.cvars().bool(&table::COMPACTION_ENABLED)
    }

    /// `compaction.reserveTokens`.
    #[must_use]
    pub fn get_compaction_reserve_tokens(&self) -> u64 {
        self.cvars().nat(&table::COMPACTION_RESERVE_TOKENS)
    }

    /// `compaction.keepRecentTokens`.
    #[must_use]
    pub fn get_compaction_keep_recent_tokens(&self) -> u64 {
        self.cvars().nat(&table::COMPACTION_KEEP_RECENT_TOKENS)
    }

    /// `compaction.agentCallable`: whether the agent may call compaction.
    #[must_use]
    pub fn get_compaction_agent_callable(&self) -> bool {
        self.cvars().bool(&table::COMPACTION_AGENT_CALLABLE)
    }

    /// `compaction.providerTokenCount`: whether the compaction threshold
    /// check asks the provider's own token counter for each request.
    #[must_use]
    pub fn get_compaction_provider_token_count(&self) -> bool {
        self.cvars().bool(&table::COMPACTION_PROVIDER_TOKEN_COUNT)
    }

    #[must_use]
    pub fn get_default_provider(&self) -> Option<String> {
        self.raw_text(&table::DEFAULT_PROVIDER)
    }

    #[must_use]
    pub fn get_default_model(&self) -> Option<String> {
        self.raw_text(&table::DEFAULT_MODEL)
    }

    /// Model for `rlm.spawn` without a pinned model; unset inherits parent.
    #[must_use]
    pub fn get_subagent_default_model(&self) -> Option<String> {
        self.cvars().optional_text(&table::SUBAGENT_DEFAULT_MODEL)
    }

    #[must_use]
    pub fn get_auxiliary_model(&self) -> Option<String> {
        self.raw_text(&table::AUXILIARY_MODEL)
    }

    /// `memory.model`: the chat memory compactor's `provider/model-id`
    /// (whitespace-only reads as unset).
    #[must_use]
    pub fn get_memory_model(&self) -> Option<String> {
        self.cvars().optional_text(&table::MEMORY_MODEL)
    }

    /// `memory.thinking`: the compactor's reasoning effort.
    #[must_use]
    pub fn get_memory_thinking(&self) -> ThinkingLevelSetting {
        self.choice(&table::MEMORY_THINKING)
    }

    /// `thinkingBudgets.*`: the user's token budget of each thinking
    /// level; `None` when no level is set (the providers' defaults apply).
    #[must_use]
    pub fn get_thinking_budgets(&self) -> Option<eukhe_types::pi_ai::ThinkingBudgets> {
        let budgets = eukhe_types::pi_ai::ThinkingBudgets {
            minimal: self.json_u64(&table::THINKING_BUDGET_MINIMAL),
            low: self.json_u64(&table::THINKING_BUDGET_LOW),
            medium: self.json_u64(&table::THINKING_BUDGET_MEDIUM),
            high: self.json_u64(&table::THINKING_BUDGET_HIGH),
        };
        (budgets != eukhe_types::pi_ai::ThinkingBudgets::default()).then_some(budgets)
    }

    /// `memory.settleTimeoutMs`: how long a turn waits for the view's
    /// lines to be summarized; then it goes on with the view as it is,
    /// each line not summarized yet as its input cut to 512 bytes. `0`
    /// takes the default, as `subagentStallMs` and `maxToolRounds` read
    /// `0`.
    #[must_use]
    pub fn get_memory_settle_timeout(&self) -> std::time::Duration {
        std::time::Duration::from_millis(self.nonzero_nat(&table::MEMORY_SETTLE_TIMEOUT_MS))
    }

    /// TS `getImageModel`: the "provider/model-id" (or bare id) reference
    /// that serves turns attaching images on session models without image
    /// input; whitespace behaves as unset.
    #[must_use]
    pub fn get_image_model(&self) -> Option<String> {
        self.cvars().optional_text(&table::IMAGE_MODEL)
    }

    /// The daemon-level model allowlist (`allowedModels`, Global): model
    /// patterns the daemon may resolve to, enforced at every daemon model
    /// resolution — a model outside it fails loudly, never a fallback.
    /// `None` is unrestricted; a list that trims to empty behaves as unset.
    #[must_use]
    pub fn get_allowed_models(&self) -> Option<Vec<String>> {
        let patterns: Vec<String> = self
            .cvars()
            .list(&table::ALLOWED_MODELS)
            .iter()
            .map(|pattern| pattern.trim().to_string())
            .filter(|pattern| !pattern.is_empty())
            .collect();
        (!patterns.is_empty()).then_some(patterns)
    }

    /// Service tier a fresh session records as its preference (TS
    /// `getDefaultServiceTier`).
    #[must_use]
    pub fn get_default_service_tier(&self) -> eukhe_types::ai::ServiceTier {
        self.choice(&table::DEFAULT_SERVICE_TIER)
    }

    #[must_use]
    pub fn get_recent_models(&self) -> Vec<String> {
        self.cvars().list(&table::RECENT_MODELS)
    }

    /// The steering queue's delivery mode (TS `steeringMode`): `all`
    /// batches every queued steering message into ONE co-delivered turn
    /// at the next turn boundary; `one-at-a-time` delivers one per turn.
    #[must_use]
    pub fn get_steering_mode(&self) -> QueueModeSetting {
        self.choice(&table::STEERING_MODE)
    }

    #[must_use]
    pub fn get_follow_up_mode(&self) -> QueueModeSetting {
        self.choice(&table::FOLLOW_UP_MODE)
    }

    #[must_use]
    pub fn get_theme(&self) -> Option<String> {
        self.raw_text(&table::THEME)
    }

    #[must_use]
    pub fn get_default_thinking_level(&self) -> Option<ThinkingLevelSetting> {
        self.raw_text(&table::DEFAULT_THINKING_LEVEL)
            .map(|_| self.choice(&table::DEFAULT_THINKING_LEVEL))
    }

    #[must_use]
    pub fn get_rlm_max_depth(&self) -> Option<u64> {
        self.json_u64(&table::RLM_MAX_DEPTH)
    }

    /// `gateway.signal`: the Signal gateway settings (Global: a gateway
    /// routes a remote party into code execution on this machine). An
    /// empty field is absent.
    #[must_use]
    pub fn get_signal_gateway(&self) -> SignalGatewaySettings {
        SignalGatewaySettings {
            // A set account, even empty, stays: the gateway reports an
            // empty one instead of falling back to the linked account.
            account: self
                .cvars()
                .layered(&table::GATEWAY_SIGNAL_ACCOUNT)
                .and_then(|value| value.as_str().map(str::to_string)),
            allow: self.nonempty_list(&table::GATEWAY_SIGNAL_ALLOW),
            cli_path: self.raw_text(&table::GATEWAY_SIGNAL_CLI_PATH),
            cwd: self.raw_text(&table::GATEWAY_SIGNAL_CWD),
            model: self.raw_text(&table::GATEWAY_SIGNAL_MODEL),
        }
    }

    /// `subagentMaxConcurrency`: how many subagents may run at once (`0`
    /// is unlimited).
    #[must_use]
    pub fn get_subagent_max_concurrency(&self) -> u32 {
        saturating_u32(self.cvars().nat(&table::SUBAGENT_MAX_CONCURRENCY))
    }

    /// `subagentStallMs`: how long a subagent may show no progress before
    /// its parent stops it and reports it stalled (`0` takes the default).
    #[must_use]
    pub fn get_subagent_stall(&self) -> std::time::Duration {
        std::time::Duration::from_millis(self.nonzero_nat(&table::SUBAGENT_STALL_MS))
    }

    /// `toolBlockingBudgetMs`: the runtime's one blocking budget for a
    /// tool call (`0` takes the default).
    #[must_use]
    pub fn get_tool_blocking_budget(&self) -> std::time::Duration {
        std::time::Duration::from_millis(self.nonzero_nat(&table::TOOL_BLOCKING_BUDGET_MS))
    }

    /// `maxToolRounds`: the tool rounds one run may make (the Harness
    /// reads `0` as its default).
    #[must_use]
    pub fn get_max_tool_rounds(&self) -> u32 {
        saturating_u32(self.cvars().nat(&table::MAX_TOOL_ROUNDS))
    }

    /// The provider admission limits (`providerMaxInFlight`,
    /// `providerMaxQueued`, Global: shared by every session of the agent
    /// dir). A malformed in-flight limit is never "no limit"
    /// ([`AdmissionLimits::from_setting`](crate::admission::AdmissionLimits::from_setting)):
    /// when the load dropped the value from `settings.json` (it named it),
    /// the value as written still caps.
    #[must_use]
    pub fn get_admission_limits(&self) -> crate::admission::AdmissionLimits {
        let decl = &table::PROVIDER_MAX_IN_FLIGHT;
        let in_flight = self
            .cvars()
            .layered(decl)
            .or_else(|| self.global_raw().and_then(|raw| raw.get(decl.id)).cloned())
            .unwrap_or(Value::Null);
        crate::admission::AdmissionLimits::from_setting(
            &in_flight,
            Some(saturating_u32(
                self.cvars().nat(&table::PROVIDER_MAX_QUEUED),
            )),
        )
    }

    /// `idleEvictionMinutes`: `number | "off" | "none"` -> finite minutes
    /// or Off; `0` or a malformed value reads as the default.
    #[must_use]
    pub fn get_idle_eviction(&self) -> IdleEviction {
        let decl = &table::IDLE_EVICTION_MINUTES;
        match off_or_number(&self.cvars().value(decl)) {
            OffOrNumber::Off => IdleEviction::Off,
            OffOrNumber::Number(minutes) if minutes > 0 => IdleEviction::Minutes(minutes),
            OffOrNumber::Number(_) | OffOrNumber::Malformed => {
                IdleEviction::Minutes(default_nat(decl))
            }
        }
    }

    /// Resolved session-archiving policy: which sessions the daemon's
    /// archive sweep moves out of the sessions directory. Both rules are
    /// independent — a session is archived when EITHER fires. `None` on a
    /// field disables that rule.
    #[must_use]
    pub fn get_session_archive_policy(&self) -> SessionArchivePolicy {
        let age = &table::SESSION_ARCHIVE_MAX_AGE_DAYS;
        let max_age_days = match off_or_number(&self.cvars().value(age)) {
            OffOrNumber::Off => None,
            OffOrNumber::Number(days) if days > 0 => Some(days),
            OffOrNumber::Number(_) | OffOrNumber::Malformed => Some(default_nat(age)),
        };
        let count = &table::SESSION_ARCHIVE_MAX_SESSIONS;
        let max_sessions = match off_or_number(&self.cvars().value(count)) {
            OffOrNumber::Off | OffOrNumber::Number(0) => None,
            OffOrNumber::Number(sessions) => Some(sessions),
            OffOrNumber::Malformed => Some(default_nat(count)),
        }
        .map(|sessions| usize::try_from(sessions).unwrap_or(usize::MAX));
        SessionArchivePolicy {
            max_age_days,
            max_sessions,
        }
    }

    #[must_use]
    pub fn get_transport(&self) -> TransportSetting {
        self.choice(&table::TRANSPORT)
    }

    /// The transport a layer sets; `None` leaves the choice to the provider
    /// (a pinned request carries no transport then, which a provider reads
    /// differently from an explicit `auto`).
    #[must_use]
    pub fn get_stream_transport(&self) -> Option<TransportSetting> {
        self.cvars()
            .layered(&table::TRANSPORT)
            .map(|_| self.get_transport())
    }

    /// `retry.enabled`: the auto-retry toggle.
    #[must_use]
    pub fn get_retry_enabled(&self) -> bool {
        self.cvars().bool(&table::RETRY_ENABLED)
    }

    /// `retry.maxRetries`.
    #[must_use]
    pub fn get_retry_max_retries(&self) -> u64 {
        self.cvars().nat(&table::RETRY_MAX_RETRIES)
    }

    /// `retry.baseDelayMs`.
    #[must_use]
    pub fn get_retry_base_delay_ms(&self) -> u64 {
        self.cvars().nat(&table::RETRY_BASE_DELAY_MS)
    }

    /// `retry.provider.maxRetryDelayMs`: the cap of a server-requested
    /// delay and the quota park's bounded wait.
    #[must_use]
    pub fn get_max_retry_delay_ms(&self) -> u64 {
        self.cvars().nat(&table::RETRY_PROVIDER_MAX_RETRY_DELAY_MS)
    }

    /// `retry.provider.timeoutMs`; `None` is each provider's own timeout.
    #[must_use]
    pub fn get_provider_timeout_ms(&self) -> Option<u64> {
        self.json_u64(&table::RETRY_PROVIDER_TIMEOUT_MS)
    }

    /// `retry.provider.streamIdleTimeoutMs` (`0` disables); `None` is the
    /// provider default.
    #[must_use]
    pub fn get_stream_idle_timeout_ms(&self) -> Option<u64> {
        self.json_u64(&table::RETRY_PROVIDER_STREAM_IDLE_TIMEOUT_MS)
    }

    /// `retry.provider.streamRepeatLimit` (`0` takes the provider
    /// default); `None` is the provider default.
    #[must_use]
    pub fn get_stream_repeat_limit(&self) -> Option<u32> {
        self.json_u64(&table::RETRY_PROVIDER_STREAM_REPEAT_LIMIT)
            .map(saturating_u32)
    }

    /// `retry.failover.enabled`.
    #[must_use]
    pub fn get_failover_enabled(&self) -> bool {
        self.cvars().bool(&table::RETRY_FAILOVER_ENABLED)
    }

    /// `retry.failover.maxRetries`: provider switches one request may make
    /// before the final failure.
    #[must_use]
    pub fn get_failover_max_retries(&self) -> u64 {
        self.cvars().nat(&table::RETRY_FAILOVER_MAX_RETRIES)
    }

    /// `retry.failover.baseDelayMs`: the wait before a request's first
    /// return to a provider it left; it doubles each return.
    #[must_use]
    pub fn get_failover_base_delay_ms(&self) -> u64 {
        self.cvars().nat(&table::RETRY_FAILOVER_BASE_DELAY_MS)
    }

    /// `retry.failover.maxDelayMs`: the longest wait before a return to a
    /// provider; a provider whose server asks for longer is not returned to.
    #[must_use]
    pub fn get_failover_max_delay_ms(&self) -> u64 {
        self.cvars().nat(&table::RETRY_FAILOVER_MAX_DELAY_MS)
    }

    /// `retry.provider.waitForUsage.pauseUntilReset`.
    #[must_use]
    pub fn get_park_pause_until_reset(&self) -> bool {
        self.cvars().bool(&table::RETRY_WAIT_PAUSE_UNTIL_RESET)
    }

    /// `retry.provider.waitForUsage.maxPauseMs`.
    #[must_use]
    pub fn get_park_max_pause_ms(&self) -> u64 {
        self.cvars().nat(&table::RETRY_WAIT_MAX_PAUSE_MS)
    }

    /// `retry.provider.waitForUsage.maxParks`.
    #[must_use]
    pub fn get_park_max_parks(&self) -> u64 {
        self.cvars().nat(&table::RETRY_WAIT_MAX_PARKS)
    }

    /// The `autoRefine` block, every field resolved.
    #[must_use]
    pub fn get_auto_refine(&self) -> AutoRefineSettings {
        AutoRefineSettings {
            enabled: Some(self.cvars().bool(&table::AUTO_REFINE_ENABLED)),
            turn_interval: Some(self.cvars().nat(&table::AUTO_REFINE_TURN_INTERVAL)),
            compact: Some(self.cvars().bool(&table::AUTO_REFINE_COMPACT)),
            cooldown_ms: Some(self.cvars().nat(&table::AUTO_REFINE_COOLDOWN_MS)),
        }
    }

    /// `requestTiming`: log per-request provider timing phases.
    #[must_use]
    pub fn get_request_timing(&self) -> bool {
        self.cvars().bool(&table::REQUEST_TIMING)
    }

    /// `npmCommand` (argv form); `None` is plain `npm`.
    #[must_use]
    pub fn get_npm_command(&self) -> Option<Vec<String>> {
        self.nonempty_list(&table::NPM_COMMAND)
    }

    /// `mcpServers`: the user-declared MCP servers by name (empty when
    /// unset or not an object).
    #[must_use]
    pub fn get_mcp_servers(&self) -> serde_json::Map<String, Value> {
        match self.cvars().value(&table::MCP_SERVERS) {
            Value::Object(servers) => servers,
            Value::Null
            | Value::Bool(_)
            | Value::Number(_)
            | Value::String(_)
            | Value::Array(_) => serde_json::Map::new(),
        }
    }

    /// `mcpCatalogSources`: extra local MCP service-catalog files.
    #[must_use]
    pub fn get_mcp_catalog_sources(&self) -> Vec<String> {
        self.cvars().list(&table::MCP_CATALOG_SOURCES)
    }

    /// `shellPath`: the shell user bash runs; `None` is the default shell.
    #[must_use]
    pub fn get_shell_path(&self) -> Option<String> {
        self.raw_text(&table::SHELL_PATH)
    }

    /// `shellCommandPrefix`: text run before each user bash command.
    #[must_use]
    pub fn get_shell_command_prefix(&self) -> Option<String> {
        self.raw_text(&table::SHELL_COMMAND_PREFIX)
    }

    /// `kernelTransport`: where the session's kernel runs (S3); `None` is a
    /// local child process.
    #[must_use]
    pub fn get_kernel_transport(&self) -> Option<Value> {
        Some(self.cvars().value(&table::KERNEL_TRANSPORT)).filter(|value| !value.is_null())
    }

    /// `shell.autoEffects`: the effects (`read`, `write`, `exec`, `net`,
    /// `outside`, `protected`) a shell command may have without asking; by
    /// default all six.
    #[must_use]
    pub fn get_shell_auto_effects(&self) -> Vec<String> {
        self.cvars().list(&table::SHELL_AUTO_EFFECTS)
    }

    /// `privacy.anonymizeRemote`: scrub outbound request text of a remote
    /// provider (default true).
    #[must_use]
    pub fn get_privacy_anonymize_remote(&self) -> bool {
        self.cvars().bool(&table::PRIVACY_ANONYMIZE_REMOTE)
    }

    /// `privacy.terms`: phrases a remote provider must not see (empty by
    /// default).
    #[must_use]
    pub fn get_privacy_terms(&self) -> Vec<String> {
        self.cvars().list(&table::PRIVACY_TERMS)
    }

    /// `ssh.hosts`: the hosts an `ssh://` read may reach (Global: new
    /// outbound traffic). Empty: every `ssh://` read is rejected.
    #[must_use]
    pub fn get_ssh_hosts(&self) -> Vec<String> {
        self.cvars().list(&table::SSH_HOSTS)
    }
}

/// Where sessions live and which input decided it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SessionDir {
    pub path: std::path::PathBuf,
    pub source: SessionDirSource,
}

/// The input that decided [`SessionDir::path`], highest first.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SessionDirSource {
    /// The `--session-dir` flag.
    Flag,
    /// The `EUKHE_SESSION_DIR` environment variable (or the legacy
    /// `EUKHE_CODING_AGENT_SESSION_DIR`).
    Environment,
    /// The `sessionDir` setting.
    Setting,
    /// `<agent dir>/sessions`.
    Default,
}

/// The environment variable that sets the sessions directory.
pub const SESSION_DIR_ENV: &str = "EUKHE_SESSION_DIR";

/// The legacy name of [`SESSION_DIR_ENV`].
pub const LEGACY_SESSION_DIR_ENV: &str = "EUKHE_CODING_AGENT_SESSION_DIR";

/// The one precedence of the sessions directory, for every reader (the
/// CLI, the dashboard, the gateway, the daemon): the `--session-dir` flag (`flag`), then the
/// `EUKHE_SESSION_DIR` environment variable (then the legacy
/// `EUKHE_CODING_AGENT_SESSION_DIR`), then the `sessionDir` setting of
/// `settings`, then `<agent_dir>/sessions`. A leading `~` is the home
/// directory.
///
/// # Errors
///
/// A value starts with `~` and the home directory is not known.
pub fn resolve_session_dir(
    flag: Option<&std::path::Path>,
    settings: &SettingsManager,
    agent_dir: &std::path::Path,
) -> anyhow::Result<SessionDir> {
    let environment = [SESSION_DIR_ENV, LEGACY_SESSION_DIR_ENV]
        .into_iter()
        .find_map(|name| std::env::var(name).ok().filter(|value| !value.is_empty()));
    let setting = settings.raw_text(&table::SESSION_DIR);
    let (text, source) = match (flag, environment, setting) {
        (Some(flag), _, _) => (flag.to_string_lossy().into_owned(), SessionDirSource::Flag),
        (None, Some(value), _) => (value, SessionDirSource::Environment),
        (None, None, Some(value)) => (value, SessionDirSource::Setting),
        (None, None, None) => {
            return Ok(SessionDir {
                path: agent_dir.join("sessions"),
                source: SessionDirSource::Default,
            })
        }
    };
    let home = || {
        eukhe_types::platform::home_dir()
            .ok_or_else(|| anyhow::anyhow!("`{text}` names the home directory, which is not set"))
    };
    let path = if text == "~" {
        home()?
    } else if let Some(rest) = text.strip_prefix("~/") {
        home()?.join(rest)
    } else {
        std::path::PathBuf::from(&text)
    };
    Ok(SessionDir { path, source })
}
