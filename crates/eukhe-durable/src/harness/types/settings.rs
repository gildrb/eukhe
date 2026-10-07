//! Harness-wide run policy and Harness options (TS `HarnessSettings`,
//! `Settings`, the policies, `ConversationStreamOptions`, `HarnessOptions`).

use std::fmt;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::Context;
use eukhe_pi_ai::models::Models;
use eukhe_pi_ai::types::DeferredRequest;
use eukhe_types::pi_ai::{CacheRetention, IndexMap, JsonObject as PiJsonObject, Transport};
use futures::future::BoxFuture;
use serde::{Deserialize, Serialize};

use super::agent::EnvTarget;
use super::extension::Extension;
use super::registry::RegistryReader;
use crate::env::ExecutionEnv;
use crate::session::{SessionError, SessionResult, Tx};
use crate::types::ConversationRecord;

/// Whether the tools of one round run at once or one after another in call
/// order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum ToolExecutionMode {
    /// `"parallel"`.
    Parallel,
    /// `"sequential"`.
    Sequential,
}

/// How many queued items of one mode a boundary places: the first, or all of
/// them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum QueueMode {
    /// `"all"`.
    #[serde(rename = "all")]
    All,
    /// `"one-at-a-time"`.
    #[serde(rename = "one-at-a-time")]
    OneAtATime,
}

/// Curated pi-ai request options; absent fields use pi-ai defaults. Persisted
/// in generation and compaction checkpoints.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ConversationStreamOptions {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub transport: Option<Transport>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "eukhe_types::pi_ai::js_number::option::serialize"
    )]
    pub timeout_ms: Option<f64>,
    /// Provider/SDK retries inside one request attempt.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_retries: Option<u32>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "eukhe_types::pi_ai::js_number::option::serialize"
    )]
    pub max_retry_delay_ms: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub headers: Option<IndexMap<String, String>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub metadata: Option<PiJsonObject>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cache_retention: Option<CacheRetention>,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        with = "deferred_serde"
    )]
    pub deferred: Option<DeferredRequest>,
}

/// Serde of TS `deferred?: boolean | { window?: "15m" | "1h" | "24h" }`.
mod deferred_serde {
    use eukhe_pi_ai::types::{DeferredRequest, DeferredWindow};
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    #[derive(Serialize, Deserialize)]
    #[serde(untagged)]
    enum Wire {
        Flag(bool),
        Window {
            #[serde(default, skip_serializing_if = "Option::is_none")]
            window: Option<DeferredWindow>,
        },
    }

    #[expect(
        clippy::ref_option,
        clippy::trivially_copy_pass_by_ref,
        reason = "serde `with` passes the field by reference"
    )]
    pub(super) fn serialize<S: Serializer>(
        value: &Option<DeferredRequest>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        value
            .map(|value| match value {
                DeferredRequest::Flag(flag) => Wire::Flag(flag),
                DeferredRequest::Window(window) => Wire::Window { window },
            })
            .serialize(serializer)
    }

    pub(super) fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Option<DeferredRequest>, D::Error> {
        Ok(
            Option::<Wire>::deserialize(deserializer)?.map(|wire| match wire {
                Wire::Flag(flag) => DeferredRequest::Flag(flag),
                Wire::Window { window } => DeferredRequest::Window(window),
            }),
        )
    }
}

/// Durable generation attempt retries; the JSON shape of pi-ai
/// `RetryPolicy`.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ConversationRetryPolicy {
    pub enabled: bool,
    pub max_retries: u32,
    #[serde(serialize_with = "eukhe_types::pi_ai::js_number::serialize")]
    pub base_delay_ms: f64,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "eukhe_types::pi_ai::js_number::option::serialize"
    )]
    pub max_agent_delay_ms: Option<f64>,
}

/// TS `Partial<ConversationRetryPolicy>`.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct PartialRetryPolicy {
    pub enabled: Option<bool>,
    pub max_retries: Option<u32>,
    pub base_delay_ms: Option<f64>,
    pub max_agent_delay_ms: Option<f64>,
}

/// Automatic compaction thresholds (spec §8.7); manual compaction ignores
/// `enabled`.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CompactionPolicy {
    /// Threshold and overflow compaction.
    pub enabled: bool,
    /// Room kept free for the answer: generation blocks to compact above
    /// `contextWindow - reserveTokens`.
    #[serde(serialize_with = "eukhe_types::pi_ai::js_number::serialize")]
    pub reserve_tokens: f64,
    /// Approximate size of the recent context a summary keeps verbatim.
    #[serde(serialize_with = "eukhe_types::pi_ai::js_number::serialize")]
    pub keep_recent_tokens: f64,
    /// Background compaction starts `backgroundTokens` below the blocking
    /// threshold; `0` disables it.
    #[serde(serialize_with = "eukhe_types::pi_ai::js_number::serialize")]
    pub background_tokens: f64,
}

/// TS `Partial<CompactionPolicy>`.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct PartialCompactionPolicy {
    pub enabled: Option<bool>,
    pub reserve_tokens: Option<f64>,
    pub keep_recent_tokens: Option<f64>,
    pub background_tokens: Option<f64>,
}

/// How often running progress is committed. Each progress commit is a
/// storage write; a host whose storage is remote can commit less often, so
/// live answers and tool output appear in larger steps.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ProgressPolicy {
    /// Minimum pause between commits of the answer being generated.
    #[serde(serialize_with = "eukhe_types::pi_ai::js_number::serialize")]
    pub partial_interval_ms: f64,
    /// Minimum pause between commits of running tool output; large commits
    /// also pause in proportion to their size.
    #[serde(serialize_with = "eukhe_types::pi_ai::js_number::serialize")]
    pub output_interval_ms: f64,
}

/// TS `Partial<ProgressPolicy>`.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct PartialProgressPolicy {
    pub partial_interval_ms: Option<f64>,
    pub output_interval_ms: Option<f64>,
}

/// Harness-wide run policy. Read at every resolution and never copied.
///
/// TS distinguishes an absent field from one set to `undefined` when it
/// spreads a partial policy over its default; Rust has one `None`, which
/// keeps the default.
#[derive(Debug, Clone, Default)]
pub struct HarnessSettings {
    /// Default extension selection; absent: every installed extension, in
    /// install order.
    pub extensions: Option<Vec<Arc<Extension>>>,
    pub stream: Option<ConversationStreamOptions>,
    pub retry: Option<PartialRetryPolicy>,
    pub compaction: Option<PartialCompactionPolicy>,
    pub progress: Option<PartialProgressPolicy>,
    pub tool_execution: Option<ToolExecutionMode>,
    pub steering_mode: Option<QueueMode>,
    pub follow_up_mode: Option<QueueMode>,
}

/// Resolved settings: every field over its built-in default, object fields
/// merged.
#[derive(Debug, Clone)]
pub struct Settings {
    /// Absent: every installed extension, in install order.
    pub extensions: Option<Vec<Arc<Extension>>>,
    pub stream: ConversationStreamOptions,
    pub retry: ConversationRetryPolicy,
    pub compaction: CompactionPolicy,
    pub progress: ProgressPolicy,
    pub tool_execution: ToolExecutionMode,
    pub steering_mode: QueueMode,
    pub follow_up_mode: QueueMode,
}

/// Live source of [`HarnessSettings`] (TS `HarnessOptions.settings`, an
/// object whose fields may be getters).
///
/// The Harness calls [`current`](Self::current) at every resolution and
/// never keeps the result past it. Implementations answer synchronously and
/// cheaply: some readers run on the Session line.
pub trait HarnessSettingsSource: Send + Sync {
    /// The settings in effect now.
    fn current(&self) -> Arc<HarnessSettings>;
}

/// Settings a host replaces or edits while the Harness runs.
#[derive(Debug, Default)]
pub struct LiveSettings {
    current: Mutex<Arc<HarnessSettings>>,
}

impl LiveSettings {
    /// A source starting with `settings`.
    #[must_use]
    pub fn new(settings: HarnessSettings) -> Self {
        Self {
            current: Mutex::new(Arc::new(settings)),
        }
    }

    /// Replace the settings; later resolutions see them.
    pub fn set(&self, settings: HarnessSettings) {
        *self.current.lock().unwrap_or_else(PoisonError::into_inner) = Arc::new(settings);
    }

    /// Edit a copy of the current settings and publish it.
    pub fn update(&self, edit: impl FnOnce(&mut HarnessSettings)) {
        let mut current = self.current.lock().unwrap_or_else(PoisonError::into_inner);
        edit(Arc::make_mut(&mut current));
    }
}

impl HarnessSettingsSource for LiveSettings {
    fn current(&self) -> Arc<HarnessSettings> {
        Arc::clone(&self.current.lock().unwrap_or_else(PoisonError::into_inner))
    }
}

/// Builds a conversation's environment at each use. Never called on the
/// Session line; may be async.
pub type EnvFactory = Arc<
    dyn Fn(EnvTarget, &Context) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ExecutionEnv>>>>
        + Send
        + Sync,
>;

/// Runs in every commit that creates or forks a conversation, raw
/// `tx.create_conversation()` included, after the built-in `pi.*` documents
/// and before the conveniences apply `agent` and run `init`. A fork already
/// has its copies. Table reads fail with `ReadAfterWrite`, as in `init`; an
/// error fails the creating commit.
pub type ConversationCreated =
    Arc<dyn Fn(Tx, ConversationRecord) -> BoxFuture<'static, SessionResult<()>> + Send + Sync>;

/// The Harness clock in milliseconds (TS `() => number`).
pub type Clock = Arc<dyn Fn() -> f64 + Send + Sync>;

/// Receives extension failures that do not fail the calling operation. Must
/// not panic.
pub type ReportFn = Arc<dyn Fn(SessionError) + Send + Sync>;

/// Options of `Harness::open`.
#[derive(Clone)]
pub struct HarnessOptions {
    /// pi-ai model access used by generation.
    pub models: Models,
    pub registry: Arc<dyn RegistryReader>,
    pub settings: Option<Arc<dyn HarnessSettingsSource>>,
    /// Builds a conversation's environment at each use.
    pub env: Option<EnvFactory>,
    pub conversation_created: Option<ConversationCreated>,
    pub now: Option<Clock>,
    pub on_report: Option<ReportFn>,
}

impl HarnessOptions {
    /// Options with only the required fields.
    #[must_use]
    pub fn new(models: Models, registry: Arc<dyn RegistryReader>) -> Self {
        Self {
            models,
            registry,
            settings: None,
            env: None,
            conversation_created: None,
            now: None,
            on_report: None,
        }
    }
}

impl fmt::Debug for HarnessOptions {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("HarnessOptions")
            .field(
                "settings",
                &self.settings.as_ref().map(|settings| settings.current()),
            )
            .field("env", &self.env.is_some())
            .field("conversation_created", &self.conversation_created.is_some())
            .field("now", &self.now.is_some())
            .field("on_report", &self.on_report.is_some())
            .finish_non_exhaustive()
    }
}

impl ConversationStreamOptions {
    /// The pi-ai request options these select (TS `{ ...streamOptions }`
    /// spread into `SimpleStreamOptions`); callers add `signal`,
    /// `sessionId`, and `reasoning`.
    pub(crate) fn simple_stream_options(&self) -> eukhe_pi_ai::types::SimpleStreamOptions {
        let mut options = eukhe_pi_ai::types::SimpleStreamOptions::default();
        let stream = &mut options.stream;
        stream.transport = self.transport;
        stream.request.timeout_ms = self.timeout_ms;
        stream.request.max_retries = self.max_retries;
        stream.request.max_retry_delay_ms = self.max_retry_delay_ms;
        stream.request.headers = self.headers.as_ref().map(|headers| {
            headers
                .iter()
                .map(|(name, value)| (name.clone(), Some(value.clone())))
                .collect()
        });
        stream.metadata.clone_from(&self.metadata);
        stream.cache_retention = self.cache_retention;
        options.deferred = self.deferred;
        options
    }
}
