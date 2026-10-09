//! Durable session telemetry: the agent-event state machine behind the
//! session events `agent started`, `agent run completed` (one per user
//! turn, every per-call fact folded into it as aggregates), and `agent
//! session ended` (with the per-session counters). Port of the session
//! engine's telemetry (`session_engine::telemetry.rs`, the TS
//! `installAgentTelemetry` subscriber plus the #2117 v2 enrichment) onto
//! the durable harness's [`AgentEvent`] batches: there is no agent
//! subscription — the host owns the event consumption task and feeds
//! every observed event (or batch) into the returned
//! [`SessionTelemetry`] handle, then finalizes the session with
//! [`SessionTelemetry::end`].
//!
//! Event mapping (old engine → durable harness):
//! - `AgentStart` → [`AgentEvent::RunStart`]: same boundary role (the
//!   turn boundary observes the recording switch, the previous run
//!   finalizes, a new active run opens). The old retry-resume arm — a
//!   run with `retry_pending` re-entering `AgentStart` — does not map:
//!   durable retries stay inside one run.
//! - `AgentEnd` → [`AgentEvent::RunEnd`]: marks the run ended and
//!   freezes its duration.
//! - `MessageStart` (user) → [`AgentEvent::MessageStart`] with a `pi_ai`
//!   user message: increments `prompt_count` and resolves the `prompt`
//!   trigger.
//! - `MessageUpdate` (stream event) → [`AgentEvent::MessageUpdate`]:
//!   non-empty `TextDelta` changes drive the visible TTFT and the
//!   run-to-first-text timing, non-empty `ThinkingDelta` changes the
//!   first-reasoning timing, and every update ticks the stream-gap
//!   tracking and the first-model-event timing. The other change kinds
//!   (`ToolcallDelta`, `TextStart`, `ThinkingStart`, `ToolcallStart`,
//!   `Block`, `Message`) carry no facts the old subscriber used.
//! - `MessageEnd` (assistant) → [`AgentEvent::MessageEnd`]: the entry's
//!   first model message, when it is an assistant message, resolves the
//!   `continuation` trigger, adds usage, records the last assistant,
//!   the model-call latency, the stop-reason error handling, the cost,
//!   and the successful-call count.
//! - tool start/end → [`AgentEvent::ToolExecutionStart`] /
//!   [`AgentEvent::ToolExecutionEnd`]. `is_error` is derived: the entry
//!   is absent (a faulted or orphaned tool task) or its tool-result
//!   message reports `is_error`.
//! - the old `note_auto_retry_event` seam →
//!   [`AgentEvent::AutoRetryStart`] / [`AgentEvent::AutoRetryEnd`] (the
//!   retried attempt continues the same run).
//! - the old `note_compaction` seam →
//!   [`AgentEvent::CompactionStart`] / [`AgentEvent::CompactionEnd`].
//! - [`AgentEvent::TaskFailed`] with the generation kind counts a model
//!   error into the active run; other kinds report through their own
//!   tool events.
//!
//! Documented deviations from the old engine:
//! - `retry_wait_ms` is the scheduled retry fire time (`at`, epoch
//!   milliseconds) minus the event-observation clock — the old seam
//!   received the centrally-computed delay directly.
//! - `failover_count` stays 0: durable events carry no backup-provider
//!   reason (another workstream owns failover).
//! - `compaction_duration_ms` is measured between the observed
//!   `CompactionStart` and `CompactionEnd` events — the old seam
//!   received the centrally-measured duration.
//! - `error_subtype` (and the `TaskFailed` error-category counting) may
//!   fall back to the run's last recorded error text (from
//!   `AutoRetryStart` / `TaskFailed`) when the final assistant message
//!   carries no `error_message`.
//! - an [`AgentEvent::EntryAppended`] of the child-usage attribution
//!   kind feeds the `rlm_child_*` counters directly (the durable
//!   replacement of the old engine's daemon-side producer feed).
//! - compactions with no active run count nothing, exactly like the old
//!   seam (`note_compaction` only counted into an open run).
//!
//! Privacy contract: this module emits counter/duration/category facts
//! only — never prompt text, model output, tool arguments or results.
//! Failed model calls classify through [`super::error_classify`]: only
//! fixed diagnostics and reviewed fixed strings ride events.
//!
//! Fire-and-forget contract: `track` hands events to the client's
//! worker; nothing here blocks, and no lock poisoning panics — a
//! poisoned telemetry state lock is recovered (the host owns the
//! consumption task and never lets telemetry fail the session).

use std::collections::HashMap;
use std::path::Path;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use eukhe_durable::harness::{AgentEvent, MessageChange};
use eukhe_durable::types::{EntryRecord, TaskId};
use eukhe_telemetry::{
    base_properties, feature_outcome_key, Properties, RunTrigger, TelemetryClient,
    TelemetryClientConfig, ToolCategory, ERROR_CATEGORIES,
};
use eukhe_types::pi_ai::{AssistantMessage, Message, StopReason, Usage};
use serde_json::Value;

use super::error_classify::classify_error_message;
use super::rlm_usage::{ChildUsageAttributionData, CHILD_USAGE_ATTRIBUTED_KIND};
use super::run_classify::{
    error_category, model_category, opt_value, provider_category, run_outcome,
};
use super::telemetry_status::{telemetry_endpoint, telemetry_switch};

/// The generation task kind: a `TaskFailed` of this kind is a model
/// error (`events.rs` `GENERATION_KIND`).
const GENERATION_KIND: &str = "pi.generation";

/// The execution mode the wiring layer resolved for this process, e.g.
/// "interactive" or "unknown" (TS `AgentExecutionMode` surface).
pub const EXECUTION_MODE_UNKNOWN: &str = "unknown";

#[cfg(test)]
mod tests;

/// A session's live opt-out switch: the recording seams ask the switch
/// at turn boundaries (run and turn starts) and cache the answer for
/// the events in between: a mid-turn opt-out is observed at the next
/// boundary, and the client's flush drops everything queued while the
/// switch is off.
#[derive(Clone)]
pub struct RecordingSwitch {
    /// Env-then-settings resolution, asked live at the turn boundaries:
    /// false means telemetry is off right now.
    pub enabled: Arc<dyn Fn() -> bool + Send + Sync>,
}

impl RecordingSwitch {
    /// A plain switch for the seams: recording gates live on `enabled`
    /// at the turn boundaries.
    #[must_use]
    pub fn test(enabled: Arc<dyn Fn() -> bool + Send + Sync>) -> Self {
        Self { enabled }
    }
}

/// Telemetry wiring supplied by the composition root. `None` telemetry
/// (opt-out) installs nothing.
pub struct TelemetryWiring {
    /// The shared client (base properties are stamped here, per event).
    pub client: TelemetryClient,
    /// Execution mode for base properties.
    pub execution_mode: Option<String>,
    /// Injectable clock (millis since epoch); defaults to system time.
    /// Tests pass a controlled clock to assert duration math.
    pub now: Option<Arc<dyn Fn() -> u64 + Send + Sync>>,
    /// The live opt-out switch the recording seams consult at the turn
    /// boundaries: while it answers false there, the run state machine
    /// severs and nothing records until the next boundary, and the
    /// client drops captures queued while the switch is off. `None` is
    /// always on (tests and one-shot paths).
    pub telemetry_enabled: Option<RecordingSwitch>,
}

/// Installed session telemetry: the in-memory state the observed durable
/// agent events feed. The host owns the event consumption task and
/// calls [`SessionTelemetry::handle_event`] (or
/// [`SessionTelemetry::observe_batch`]) per observed event; the handle
/// outlives the events and finalizes the session on `end()`.
pub struct SessionTelemetry {
    client: TelemetryClient,
    state: Arc<Mutex<TelemetryState>>,
    execution_mode: String,
    counters: Arc<SessionCounters>,
    /// `end()` runs exactly once (session close and later kill/shutdown
    /// paths may both reach it; only the first emits the ended event).
    ended: std::sync::atomic::AtomicBool,
}

/// Everything the observer accumulates. Guarded by one mutex; a
/// poisoned lock is recovered (never a panic — telemetry must not fail
/// the session).
pub struct TelemetryState {
    session_id: String,
    started_at: u64,
    totals: SessionTotals,
    active_run: Option<ActiveRun>,
    tool_starts: HashMap<String, u64>,
    /// Observed `CompactionStart` timestamps by compaction task: the
    /// end event measures its duration against its start observation.
    compaction_starts: HashMap<TaskId, u64>,
    /// The live opt-out switch from the wiring: asked at the turn
    /// boundaries, never per event.
    telemetry_enabled: Option<RecordingSwitch>,
    /// The cached switch answer from the last turn boundary. Recording
    /// on any other event consults only this flag, so a streaming delta
    /// never re-reads and re-parses the settings file.
    recording: bool,
    now: Arc<dyn Fn() -> u64 + Send + Sync>,
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Is recording on right now? `None` (tests, one-shot paths) is always
/// on; a set switch answers live. Called from under the state lock, so
/// the switch itself must never lock the telemetry state.
fn recording_on(state: &TelemetryState) -> bool {
    state
        .telemetry_enabled
        .as_ref()
        .is_none_or(|telemetry_switch| (telemetry_switch.enabled)())
}

/// While telemetry is off, the active run (if any) is severed: dropped
/// without emitting, together with its in-flight tables. The switch is
/// asked at the turn boundaries, so a run that spans an opt-out never
/// completes after the boundary that observes the off period — neither
/// its facts nor the off window's timing ride a later event.
fn sever_off_period_run(state: &mut TelemetryState) {
    state.active_run = None;
    state.tool_starts.clear();
    state.compaction_starts.clear();
}

/// One turn boundary (a run or turn start): ask the live switch, cache
/// the answer for the events until the next boundary, and cut the run
/// when the switch says off. Between boundaries nothing re-reads the
/// settings file — the client's flush drops everything queued while the
/// switch is off, which covers a mid-turn opt-out.
fn observe_turn_boundary(state: &mut TelemetryState) {
    state.recording = recording_on(state);
    if !state.recording {
        sever_off_period_run(state);
    }
}

#[derive(Default)]
struct SessionTotals {
    run_count: u64,
    successful_run_count: u64,
    failed_run_count: u64,
    aborted_run_count: u64,
    prompt_count: u64,
    tool_call_count: u64,
    compaction_count: u64,
    retry_count: u64,
    failover_count: u64,
    model_error_count: u64,
    usage: UsageTotals,
}

#[derive(Default)]
struct UsageTotals {
    input: u64,
    output: u64,
    cache_read: u64,
    cache_write: u64,
    total_tokens: u64,
    model_call_count: u64,
}

impl UsageTotals {
    fn add(&mut self, usage: &Usage) {
        self.input += usage.input;
        self.output += usage.output;
        self.cache_read += usage.cache_read;
        self.cache_write += usage.cache_write;
        self.total_tokens += usage.total_tokens;
        self.model_call_count += 1;
    }

    fn merge(&mut self, other: &UsageTotals) {
        self.input += other.input;
        self.output += other.output;
        self.cache_read += other.cache_read;
        self.cache_write += other.cache_write;
        self.total_tokens += other.total_tokens;
        self.model_call_count += other.model_call_count;
    }
}

// The run's independent lifecycle flags (ended, retry pending, trigger
// pending, usage complete); an enum would not change the flow.
#[allow(clippy::struct_excessive_bools)]
struct ActiveRun {
    started_at: u64,
    /// `RunEnd` fired but the run is not finalized yet: the post-run
    /// compaction drain still counts into it (TS keeps the run open
    /// until the turn action deactivates; the durable analog defers to
    /// the next `RunStart` or session end).
    ended: bool,
    /// Wall time of `RunEnd`: the run's duration freezes here (deferring
    /// the finalize must not stretch the duration across the idle gap).
    ended_at: Option<u64>,
    first_turn_started_at: Option<u64>,
    first_model_event_ms: Option<u64>,
    visible_ttft_ms: Option<u64>,
    current_turn_started_at: Option<u64>,
    model_latency_ms: u64,
    max_model_latency_ms: u64,
    turn_count: u64,
    tool_call_count: u64,
    tool_error_count: u64,
    compaction_count: u64,
    retry_count: u64,
    failover_count: u64,
    usage: UsageTotals,
    last_assistant: Option<AssistantMessage>,
    /// An auto-retry started after this run's failed attempt: the
    /// retried attempt continues this run (TS: one run per turn,
    /// retries counted in `retry_count`).
    retry_pending: bool,
    /// The run's last error text, from `AutoRetryStart` or a generation
    /// `TaskFailed` — the fallback for `error_subtype` when the final
    /// assistant message carries no `error_message`.
    last_error_text: Option<String>,
    // v2 (#2117) per-run tracking:
    /// The run's uuid.
    run_id: String,
    /// 1-based ordinal of this run in the session.
    run_index: u64,
    /// The trigger is still undecided: a prompt-run emits its user
    /// `MessageStart` right after `RunStart`; a continuation-run goes
    /// straight to model events.
    trigger_pending: bool,
    trigger: RunTrigger,
    first_reasoning_ms: Option<u64>,
    run_to_first_text_ms: Option<u64>,
    /// Sum of tool execution durations (the `tool` timing stage).
    tool_duration_ms: u64,
    /// Sum of auto-retry delays (the `retry_wait` timing stage).
    retry_wait_ms: u64,
    /// The largest gap between consecutive model stream events.
    max_stream_gap_ms: Option<u64>,
    last_stream_event_at: Option<u64>,
    /// Model calls whose response settled without an error stop reason.
    successful_model_call_count: u64,
    /// False once a model call ended in an error (#2117: pending or
    /// failed calls make usage incomplete).
    usage_complete: bool,
    /// Summed usage cost in USD (estimated; null when incomplete or
    /// pricing was unknown - the conservative direction).
    cost_usd: f64,
    /// Each model call's latency (the p50 on the run event).
    model_latencies: Vec<u64>,
    /// Failed model calls in the run (every retried attempt included).
    model_error_count: u64,
    /// Failed model calls by TS `error_category`.
    error_category_counts: std::collections::BTreeMap<&'static str, u64>,
    /// Summed compaction durations inside the run.
    compaction_duration_ms: u64,
    /// Per-tool aggregates, keyed by the fixed tool category (built-in
    /// tools by name, every MCP and custom tool folded into `mcp` /
    /// `custom`: no raw tool names leave the machine).
    tool_summary: HashMap<ToolCategory, ToolCategoryStats>,
}

/// One tool category's per-run aggregates.
#[derive(Debug, Default)]
struct ToolCategoryStats {
    calls: u64,
    failures: u64,
    duration_ms: u64,
    max_duration_ms: u64,
}

/// Per-session counters for the frequent per-occurrence facts that ride
/// `agent session ended` instead of their own events (skill invocations,
/// MCP connector use, kernel boots, RLM child usage, feature outcomes).
/// Shared with the engine seams that report them.
#[derive(Default)]
pub struct SessionCounters {
    inner: Mutex<CounterValues>,
    /// The live opt-out switch, installed by the host at the counters'
    /// creation, before the MCP and kernel seams that count into them
    /// capture their handles. While it answers false the counters stop
    /// recording, so a later enable never sends what happened while
    /// telemetry was off (the TUI counters' rule). `None` (the default,
    /// used by tests and one-shot paths) is always on.
    telemetry_enabled: std::sync::OnceLock<Arc<dyn Fn() -> bool + Send + Sync>>,
}

#[derive(Default)]
struct CounterValues {
    skill_use_count: u64,
    mcp_connector_use_count: u64,
    kernel_bootstrap_count: u64,
    kernel_bootstrap_cold_count: u64,
    kernel_bootstrap_failed_count: u64,
    kernel_bootstrap_max_ms: u64,
    rlm_child_usage_count: u64,
    rlm_child_input_tokens: u64,
    rlm_child_output_tokens: u64,
    rlm_child_cache_read_tokens: u64,
    rlm_child_cache_write_tokens: u64,
    rlm_child_cost: f64,
    /// `feature_<name>_<outcome>_count` over the fixed feature vocabulary.
    feature_outcomes: std::collections::BTreeMap<String, u64>,
}

impl SessionCounters {
    /// Install the live opt-out switch. The host calls this at the
    /// counters' creation, ahead of the MCP and kernel counting seams,
    /// so no event can count before the switch is in place. A second
    /// call is ignored (the first switch wins).
    pub fn set_telemetry_enabled(&self, telemetry_enabled: Arc<dyn Fn() -> bool + Send + Sync>) {
        let _ = self.telemetry_enabled.set(telemetry_enabled);
    }

    /// Count only while telemetry is on, so turning it on later never
    /// sends what happened while it was off.
    fn with(&self, update: impl FnOnce(&mut CounterValues)) {
        if self
            .telemetry_enabled
            .get()
            .is_some_and(|telemetry_enabled| !telemetry_enabled())
        {
            return;
        }
        update(&mut lock(&self.inner));
    }

    /// An MCP connector call (the server name never uploads).
    pub fn note_mcp_connector_use(&self) {
        self.with(|values| values.mcp_connector_use_count += 1);
    }

    /// One kernel boot: cold or revived, its outcome, its duration.
    pub fn note_kernel_bootstrap(&self, cold: bool, succeeded: bool, duration_ms: u64) {
        self.with(|values| {
            values.kernel_bootstrap_count += 1;
            values.kernel_bootstrap_cold_count += u64::from(cold);
            values.kernel_bootstrap_failed_count += u64::from(!succeeded);
            values.kernel_bootstrap_max_ms = values.kernel_bootstrap_max_ms.max(duration_ms);
        });
    }

    fn write_into(&self, properties: &mut Properties) {
        self.with(|values| {
            for (key, value) in [
                ("skill_use_count", values.skill_use_count),
                ("mcp_connector_use_count", values.mcp_connector_use_count),
                ("kernel_bootstrap_count", values.kernel_bootstrap_count),
                (
                    "kernel_bootstrap_cold_count",
                    values.kernel_bootstrap_cold_count,
                ),
                (
                    "kernel_bootstrap_failed_count",
                    values.kernel_bootstrap_failed_count,
                ),
                ("kernel_bootstrap_max_ms", values.kernel_bootstrap_max_ms),
                ("rlm_child_usage_count", values.rlm_child_usage_count),
                ("rlm_child_input_tokens", values.rlm_child_input_tokens),
                ("rlm_child_output_tokens", values.rlm_child_output_tokens),
                (
                    "rlm_child_cache_read_tokens",
                    values.rlm_child_cache_read_tokens,
                ),
                (
                    "rlm_child_cache_write_tokens",
                    values.rlm_child_cache_write_tokens,
                ),
            ] {
                properties.set(key, Value::from(value));
            }
            if values.rlm_child_usage_count > 0 {
                properties.set("rlm_child_cost", Value::from(values.rlm_child_cost));
            }
            for (key, count) in &values.feature_outcomes {
                properties.set(key, Value::from(*count));
            }
        });
    }
}

/// Skills present at session start (adoption counts on `agent started`).
pub struct SkillCounts {
    pub skill_count: usize,
    pub python_skill_count: usize,
}

/// Install the session telemetry and emit `agent started`. There is no
/// agent subscription anymore: the host owns the event consumption task
/// and feeds every observed durable agent event into the returned
/// handle (the state it builds lives there for session-end
/// finalization).
pub fn install(
    wiring: &TelemetryWiring,
    skill_counts: Option<SkillCounts>,
    counters: Arc<SessionCounters>,
) -> SessionTelemetry {
    let execution_mode = wiring
        .execution_mode
        .clone()
        .unwrap_or_else(|| EXECUTION_MODE_UNKNOWN.to_string());
    let now = wiring.now.clone().unwrap_or_else(|| Arc::new(now_millis));
    let client = wiring.client.clone();
    let state = Arc::new(Mutex::new(TelemetryState {
        session_id: uuid(),
        started_at: now(),
        totals: SessionTotals::default(),
        active_run: None,
        tool_starts: HashMap::new(),
        compaction_starts: HashMap::new(),
        telemetry_enabled: wiring.telemetry_enabled.clone(),
        recording: true,
        now,
    }));
    // The counters arrive already gated: the host installs the same
    // live switch on them at creation (the MCP and kernel seams count
    // long before this install runs), so nothing counts while telemetry
    // is off in any window.

    let telemetry = SessionTelemetry {
        client: client.clone(),
        state,
        execution_mode,
        counters,
        ended: std::sync::atomic::AtomicBool::new(false),
    };

    let mut properties = base_properties(&telemetry.execution_mode);
    {
        let state = lock(&telemetry.state);
        properties.set("session_id", Value::from(state.session_id.as_str()));
        if let Some(counts) = skill_counts {
            properties.set("skill_count", Value::from(counts.skill_count as u64));
            properties.set(
                "python_skill_count",
                Value::from(counts.python_skill_count as u64),
            );
        }
    }
    client.track("agent started", properties);
    telemetry
}

impl SessionTelemetry {
    /// One observed agent event → state machine step. The host's
    /// consumption task calls this per event (in commit order). Never
    /// panics: a poisoned state lock is recovered.
    pub fn handle_event(&self, event: &AgentEvent) {
        let mut state = lock(&self.state);
        // The switch is asked at the turn boundaries only: a run or
        // turn start refreshes the cached decision, every other event
        // consults the cache, and the client's flush drops everything
        // queued while the switch is off. While recording is off
        // nothing records, and the run severs: its facts never enter
        // the aggregates, so a later enable can neither complete it nor
        // merge the next run into it.
        if matches!(event, AgentEvent::RunStart { .. } | AgentEvent::TurnStart) {
            observe_turn_boundary(&mut state);
            if !state.recording {
                return;
            }
        } else if !state.recording {
            sever_off_period_run(&mut state);
            return;
        }
        let now = (state.now)();
        match event {
            AgentEvent::RunStart { .. } => {
                // Durable retries stay inside one run (AutoRetryStart
                // keeps it open), so every RunStart is a fresh window.
                // The previous run finalizes here (not at RunEnd): a
                // post-run compaction drained between RunEnd and this
                // start must land in that run, exactly like the TS
                // turn-action window. A missing RunEnd (misbehaving
                // emitter) still cannot lose run facts.
                finalize_run_locked(&self.client, &self.execution_mode, &mut state);
                let run_index = state.totals.run_count + 1;
                state.active_run = Some(ActiveRun {
                    started_at: now,
                    ended: false,
                    ended_at: None,
                    first_turn_started_at: None,
                    first_model_event_ms: None,
                    visible_ttft_ms: None,
                    current_turn_started_at: None,
                    model_latency_ms: 0,
                    max_model_latency_ms: 0,
                    turn_count: 0,
                    tool_call_count: 0,
                    tool_error_count: 0,
                    compaction_count: 0,
                    retry_count: 0,
                    failover_count: 0,
                    usage: UsageTotals::default(),
                    last_assistant: None,
                    retry_pending: false,
                    last_error_text: None,
                    run_id: uuid(),
                    run_index,
                    trigger_pending: true,
                    trigger: RunTrigger::Unknown,
                    first_reasoning_ms: None,
                    run_to_first_text_ms: None,
                    tool_duration_ms: 0,
                    retry_wait_ms: 0,
                    max_stream_gap_ms: None,
                    last_stream_event_at: None,
                    successful_model_call_count: 0,
                    usage_complete: true,
                    cost_usd: 0.0,
                    model_latencies: Vec::new(),
                    model_error_count: 0,
                    error_category_counts: std::collections::BTreeMap::new(),
                    compaction_duration_ms: 0,
                    tool_summary: HashMap::new(),
                });
            }
            AgentEvent::TurnStart => {
                if let Some(run) = state.active_run.as_mut() {
                    if run.first_turn_started_at.is_none() {
                        run.first_turn_started_at = Some(now);
                    }
                    run.current_turn_started_at = Some(now);
                    run.turn_count += 1;
                }
            }
            AgentEvent::MessageStart { message } => {
                if message.role() == "user" {
                    state.totals.prompt_count += 1;
                    // A prompt-run's user message lands right after
                    // `RunStart`: the run's trigger is a fresh prompt.
                    resolve_trigger(&mut state, RunTrigger::Prompt);
                }
            }
            AgentEvent::MessageUpdate { changes, .. } => {
                if state.active_run.is_some() {
                    // A continuation-run's first event is a model event
                    // (no user message ever lands inside it): the retry
                    // re-entry disambiguates the trigger.
                    resolve_trigger(&mut state, RunTrigger::Continuation);
                    let Some(run) = state.active_run.as_mut() else {
                        return;
                    };
                    if run.first_model_event_ms.is_none() {
                        if let Some(first_turn) = run.first_turn_started_at {
                            run.first_model_event_ms = Some(now.saturating_sub(first_turn));
                        }
                    }
                    // The old subscriber saw one stream event per
                    // MessageUpdate; a durable update may carry several
                    // changes, so the delta kinds scan the change list.
                    let is_text_delta = changes.iter().any(|change| {
                        matches!(change, MessageChange::TextDelta { delta, .. } if !delta.is_empty())
                    });
                    if is_text_delta {
                        if run.visible_ttft_ms.is_none() {
                            if let Some(first_turn) = run.first_turn_started_at {
                                run.visible_ttft_ms = Some(now.saturating_sub(first_turn));
                            }
                        }
                        if run.run_to_first_text_ms.is_none() {
                            run.run_to_first_text_ms = Some(now.saturating_sub(run.started_at));
                        }
                    }
                    let is_reasoning_delta = changes.iter().any(|change| {
                        matches!(change, MessageChange::ThinkingDelta { delta, .. } if !delta.is_empty())
                    });
                    if is_reasoning_delta && run.first_reasoning_ms.is_none() {
                        if let Some(first_turn) = run.first_turn_started_at {
                            run.first_reasoning_ms = Some(now.saturating_sub(first_turn));
                        }
                    }
                    // The stream gap: the largest quiet stretch between
                    // consecutive model events within the run.
                    if let Some(last) = run.last_stream_event_at {
                        let gap = now.saturating_sub(last);
                        run.max_stream_gap_ms =
                            Some(run.max_stream_gap_ms.map_or(gap, |max| max.max(gap)));
                    }
                    run.last_stream_event_at = Some(now);
                }
            }
            AgentEvent::MessageEnd { entry } => {
                if let Some(assistant) = assistant_of(entry) {
                    // A continuation-run without stream events (a
                    // non-streamed response) still disambiguates at its
                    // first assistant message end.
                    resolve_trigger(&mut state, RunTrigger::Continuation);
                    let is_error = assistant.stop_reason == StopReason::Error;
                    let category = error_category(Some(&assistant))
                        .as_str()
                        .and_then(|category| {
                            ERROR_CATEGORIES
                                .iter()
                                .find(|known| **known == category)
                                .copied()
                        });
                    let cost_total = assistant.usage.cost.total;
                    if let Some(run) = state.active_run.as_mut() {
                        run.usage.add(&assistant.usage);
                        run.last_assistant = Some(assistant);
                        if let Some(turn_started) = run.current_turn_started_at.take() {
                            let latency = now.saturating_sub(turn_started);
                            run.model_latency_ms += latency;
                            run.max_model_latency_ms = run.max_model_latency_ms.max(latency);
                            run.model_latencies.push(latency);
                        }
                        if is_error {
                            run.usage_complete = false;
                            run.model_error_count += 1;
                            if let Some(category) = category {
                                *run.error_category_counts.entry(category).or_default() += 1;
                            }
                        } else {
                            run.successful_model_call_count += 1;
                        }
                        run.cost_usd += cost_total;
                    }
                }
            }
            AgentEvent::ToolExecutionStart { tool_call_id, .. } => {
                state.tool_starts.insert(tool_call_id.clone(), now);
            }
            AgentEvent::ToolExecutionEnd {
                tool_call_id,
                tool_name,
                entry,
            } => {
                // `is_error` is derived: no entry (a faulted or
                // orphaned tool task), or the entry's tool-result
                // message reports `is_error`.
                let is_error = entry.as_ref().is_none_or(|entry| {
                    entry
                        .model
                        .as_deref()
                        .unwrap_or_default()
                        .iter()
                        .find_map(|message| match message {
                            Message::ToolResult(result) => Some(result.is_error),
                            Message::System(_) | Message::User(_) | Message::Assistant(_) => None,
                        })
                        .unwrap_or(false)
                });
                let started_at = state.tool_starts.remove(tool_call_id);
                let duration_ms = started_at.map_or(0, |start| now.saturating_sub(start));
                let category = ToolCategory::from_tool_name(tool_name);
                if let Some(run) = state.active_run.as_mut() {
                    run.tool_call_count += 1;
                    if is_error {
                        run.tool_error_count += 1;
                    }
                    run.tool_duration_ms += duration_ms;
                    let tool_stats = run.tool_summary.entry(category).or_default();
                    tool_stats.calls += 1;
                    tool_stats.failures += u64::from(is_error);
                    tool_stats.duration_ms += duration_ms;
                    tool_stats.max_duration_ms = tool_stats.max_duration_ms.max(duration_ms);
                }
            }
            AgentEvent::RunEnd { .. } => {
                if let Some(run) = state.active_run.as_mut() {
                    run.ended = true;
                    run.ended_at = Some(now);
                }
            }
            AgentEvent::AutoRetryStart {
                at, error_message, ..
            } => {
                if let Some(run) = state.active_run.as_mut() {
                    run.retry_count += 1;
                    run.retry_pending = true;
                    run.last_error_text = Some(error_message.clone());
                    // `at` is the scheduled fire time in epoch
                    // milliseconds (the harness clock's `Date.now()`
                    // unit); the observed delay is the distance to now,
                    // clamped at zero for an already-elapsed schedule.
                    // (milliseconds as f64, whole below 2^53).
                    run.retry_wait_ms += (*at - now as f64).max(0.0) as u64;
                    // failover_count stays 0: durable events carry no
                    // backup-provider reason (another workstream owns
                    // failover).
                }
            }
            AgentEvent::AutoRetryEnd { .. } => {
                if let Some(run) = state.active_run.as_mut() {
                    run.retry_pending = false;
                    // The retried attempt continues this run: the
                    // failed call is behind a retry now, so the run's
                    // cost stays reported (with the failed attempts'
                    // usage included) unless the final attempt fails
                    // too.
                    run.usage_complete = true;
                }
            }
            AgentEvent::CompactionStart { task_id, .. } => {
                state.compaction_starts.insert(*task_id, now);
            }
            AgentEvent::CompactionEnd { task_id, .. } => {
                // Counted into the active run only — compactions
                // outside a run never inflate session totals (a start
                // with no active run records nothing at its end
                // either).
                let started_at = state.compaction_starts.remove(task_id);
                if let Some(run) = state.active_run.as_mut() {
                    run.compaction_count += 1;
                    run.compaction_duration_ms +=
                        started_at.map_or(0, |start| now.saturating_sub(start));
                }
            }
            AgentEvent::TaskFailed { kind, message, .. } => {
                // Only the generation kind is a model error; tool
                // failures already report through ToolExecutionEnd.
                if kind == GENERATION_KIND {
                    if let Some(run) = state.active_run.as_mut() {
                        run.model_error_count += 1;
                        run.last_error_text = Some(message.clone());
                        let classification = classify_error_message(message);
                        if let Some(category) = ERROR_CATEGORIES
                            .iter()
                            .find(|known| **known == classification.category)
                            .copied()
                        {
                            *run.error_category_counts.entry(category).or_default() += 1;
                        }
                    }
                }
            }
            AgentEvent::EntryAppended { entry } => {
                // One durable child-usage attribution row (the durable
                // form of the old engine's producer feed for the
                // `rlm_child_*` counters). A torn row counts nothing.
                if entry.kind == CHILD_USAGE_ATTRIBUTED_KIND {
                    let attribution = entry.data.as_ref().and_then(|data| {
                        eukhe_chord::json::from_json::<ChildUsageAttributionData>(data).ok()
                    });
                    if let Some(attribution) = attribution {
                        self.counters.with(|values| {
                            values.rlm_child_usage_count += 1;
                            values.rlm_child_input_tokens += attribution.child_usage.input;
                            values.rlm_child_output_tokens += attribution.child_usage.output;
                            values.rlm_child_cache_read_tokens +=
                                attribution.child_usage.cache_read;
                            values.rlm_child_cache_write_tokens +=
                                attribution.child_usage.cache_write;
                            let cost = attribution.child_usage.cost.total;
                            if cost.is_finite() && cost > 0.0 {
                                values.rlm_child_cost += cost;
                            }
                        });
                    }
                }
            }
            // Snapshot, InboxUpdate, Submission, AgentChanged,
            // UsageChanged, and DeferredPoll carry no
            // facts the old subscriber used; TurnEnd carries none
            // (turn_count comes from TurnStart) and
            // ToolExecutionUpdate is mid-execution progress. All are
            // still run-scoped events: while the cached decision is off
            // they sever (a tool whose execution spans an opt-out
            // observed at a boundary never counts into a surviving
            // run).
            AgentEvent::Snapshot(_)
            | AgentEvent::InboxUpdate { .. }
            | AgentEvent::Submission { .. }
            | AgentEvent::DeferredPoll { .. }
            | AgentEvent::AgentChanged { .. }
            | AgentEvent::UsageChanged { .. }
            | AgentEvent::TurnEnd
            | AgentEvent::ToolExecutionUpdate { .. } => {}
        }
    }

    /// Feed one observed batch (a commit's events) in order.
    pub fn observe_batch(&self, batch: &[AgentEvent]) {
        for event in batch {
            self.handle_event(event);
        }
    }

    /// A feature attempt's observed result at a host seam, counted as
    /// `feature_<name>_<outcome>_count` on `agent session ended`. The
    /// configuration choice is not reported.
    pub fn note_feature_outcome(
        &self,
        feature_name: &'static str,
        outcome: &'static str,
        _configuration_choice: Option<&'static str>,
    ) {
        if let Some(key) = feature_outcome_key(feature_name, outcome) {
            self.counters
                .with(|values| *values.feature_outcomes.entry(key).or_default() += 1);
        }
    }

    /// Finalize any active run, emit `agent session ended`, and flush.
    /// The host calls this at session close (TUI exit, worker shutdown,
    /// kill); the `ended` flag makes a second close path a no-op,
    /// matching the TS single `registerDisposeCallback` firing. A run
    /// still open across an opt-out severs before the finalize, so an
    /// off window's run never reports after a re-enable.
    ///
    /// # Errors
    ///
    /// Returns the telemetry client's flush error, if any.
    pub async fn end(&self) -> anyhow::Result<()> {
        if self.ended.swap(true, std::sync::atomic::Ordering::SeqCst) {
            return Ok(());
        }
        {
            let mut state = lock(&self.state);
            // Session close is the LAST recording seam: the live switch
            // is asked here like a turn boundary, so a run still open
            // when the opt-out landed after its last boundary severs
            // instead of reporting; the client's flush drops whatever
            // the mid-turn opt-out already queued.
            observe_turn_boundary(&mut state);
            finalize_run_locked(&self.client, &self.execution_mode, &mut state);
        }
        let mut properties = self.session_properties();
        {
            let state = lock(&self.state);
            let totals = &state.totals;
            properties.set(
                "duration_ms",
                Value::from((state.now)().saturating_sub(state.started_at)),
            );
            properties.set("prompt_count", Value::from(totals.prompt_count));
            properties.set("run_count", Value::from(totals.run_count));
            properties.set(
                "successful_run_count",
                Value::from(totals.successful_run_count),
            );
            properties.set("failed_run_count", Value::from(totals.failed_run_count));
            properties.set("aborted_run_count", Value::from(totals.aborted_run_count));
            properties.set("tool_call_count", Value::from(totals.tool_call_count));
            properties.set("compaction_count", Value::from(totals.compaction_count));
            properties.set(
                "model_call_count",
                Value::from(totals.usage.model_call_count),
            );
            properties.set("input_tokens", Value::from(totals.usage.input));
            properties.set("output_tokens", Value::from(totals.usage.output));
            properties.set("cache_read_tokens", Value::from(totals.usage.cache_read));
            properties.set("cache_write_tokens", Value::from(totals.usage.cache_write));
            properties.set("total_tokens", Value::from(totals.usage.total_tokens));
            // v2 (#2117): the session's terminal outcome. `end()` is the
            // normal dispose path (interactive exit, worker shutdown); a
            // crash never reaches it, and the archive path emits
            // `session archived` first.
            properties.set("terminal_outcome", Value::from("success"));
            properties.set("retry_count", Value::from(totals.retry_count));
            properties.set("failover_count", Value::from(totals.failover_count));
            properties.set("model_error_count", Value::from(totals.model_error_count));
        }
        self.counters.write_into(&mut properties);
        self.client.track("agent session ended", properties);
        self.client.flush().await
    }

    /// `session archived` (schema v1): the session reached the archive
    /// state (daemon `kill`). Lifetime in ms; emitted before `end()` on
    /// that path.
    pub fn note_archived(&self) {
        let mut properties = self.session_properties();
        {
            let state = lock(&self.state);
            properties.set(
                "duration_ms",
                Value::from((state.now)().saturating_sub(state.started_at)),
            );
        }
        self.client.track("session archived", properties);
    }

    /// A `/skill:<name>` submission expanded into its skill block,
    /// counted as `skill_use_count` on `agent session ended`; the skill
    /// name never uploads.
    pub fn note_skill_used(&self) {
        self.counters.with(|values| values.skill_use_count += 1);
    }

    /// One durable child-usage attribution row landed in the parent
    /// session (the RLM producer's flush), summed into the `rlm_child_*`
    /// counters on `agent session ended`.
    pub fn note_child_usage_attributed(
        &self,
        input_tokens: u64,
        output_tokens: u64,
        cache_read_tokens: u64,
        cache_write_tokens: u64,
        cost: f64,
    ) {
        self.counters.with(|values| {
            values.rlm_child_usage_count += 1;
            values.rlm_child_input_tokens += input_tokens;
            values.rlm_child_output_tokens += output_tokens;
            values.rlm_child_cache_read_tokens += cache_read_tokens;
            values.rlm_child_cache_write_tokens += cache_write_tokens;
            if cost.is_finite() && cost > 0.0 {
                values.rlm_child_cost += cost;
            }
        });
    }

    /// Base properties + `session_id` for per-event properties.
    fn session_properties(&self) -> Properties {
        let mut properties = base_properties(&self.execution_mode);
        let state = lock(&self.state);
        properties.set("session_id", Value::from(state.session_id.as_str()));
        properties
    }
}

/// The entry's first model message, when it is an assistant message.
fn assistant_of(entry: &EntryRecord) -> Option<AssistantMessage> {
    match entry.model.as_ref()?.first()? {
        Message::Assistant(assistant) => Some(assistant.clone()),
        Message::System(_) | Message::User(_) | Message::ToolResult(_) => None,
    }
}

/// Record the run's trigger the first time it disambiguates.
fn resolve_trigger(state: &mut TelemetryState, trigger: RunTrigger) {
    if let Some(run) = state.active_run.as_mut().filter(|run| run.trigger_pending) {
        run.trigger_pending = false;
        run.trigger = trigger;
    }
}

/// Finalize the active run and emit `agent run completed` (TS
/// `finalizeRun`), merging run totals into session totals.
fn finalize_run_locked(client: &TelemetryClient, execution_mode: &str, state: &mut TelemetryState) {
    let Some(mut run) = state.active_run.take() else {
        return;
    };
    let now = (state.now)();
    let run_end = run.ended_at.unwrap_or(now);
    let outcome = match run.last_assistant.as_ref() {
        Some(assistant) => run_outcome(Some(assistant)),
        // A run with no assistant row at all: a recorded model error
        // (a failed generation task, or retry text) failed it; an empty
        // run (opened and closed without a model call) simply succeeded
        // — the old engine never finalized a run without an assistant
        // message, the durable event stream can.
        None if run.model_error_count > 0 || run.last_error_text.is_some() => "error",
        None => "success",
    };
    state.totals.run_count += 1;
    state.totals.tool_call_count += run.tool_call_count;
    state.totals.compaction_count += run.compaction_count;
    match outcome {
        "success" => state.totals.successful_run_count += 1,
        "aborted" => state.totals.aborted_run_count += 1,
        _ => state.totals.failed_run_count += 1,
    }
    state.totals.usage.merge(&run.usage);

    state.totals.retry_count += run.retry_count;
    state.totals.failover_count += run.failover_count;
    state.totals.model_error_count += run.model_error_count;

    let mut properties = base_properties(execution_mode);
    properties.set("session_id", Value::from(state.session_id.as_str()));
    properties.set("outcome", Value::from(outcome));
    properties.set(
        "duration_ms",
        Value::from(run_end.saturating_sub(run.started_at)),
    );
    properties.set("visible_ttft_ms", opt_value(run.visible_ttft_ms));
    properties.set("first_model_event_ms", opt_value(run.first_model_event_ms));
    properties.set("model_latency_ms", Value::from(run.model_latency_ms));
    properties.set(
        "max_model_latency_ms",
        Value::from(run.max_model_latency_ms),
    );
    properties.set("model_call_count", Value::from(run.usage.model_call_count));
    properties.set("turn_count", Value::from(run.turn_count));
    properties.set("tool_call_count", Value::from(run.tool_call_count));
    properties.set("tool_error_count", Value::from(run.tool_error_count));
    properties.set("input_tokens", Value::from(run.usage.input));
    properties.set("output_tokens", Value::from(run.usage.output));
    properties.set("cache_read_tokens", Value::from(run.usage.cache_read));
    properties.set("cache_write_tokens", Value::from(run.usage.cache_write));
    properties.set("total_tokens", Value::from(run.usage.total_tokens));
    properties.set("compaction_count", Value::from(run.compaction_count));
    properties.set("retry_count", Value::from(run.retry_count));
    properties.set("failover_count", Value::from(run.failover_count));
    properties.set(
        "provider_category",
        Value::from(provider_category(
            run.last_assistant.as_ref().map(|m| m.provider.as_str()),
        )),
    );
    properties.set(
        "model_category",
        Value::from(
            run.last_assistant
                .as_ref()
                .map_or("unknown", |m| model_category(&m.model)),
        ),
    );
    properties.set(
        "error_category",
        error_category(run.last_assistant.as_ref()),
    );
    // v2 (#2117) enrichment:
    properties.set("run_id", Value::from(run.run_id.as_str()));
    properties.set("run_index", Value::from(run.run_index));
    properties.set("trigger", Value::from(run.trigger.as_str()));
    properties.set(
        "stop_reason",
        Value::from(stop_reason(run.last_assistant.as_ref())),
    );
    properties.set("terminal_outcome", Value::from(terminal_outcome(outcome)));
    properties.set(
        "successful_model_call_count",
        Value::from(run.successful_model_call_count),
    );
    if run.usage.model_call_count > 0 {
        properties.set("usage_complete", Value::from(run.usage_complete));
    }
    if run.usage_complete && run.usage.model_call_count > 0 && run.cost_usd > 0.0 {
        // Estimated cost requires known pricing and complete usage for
        // every call; the conservative direction keeps it null otherwise.
        properties.set("estimated_cost_usd", Value::from(run.cost_usd));
    }
    let assistant_errored =
        run.last_assistant.as_ref().map(|m| m.stop_reason) == Some(StopReason::Error);
    if assistant_errored || (run.last_assistant.is_none() && run.last_error_text.is_some()) {
        // The final assistant's own error message when it carries one;
        // otherwise the run's last recorded error text (an AutoRetryStart
        // or generation TaskFailed message) — the old engine always had
        // the assistant's text, the durable events may not (a failed
        // generation task leaves no assistant row at all).
        let error_text = run
            .last_assistant
            .as_ref()
            .and_then(|m| m.error_message.as_deref())
            .or(run.last_error_text.as_deref())
            .unwrap_or_default();
        properties.set(
            "error_subtype",
            Value::from(classify_error_message(error_text).subtype),
        );
    }
    properties.set("first_reasoning_ms", opt_value(run.first_reasoning_ms));
    properties.set("run_to_first_text_ms", opt_value(run.run_to_first_text_ms));
    properties.set("tool_duration_ms", Value::from(run.tool_duration_ms));
    properties.set("retry_wait_ms", Value::from(run.retry_wait_ms));
    properties.set("max_stream_gap_ms", opt_value(run.max_stream_gap_ms));
    properties.set(
        "compaction_duration_ms",
        Value::from(run.compaction_duration_ms),
    );
    properties.set(
        "model_latency_p50_ms",
        opt_value(median(&mut run.model_latencies)),
    );
    properties.set("model_error_count", Value::from(run.model_error_count));
    for (category, count) in &run.error_category_counts {
        properties.set(&format!("error_{category}_count"), Value::from(*count));
    }
    // Per built-in tool by name; every MCP and custom tool folds into the
    // `mcp_tool_*` / `custom_tool_*` aggregates (no raw tool names).
    for (category, stats) in &run.tool_summary {
        let prefix = match category {
            ToolCategory::Mcp => "mcp_tool".to_string(),
            ToolCategory::Custom | ToolCategory::Unknown => "custom_tool".to_string(),
            builtin => format!("tool_{}", builtin.as_str()),
        };
        for (suffix, value) in [
            ("call_count", stats.calls),
            ("error_count", stats.failures),
            ("duration_ms", stats.duration_ms),
            ("max_duration_ms", stats.max_duration_ms),
        ] {
            let key = format!("{prefix}_{suffix}");
            let total = properties.get(&key).and_then(Value::as_u64).unwrap_or(0);
            let value = if suffix == "max_duration_ms" {
                total.max(value)
            } else {
                total + value
            };
            properties.set(&key, Value::from(value));
        }
    }
    client.track("agent run completed", properties);
}

/// The median of the run's model-call latencies (the lower middle for an
/// even count); `None` without calls.
fn median(values: &mut [u64]) -> Option<u64> {
    if values.is_empty() {
        return None;
    }
    values.sort_unstable();
    Some(values[(values.len() - 1) / 2])
}

/// The #2117 `terminal_outcome` vocabulary: the legacy run outcome
/// (`success`/`error`/`aborted`) onto the terminal vocabulary (the legacy
/// `aborted` is the terminal `cancelled`).
fn terminal_outcome(run_outcome: &str) -> &'static str {
    match run_outcome {
        "success" => "success",
        "error" => "error",
        "aborted" => "cancelled",
        _ => "unknown",
    }
}

/// The #2117 `stop_reason` vocabulary for the final assistant message.
fn stop_reason(last_assistant: Option<&AssistantMessage>) -> &'static str {
    match last_assistant.map(|message| message.stop_reason) {
        Some(StopReason::Stop) => "stop",
        Some(StopReason::Length) => "length",
        Some(StopReason::ToolUse) => "toolUse",
        Some(StopReason::Error) => "error",
        Some(StopReason::Aborted) => "aborted",
        Some(StopReason::Pending | StopReason::Deferred) | None => "unknown",
    }
}

/// Build the product telemetry client from settings: the Prime Intellect
/// analytics sink (the TS endpoint and wire format; none in debug builds,
/// see [`telemetry_endpoint`]) plus the local JSONL transparency mirror
/// (default on, `telemetry.localMirror` disables it), behind the live
/// [`telemetry_switch`] re-read before every delivery pass. Never fails: a
/// broken install id falls back to a no-op client (TS parity: capture
/// disables itself when the installation identity cannot be created).
pub fn build_client(
    settings: &crate::settings::SettingsManager,
    agent_dir: &std::path::Path,
) -> TelemetryClient {
    let mut config = TelemetryClientConfig::new("disabled");
    let install_id = eukhe_telemetry::install_id(agent_dir);
    match install_id {
        Ok(id) => {
            config.install_id = id;
            let mut sinks: Vec<Arc<dyn eukhe_telemetry::TelemetrySink>> = Vec::new();
            if let Some(endpoint) = telemetry_endpoint() {
                sinks.push(Arc::new(eukhe_telemetry::AnalyticsSink::new(endpoint)));
            }
            let local_mirror = settings
                .settings()
                .telemetry
                .as_ref()
                .and_then(|telemetry| telemetry.local_mirror)
                .unwrap_or(true);
            if local_mirror {
                sinks.push(Arc::new(eukhe_telemetry::FileSink::new(agent_dir)));
            }
            config.sinks = sinks;
            // `/telemetry off` (or a settings edit) applies to running
            // clients at their next delivery pass, no restart needed.
            let settings = settings.reopen();
            config.enabled = Some(Arc::new(move || {
                telemetry_switch(&settings.reopen()).enabled()
            }));
        }
        Err(error) => {
            tracing::warn!(error = %error, "telemetry install id unavailable; telemetry disabled");
            config.sinks = vec![Arc::new(eukhe_telemetry::NoopSink)];
        }
    }
    TelemetryClient::spawn(config).unwrap_or_else(|error| {
        // No runtime on this thread: an inert client whose tracks are
        // counted as dropped. Telemetry must never fail the session.
        tracing::warn!(error = %error, "telemetry worker unavailable; events will drop");
        TelemetryClient::inert()
    })
}

/// The recording seams' live opt-out switch: the same env-then-settings
/// resolution the delivery pass applies ([`telemetry_switch`]), resolved
/// live at the turn boundaries: an off (or an on) applies to the
/// recording seams at the next boundary, exactly like the client's
/// delivery gate applies it at the flush.
#[must_use]
pub fn telemetry_enabled_switch(cwd: &Path, agent_dir: &Path) -> RecordingSwitch {
    let settings = crate::settings::SettingsManager::create(cwd, agent_dir);
    RecordingSwitch {
        enabled: Arc::new(move || telemetry_switch(&settings.reopen()).enabled()),
    }
}

fn uuid() -> String {
    uuid::Uuid::new_v4().to_string()
}

fn now_millis() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_millis() as u64)
        .unwrap_or_default()
}
