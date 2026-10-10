//! Per-request phase timing for provider requests on the durable models
//! layer: the port of the old engine's
//! `session_engine::request_timing` clock (TS #2462,
//! `packages/coding-agent/src/core/request-timing.ts`).
//!
//! It answers "what is the agent waiting for" while the provider request
//! is in flight: the wire/server phases (request-sent -> first-byte
//! covers request body serialization, upload, and provider TTFB;
//! first-byte -> first-token the server-side TTFT; first-token ->
//! stream-done the decode) plus a stream-done summary carrying the final
//! usage, so a prompt-cache miss shows as cacheRead ~ 0 with cacheWrite ~
//! the full prompt.
//!
//! Enable with `EUKHE_REQUEST_TIMING=1` (env, inherited by daemon workers)
//! or `"requestTiming": true` in settings. Entries go to the shared JSONL
//! diagnostic log ([`crate::agent_log::AgentLog`],
//! `<agentDir>/logs/agent.jsonl`) under the component
//! `coding-agent.request-timing`, byte-identical to the old engine's
//! lines for every phase observable at the provider-stream seam.
//!
//! # Omissions versus the old engine
//!
//! Two old-engine phases happen above the provider-stream seam the
//! durable models layer sits at, and are therefore not observable here:
//!
//! - the `prompt-built` phase (turn dispatch -> the LLM message array is
//!   built) and with it the summary's `dispatchToPromptBuiltMs` delta and
//!   every `contextEntries` field — the durable generation only sees
//!   [`eukhe_types::pi_ai::Models`], never the loop's convert seam;
//! - `requestBytes` (the serialized request body size) and the outbound
//!   payload capture — the body is serialized inside the provider client,
//!   below this seam.
//!
//! Every other entry keeps the old JSON shape: component, phase names,
//! `requestSeq`, rounded milliseconds with one decimal, and the usage
//! fields.

use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Instant;

use eukhe_types::pi_ai::{AssistantMessage, AssistantMessageEvent, StopReason, Usage};
use serde_json::{json, Map, Value};

use crate::agent_log::{AgentLog, AgentLogLevel};

/// TS `REQUEST_TIMING_ENV`: the env override (inherited by daemon workers).
const REQUEST_TIMING_ENV: &str = "EUKHE_REQUEST_TIMING";

/// TS log component: `getLogger("coding-agent.request-timing")`.
const LOG_COMPONENT: &str = "coding-agent.request-timing";

/// Truthy follows the `EUKHE_OFFLINE`/`EUKHE_TIMING` convention: 1/true/yes
/// (TS `truthyEnvFlag`).
fn truthy_env_flag(value: Option<&str>) -> bool {
    let Some(value) = value else {
        return false;
    };
    let normalized = value.to_ascii_lowercase();
    normalized == "1" || normalized == "true" || normalized == "yes"
}

// ---------------------------------------------------------------------------
// Wiring
// ---------------------------------------------------------------------------

/// Per-agent-dir timing state: the shared JSONL log the entries go to and
/// the request-sequence counter (the old engine's `RequestTimingWiring`,
/// minus the loop correlation slots this seam cannot observe).
pub(crate) struct RequestTimingWiring {
    log: AgentLog,
    request_seq: AtomicU64,
}

impl RequestTimingWiring {
    /// New wiring: entries go to `<agentDir>/logs/agent.jsonl`.
    #[must_use]
    pub(crate) fn new(agent_dir: &Path) -> Self {
        Self {
            log: AgentLog::new(agent_dir, LOG_COMPONENT),
            request_seq: AtomicU64::new(0),
        }
    }

    /// Request timing is on when either the settings flag
    /// (`"requestTiming": true`) or the env override is set (TS
    /// `isRequestTimingEnabled`). The env half is read live so the flag
    /// can change without a restart.
    #[must_use]
    pub(crate) fn enabled(settings_flag: bool) -> bool {
        settings_flag || truthy_env_flag(std::env::var(REQUEST_TIMING_ENV).ok().as_deref())
    }

    /// TS `nextRequestSeq`: 1-based, one number per request, shared by
    /// every entry of one request.
    fn next_request_seq(&self) -> u64 {
        self.request_seq.fetch_add(1, Ordering::Relaxed) + 1
    }

    /// Info-level entry (TS `Logger.info`).
    fn info(&self, msg: &str, fields: Map<String, Value>) {
        self.log.log(AgentLogLevel::Info, msg, fields);
    }
}

// ---------------------------------------------------------------------------
// Per-request clock
// ---------------------------------------------------------------------------

/// Final usage carried by the summary (TS `{input, output, cacheRead,
/// cacheWrite}`).
#[derive(Debug, Clone, Copy)]
struct TimingUsage {
    input: u64,
    output: u64,
    cache_read: u64,
    cache_write: u64,
}

impl From<&Usage> for TimingUsage {
    fn from(usage: &Usage) -> Self {
        TimingUsage {
            input: usage.input,
            output: usage.output,
            cache_read: usage.cache_read,
            cache_write: usage.cache_write,
        }
    }
}

impl TimingUsage {
    fn fields(&self) -> Value {
        json!({
            "input": self.input,
            "output": self.output,
            "cacheRead": self.cache_read,
            "cacheWrite": self.cache_write,
        })
    }
}

/// The summary outcome (TS `emitSummary(outcome: "done" | "aborted" |
/// "failed")`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    Done,
    Aborted,
    Failed,
}

impl Outcome {
    fn as_str(self) -> &'static str {
        match self {
            Outcome::Done => "done",
            Outcome::Aborted => "aborted",
            Outcome::Failed => "failed",
        }
    }
}

/// Mutable phase clock for one provider request (the old engine's
/// `RequestTiming`, created at its streamFn seam). Phase transitions are
/// logged as they happen so a hung request shows the last completed phase
/// in the live log. Create only on the enabled path; one per request.
pub(crate) struct RequestTiming {
    wiring: Arc<RequestTimingWiring>,
    /// The request's model identity (`RequestInfo.model`; the provider,
    /// api, and session fields the old engine read off its stream options
    /// are not observable at this seam and stay omitted, exactly like the
    /// old engine omitted empty ones).
    model: String,
    request_seq: u64,
    started_at: Instant,
    request_sent_at: Option<Instant>,
    first_byte_at: Option<Instant>,
    first_token_at: Option<Instant>,
    stop_reason: Option<String>,
    error_message: Option<String>,
    usage: Option<TimingUsage>,
    summary_emitted: bool,
}

/// Create one request's clock and take its sequence number.
#[must_use]
pub(crate) fn start(wiring: Arc<RequestTimingWiring>, model: &str) -> RequestTiming {
    let request_seq = wiring.next_request_seq();
    RequestTiming {
        wiring,
        model: model.to_string(),
        request_seq,
        started_at: Instant::now(),
        request_sent_at: None,
        first_byte_at: None,
        first_token_at: None,
        stop_reason: None,
        error_message: None,
        usage: None,
        summary_emitted: false,
    }
}

impl RequestTiming {
    /// request-sent: the request is dispatched to the provider (the old
    /// engine's payload-hook mark). Measured from the clock's creation,
    /// since the prompt-built timestamp lives above this seam.
    pub(crate) fn request_sent(&mut self) {
        if self.request_sent_at.is_some() {
            return;
        }
        let now = Instant::now();
        self.request_sent_at = Some(now);
        let phase_ms = round_ms(elapsed_ms(self.started_at, now));
        let mut fields = Map::new();
        fields.insert("phase".to_string(), json!("request-sent"));
        fields.insert("phaseMs".to_string(), json!(phase_ms));
        self.emit("request timing", fields);
    }

    /// Observe one streamed event: first-byte on the start event (the old
    /// engine marked it on the HTTP response hook, with the start event as
    /// its fallback — this seam sees only the stream, so the start event
    /// is the mark), first-token on the first thinking/text/toolcall start
    /// or delta (TS `FIRST_TOKEN_EVENT_TYPES`). Every other event carries
    /// no phase of its own; terminal events are the caller's `done` /
    /// `failed` calls.
    pub(crate) fn event(&mut self, event: &AssistantMessageEvent) {
        if is_request_timing_first_token_event(event) {
            self.mark_first_token();
        }
        if matches!(event, AssistantMessageEvent::Start { .. }) {
            self.mark_first_byte();
        }
    }

    /// first-byte: the provider's stream opened (provider TTFB complete).
    fn mark_first_byte(&mut self) {
        if self.first_byte_at.is_some() {
            return;
        }
        let now = Instant::now();
        self.first_byte_at = Some(now);
        // Without a request-sent timestamp (the request was never marked
        // sent) the delta spans from the clock's creation, not just the
        // wire wait (TS `phaseFrom`, whose fallback label is kept
        // byte-identical to the old lines).
        let (from, phase_from) = match self.request_sent_at {
            Some(sent) => (sent, None),
            None => (self.started_at, Some("prompt-built")),
        };
        let phase_ms = round_ms(elapsed_ms(from, now));
        let mut fields = Map::new();
        fields.insert("phase".to_string(), json!("first-byte"));
        fields.insert("phaseMs".to_string(), json!(phase_ms));
        if let Some(phase_from) = phase_from {
            fields.insert("phaseFrom".to_string(), json!(phase_from));
        }
        self.emit("request timing", fields);
    }

    /// first-content-token: first streamed content block (thinking/text/
    /// toolcall), which clears the TUI Waiting state.
    fn mark_first_token(&mut self) {
        if self.first_token_at.is_some() {
            return;
        }
        let now = Instant::now();
        self.first_token_at = Some(now);
        let from = self
            .first_byte_at
            .or(self.request_sent_at)
            .unwrap_or(self.started_at);
        let phase_ms = round_ms(elapsed_ms(from, now));
        let mut fields = Map::new();
        fields.insert("phase".to_string(), json!("first-token"));
        fields.insert("phaseMs".to_string(), json!(phase_ms));
        self.emit("request timing", fields);
    }

    /// Terminal success (the stream's done event): emit the stream-done
    /// summary with the final message's usage, stop reason, and error
    /// message. Safe to call once; later calls are ignored.
    pub(crate) fn done(&mut self, message: &AssistantMessage) {
        self.stop_reason = Some(message.stop_reason.as_str().to_string());
        self.error_message.clone_from(&message.error_message);
        self.usage = Some(TimingUsage::from(&message.usage));
        self.emit_summary(Outcome::Done);
    }

    /// Terminal failure before or without a done (the stream's error
    /// event, or a request the provider rejected): emit the failed
    /// summary. An aborted stop reason reports as aborted, exactly like
    /// the old engine's error-event arm.
    pub(crate) fn failed(&mut self, error: &AssistantMessage) {
        self.stop_reason = Some(error.stop_reason.as_str().to_string());
        self.error_message.clone_from(&error.error_message);
        self.usage = Some(TimingUsage::from(&error.usage));
        self.emit_summary(if error.stop_reason == StopReason::Aborted {
            Outcome::Aborted
        } else {
            Outcome::Failed
        });
    }

    /// Emit the summary with every known phase delta (TS `emitSummary`).
    fn emit_summary(&mut self, outcome: Outcome) {
        if self.summary_emitted {
            return;
        }
        self.summary_emitted = true;
        let done_at = Instant::now();
        let mut phases = Map::new();
        if let Some(sent) = self.request_sent_at {
            phases.insert(
                "promptBuiltToRequestSentMs".to_string(),
                json!(round_ms(elapsed_ms(self.started_at, sent))),
            );
        }
        if let (Some(sent), Some(first_byte)) = (self.request_sent_at, self.first_byte_at) {
            phases.insert(
                "requestSentToFirstByteMs".to_string(),
                json!(round_ms(elapsed_ms(sent, first_byte))),
            );
        }
        let first_token_from = self.first_byte_at.or(self.request_sent_at);
        if let (Some(first_token), Some(from)) = (self.first_token_at, first_token_from) {
            phases.insert(
                "firstByteToFirstTokenMs".to_string(),
                json!(round_ms(elapsed_ms(from, first_token))),
            );
        }
        if let Some(first_token) = self.first_token_at {
            phases.insert(
                "firstTokenToStreamDoneMs".to_string(),
                json!(round_ms(elapsed_ms(first_token, done_at))),
            );
        }
        let mut fields = Map::new();
        fields.insert("phase".to_string(), json!("stream-done"));
        fields.insert("requestSeq".to_string(), json!(self.request_seq));
        fields.insert("outcome".to_string(), json!(outcome.as_str()));
        fields.insert("model".to_string(), json!(self.model));
        fields.insert("phases".to_string(), Value::Object(phases));
        fields.insert(
            "totalMs".to_string(),
            json!(round_ms(elapsed_ms(self.started_at, done_at))),
        );
        if let Some(stop_reason) = &self.stop_reason {
            fields.insert("stopReason".to_string(), json!(stop_reason));
        }
        if let Some(error_message) = &self.error_message {
            fields.insert("errorMessage".to_string(), json!(error_message));
        }
        if let Some(usage) = self.usage {
            fields.insert("usage".to_string(), usage.fields());
        }
        self.wiring.info("request timing summary", fields);
    }

    /// TS `emit`: phase entry with the request sequence and model identity.
    fn emit(&self, msg: &str, mut fields: Map<String, Value>) {
        fields.insert("requestSeq".to_string(), json!(self.request_seq));
        fields.insert("model".to_string(), json!(self.model));
        self.wiring.info(msg, fields);
    }
}

/// First streamed content events (TS `FIRST_TOKEN_EVENT_TYPES`):
/// thinking/text/toolcall starts and deltas.
fn is_request_timing_first_token_event(event: &AssistantMessageEvent) -> bool {
    matches!(
        event,
        AssistantMessageEvent::TextStart { .. }
            | AssistantMessageEvent::TextDelta { .. }
            | AssistantMessageEvent::ThinkingStart { .. }
            | AssistantMessageEvent::ThinkingDelta { .. }
            | AssistantMessageEvent::ToolCallStart { .. }
            | AssistantMessageEvent::ToolCallDelta { .. }
    )
}

/// `performance.now()` delta in milliseconds.
fn elapsed_ms(from: Instant, to: Instant) -> f64 {
    (to - from).as_secs_f64() * 1000.0
}

/// TS `roundMs`: one decimal of precision.
fn round_ms(delta_ms: f64) -> f64 {
    (delta_ms * 10.0).round() / 10.0
}

#[cfg(test)]
mod tests {
    use super::*;
    use eukhe_types::pi_ai::{AssistantContentBlock, ThinkingContent, UsageCost};

    /// Tests that touch the `EUKHE_REQUEST_TIMING` env serialize on this
    /// lock: the process env is global across parallel test threads.
    static REQUEST_TIMING_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    /// TS `finalMessage()`: the usage the summary must account.
    fn final_message() -> AssistantMessage {
        let mut message = empty_partial();
        message.content = vec![AssistantContentBlock::Thinking(ThinkingContent {
            thinking: "hm".to_string(),
            thinking_signature: None,
            redacted: None,
        })];
        message.usage = Usage {
            input: 800_000,
            output: 12,
            cache_read: 790_000,
            cache_write: 0,
            cache_write_1h: None,
            reasoning: None,
            total_tokens: 800_012,
            cost: UsageCost::default(),
        };
        message
    }

    fn empty_partial() -> AssistantMessage {
        AssistantMessage {
            content: Vec::new(),
            api: "openai-completions".to_string(),
            provider: "bench".to_string(),
            model: "bench/bench-model".to_string(),
            response_model: None,
            response_id: None,
            provider_thinking_level: None,
            thinking_level: None,
            diagnostics: None,
            usage: Usage::default(),
            stop_reason: StopReason::Stop,
            deferred: None,
            error_message: None,
            raw_stop_reason: None,
            end_turn: None,
            timestamp: 0,
            duration_ms: None,
        }
    }

    /// The timing entries from the JSONL log (TS `timingEntries()` filters
    /// the sink by component).
    fn timing_entries(path: &Path) -> Vec<Value> {
        let content = std::fs::read_to_string(path).unwrap_or_default();
        content
            .lines()
            .filter_map(|line| serde_json::from_str::<Value>(line).ok())
            .filter(|entry| entry.get("component").and_then(Value::as_str) == Some(LOG_COMPONENT))
            .collect()
    }

    fn phases_of(entries: &[Value]) -> Vec<&str> {
        entries
            .iter()
            .map(|entry| {
                entry
                    .get("phase")
                    .and_then(Value::as_str)
                    .unwrap_or_default()
            })
            .collect()
    }

    /// Assert a measured-milliseconds field is present and non-negative,
    /// then remove it so the whole entry object can be compared.
    fn strip_measured(entry: &Value, keys: &[&str]) -> Value {
        let mut stripped = entry.clone();
        for key in keys {
            let measured = stripped
                .get(*key)
                .cloned()
                .unwrap_or_else(|| panic!("field {key} present: {entry}"));
            let measured = measured
                .as_f64()
                .unwrap_or_else(|| panic!("field {key} numeric: {entry}"));
            assert!(measured >= 0.0, "field {key} = {measured}");
            stripped
                .as_object_mut()
                .unwrap()
                .remove(*key)
                .unwrap_or_else(|| panic!("field {key} removed twice"));
        }
        stripped
    }

    /// Drop the log's reserved per-entry keys the old tests did not pin
    /// (`ts`, `pid`).
    fn strip_reserved(entry: Value) -> Value {
        let mut entry = entry;
        let object = entry.as_object_mut().unwrap();
        object.remove("ts");
        object.remove("pid");
        entry
    }

    fn wiring_at(dir: &Path) -> Arc<RequestTimingWiring> {
        Arc::new(RequestTimingWiring::new(dir))
    }

    /// The full timeline through this seam: request-sent, first-byte (from
    /// the start event), first-token, and the done summary — the entries,
    /// their order, and their whole shapes (every measured delta present
    /// and non-negative, the TS fake-timer pins replaced by shape pins).
    #[test]
    fn emits_the_full_timeline() {
        let dir = tempfile::tempdir().unwrap();
        let log_path = dir.path().join("logs/agent.jsonl");
        let wiring = wiring_at(dir.path());
        let mut timing = start(wiring, "bench/bench-model");
        timing.request_sent();
        timing.event(&AssistantMessageEvent::Start {
            partial: empty_partial(),
        });
        timing.event(&AssistantMessageEvent::TextDelta {
            content_index: 0,
            delta: "hm".to_string(),
            partial: empty_partial(),
        });
        timing.event(&AssistantMessageEvent::TextEnd {
            content_index: 0,
            content: "hm".to_string(),
            partial: empty_partial(),
        });
        timing.done(&final_message());

        let entries = timing_entries(&log_path);
        assert_eq!(
            phases_of(&entries).join(","),
            "request-sent,first-byte,first-token,stream-done",
            "entries: {entries:?}"
        );
        let seqs: Vec<&Value> = entries
            .iter()
            .filter_map(|entry| entry.get("requestSeq"))
            .collect();
        assert_eq!(seqs.len(), 4, "every entry carries requestSeq");
        assert!(
            seqs.iter().all(|seq| *seq == seqs[0]),
            "one request sequence: {seqs:?}"
        );
        assert_eq!(
            strip_reserved(strip_measured(&entries[0], &["phaseMs"])),
            json!({
                "level": "info",
                "component": LOG_COMPONENT,
                "msg": "request timing",
                "phase": "request-sent",
                "requestSeq": 1,
                "model": "bench/bench-model",
            })
        );
        assert_eq!(
            strip_reserved(strip_measured(&entries[1], &["phaseMs"])),
            json!({
                "level": "info",
                "component": LOG_COMPONENT,
                "msg": "request timing",
                "phase": "first-byte",
                "requestSeq": 1,
                "model": "bench/bench-model",
            })
        );
        assert_eq!(
            strip_reserved(strip_measured(&entries[2], &["phaseMs"])),
            json!({
                "level": "info",
                "component": LOG_COMPONENT,
                "msg": "request timing",
                "phase": "first-token",
                "requestSeq": 1,
                "model": "bench/bench-model",
            })
        );
        let mut summary = strip_measured(&entries[3], &["totalMs"]);
        let phases = summary.get("phases").cloned().unwrap();
        for key in [
            "promptBuiltToRequestSentMs",
            "requestSentToFirstByteMs",
            "firstByteToFirstTokenMs",
            "firstTokenToStreamDoneMs",
        ] {
            let phase_ms = phases
                .get(key)
                .and_then(Value::as_f64)
                .unwrap_or_else(|| panic!("phase {key} present: {phases}"));
            assert!(phase_ms >= 0.0, "phase {key} = {phase_ms}");
        }
        summary
            .as_object_mut()
            .expect("an object")
            .remove("phases")
            .expect("the phases strip");
        assert_eq!(
            strip_reserved(summary),
            json!({
                "level": "info",
                "component": LOG_COMPONENT,
                "msg": "request timing summary",
                "phase": "stream-done",
                "requestSeq": 1,
                "outcome": "done",
                "model": "bench/bench-model",
                "stopReason": "stop",
                "usage": {
                    "input": 800_000,
                    "output": 12,
                    "cacheRead": 790_000,
                    "cacheWrite": 0,
                },
            })
        );
    }

    /// A request never marked sent (the old engine's faux-provider shape):
    /// the request-sent entry and its summary deltas are absent, and
    /// first-byte measures from the clock's creation with the TS
    /// `phaseFrom` fallback label.
    #[test]
    fn first_byte_falls_back_without_request_sent() {
        let dir = tempfile::tempdir().unwrap();
        let log_path = dir.path().join("logs/agent.jsonl");
        let wiring = wiring_at(dir.path());
        let mut timing = start(wiring, "bench/bench-model");
        timing.event(&AssistantMessageEvent::Start {
            partial: empty_partial(),
        });
        timing.event(&AssistantMessageEvent::ThinkingDelta {
            content_index: 0,
            delta: "hm".to_string(),
            partial: empty_partial(),
        });
        timing.done(&final_message());

        let entries = timing_entries(&log_path);
        assert_eq!(
            phases_of(&entries).join(","),
            "first-byte,first-token,stream-done",
            "entries: {entries:?}"
        );
        assert_eq!(
            strip_reserved(strip_measured(&entries[0], &["phaseMs"])),
            json!({
                "level": "info",
                "component": LOG_COMPONENT,
                "msg": "request timing",
                "phase": "first-byte",
                "phaseFrom": "prompt-built",
                "requestSeq": 1,
                "model": "bench/bench-model",
            })
        );
        let phases = entries[2].get("phases").cloned().unwrap();
        assert!(phases.get("promptBuiltToRequestSentMs").is_none());
        assert!(phases.get("requestSentToFirstByteMs").is_none());
        assert!(phases.get("firstByteToFirstTokenMs").is_some());
        assert!(phases.get("firstTokenToStreamDoneMs").is_some());
    }

    /// Only the first content event marks first-token (TS
    /// `FIRST_TOKEN_EVENT_TYPES` covers the starts and the deltas, the
    /// mark fires once).
    #[test]
    fn first_token_marks_only_the_first_content_event() {
        let dir = tempfile::tempdir().unwrap();
        let log_path = dir.path().join("logs/agent.jsonl");
        let wiring = wiring_at(dir.path());
        let mut timing = start(wiring, "bench/bench-model");
        timing.request_sent();
        timing.event(&AssistantMessageEvent::Start {
            partial: empty_partial(),
        });
        timing.event(&AssistantMessageEvent::TextStart {
            content_index: 0,
            partial: empty_partial(),
        });
        timing.event(&AssistantMessageEvent::TextDelta {
            content_index: 0,
            delta: "a".to_string(),
            partial: empty_partial(),
        });
        timing.event(&AssistantMessageEvent::ToolCallStart {
            content_index: 1,
            partial: empty_partial(),
        });
        timing.done(&final_message());

        let entries = timing_entries(&log_path);
        assert_eq!(
            phases_of(&entries).join(","),
            "request-sent,first-byte,first-token,stream-done",
            "entries: {entries:?}"
        );
    }

    /// TS "reports provider failures as failed instead of losing the
    /// timeline": the terminal failure summary carries the stop reason,
    /// error message, and usage from the error message.
    #[test]
    fn reports_terminal_error_events_as_failed() {
        let dir = tempfile::tempdir().unwrap();
        let log_path = dir.path().join("logs/agent.jsonl");
        let wiring = wiring_at(dir.path());
        let mut timing = start(wiring, "bench/bench-model");
        timing.request_sent();
        let mut error = empty_partial();
        error.stop_reason = StopReason::Error;
        error.error_message = Some("upstream 429".to_string());
        error.usage = Usage {
            input: 10,
            output: 0,
            cache_read: 0,
            cache_write: 0,
            cache_write_1h: None,
            reasoning: None,
            total_tokens: 10,
            cost: UsageCost::default(),
        };
        timing.failed(&error);

        let entries = timing_entries(&log_path);
        assert_eq!(
            phases_of(&entries).join(","),
            "request-sent,stream-done",
            "entries: {entries:?}"
        );
        let mut summary = strip_measured(&entries[1], &["totalMs"]);
        summary.as_object_mut().unwrap().remove("phases").unwrap();
        assert_eq!(
            strip_reserved(summary),
            json!({
                "level": "info",
                "component": LOG_COMPONENT,
                "msg": "request timing summary",
                "phase": "stream-done",
                "requestSeq": 1,
                "outcome": "failed",
                "model": "bench/bench-model",
                "stopReason": "error",
                "errorMessage": "upstream 429",
                "usage": {
                    "input": 10,
                    "output": 0,
                    "cacheRead": 0,
                    "cacheWrite": 0,
                },
            })
        );
    }

    /// An aborted terminal error reports as aborted, not failed (the old
    /// engine's error-event arm).
    #[test]
    fn aborted_errors_report_as_aborted() {
        let dir = tempfile::tempdir().unwrap();
        let log_path = dir.path().join("logs/agent.jsonl");
        let wiring = wiring_at(dir.path());
        let mut timing = start(wiring, "bench/bench-model");
        let mut error = empty_partial();
        error.stop_reason = StopReason::Aborted;
        timing.failed(&error);

        let entries = timing_entries(&log_path);
        assert_eq!(phases_of(&entries).join(","), "stream-done");
        assert_eq!(entries[0].get("outcome"), Some(&json!("aborted")));
        assert_eq!(entries[0].get("stopReason"), Some(&json!("aborted")));
    }

    /// The summary is emitted once: a done followed by a failed (or a
    /// second done) reports one stream-done entry, exactly like the old
    /// engine's `emitSummary` guard.
    #[test]
    fn the_summary_is_emitted_once() {
        let dir = tempfile::tempdir().unwrap();
        let log_path = dir.path().join("logs/agent.jsonl");
        let wiring = wiring_at(dir.path());
        let mut timing = start(wiring, "bench/bench-model");
        timing.done(&final_message());
        let mut error = empty_partial();
        error.stop_reason = StopReason::Error;
        timing.failed(&error);

        let entries = timing_entries(&log_path);
        assert_eq!(phases_of(&entries).join(","), "stream-done");
        assert_eq!(entries[0].get("outcome"), Some(&json!("done")));
    }

    /// TS `nextRequestSeq`: 1-based, one number per request shared by
    /// every entry of that request.
    #[test]
    fn request_sequences_increment_per_request() {
        let dir = tempfile::tempdir().unwrap();
        let log_path = dir.path().join("logs/agent.jsonl");
        let wiring = wiring_at(dir.path());
        let mut first = start(Arc::clone(&wiring), "bench/bench-model");
        let mut second = start(Arc::clone(&wiring), "bench/bench-model");
        first.request_sent();
        second.request_sent();
        drop(second);
        first.done(&final_message());

        let entries = timing_entries(&log_path);
        assert_eq!(
            phases_of(&entries).join(","),
            "request-sent,request-sent,stream-done"
        );
        assert_eq!(entries[0].get("requestSeq"), Some(&json!(1)));
        assert_eq!(entries[1].get("requestSeq"), Some(&json!(2)));
        assert_eq!(entries[2].get("requestSeq"), Some(&json!(1)));
    }

    /// TS `truthyEnvFlag` parsing (the env values that count as on).
    #[test]
    fn truthy_env_flag_follows_the_offline_convention() {
        assert!(!truthy_env_flag(None));
        assert!(!truthy_env_flag(Some("")));
        assert!(!truthy_env_flag(Some("0")));
        assert!(!truthy_env_flag(Some("no")));
        assert!(!truthy_env_flag(Some("off")));
        assert!(truthy_env_flag(Some("1")));
        assert!(truthy_env_flag(Some("true")));
        assert!(truthy_env_flag(Some("yes")));
        assert!(truthy_env_flag(Some("YES")));
        assert!(truthy_env_flag(Some("True")));
    }

    /// The env half of `enabled` (serialized on the env lock: the process
    /// env is global), plus the settings half.
    #[test]
    fn the_env_override_enables_request_timing() {
        let _env = REQUEST_TIMING_ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        std::env::remove_var(REQUEST_TIMING_ENV);
        assert!(!RequestTimingWiring::enabled(false));
        assert!(RequestTimingWiring::enabled(true));
        std::env::set_var(REQUEST_TIMING_ENV, "1");
        assert!(RequestTimingWiring::enabled(false));
        std::env::set_var(REQUEST_TIMING_ENV, "0");
        assert!(!RequestTimingWiring::enabled(false));
        std::env::remove_var(REQUEST_TIMING_ENV);
    }
}
