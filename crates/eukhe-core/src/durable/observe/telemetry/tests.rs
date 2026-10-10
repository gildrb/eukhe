//! The durable telemetry unit battery: the scripted run state machine
//! over durable agent events, and the session-end finalize surface.
use std::sync::Arc;
use std::time::Duration;

use eukhe_durable::harness::types::{AgentState, CompactionReason};
use eukhe_durable::harness::usage::UsageState;
use eukhe_durable::harness::{AgentEvent, MessageChange, SnapshotEvent, ToolEventCall};
use eukhe_durable::types::{ConversationId, EntryId, EntryRecord, SubmissionId, TaskId};
use eukhe_telemetry::{MockSink, TelemetryClient, TelemetryClientConfig};
use eukhe_types::pi_ai::{
    AssistantContentBlock, AssistantMessage, Message, StopReason, TextContent, ToolResultMessage,
    Usage, UsageCost, UserContent, UserMessage,
};
use serde_json::{json, Value};

use super::*;

/// Controllable clock: tests move it between emits.
#[derive(Clone, Default)]
struct TestClock {
    millis: Arc<std::sync::atomic::AtomicU64>,
}

impl TestClock {
    fn set(&self, millis: u64) {
        self.millis
            .store(millis, std::sync::atomic::Ordering::Relaxed);
    }
}

fn client_for(mock: &Arc<MockSink>) -> TelemetryClient {
    let mut config = TelemetryClientConfig::new("install-1");
    // Flush per event so assertions see every tracked event without an
    // explicit flush round-trip.
    config.batch_size = 1;
    config.flush_interval = Duration::from_mins(10);
    config.sinks = vec![mock.clone() as Arc<dyn eukhe_telemetry::TelemetrySink>];
    TelemetryClient::spawn(config).expect("spawn client")
}

struct Fixture {
    telemetry: SessionTelemetry,
    counters: Arc<SessionCounters>,
    clock: TestClock,
    mock: Arc<MockSink>,
}

/// Installed telemetry fed by scripted events — the same
/// `handle_event` call the host's consumption task uses.
fn fixture() -> Fixture {
    fixture_with_switch(None)
}

fn fixture_with_switch(telemetry_enabled: Option<RecordingSwitch>) -> Fixture {
    let mock = Arc::new(MockSink::new());
    let clock = TestClock::default();
    let now: Arc<dyn Fn() -> u64 + Send + Sync> = {
        let millis = clock.millis.clone();
        Arc::new(move || millis.load(std::sync::atomic::Ordering::Relaxed))
    };
    let counters = Arc::new(SessionCounters::default());
    let telemetry = install(
        &TelemetryWiring {
            client: client_for(&mock),
            execution_mode: Some("interactive".to_string()),
            now: Some(now),
            telemetry_enabled,
        },
        None,
        Arc::clone(&counters),
    );
    Fixture {
        telemetry,
        counters,
        clock,
        mock,
    }
}

fn emit(fixture: &Fixture, event: &AgentEvent) {
    fixture.telemetry.handle_event(event);
}

fn session_id(fixture: &Fixture) -> String {
    lock(&fixture.telemetry.state).session_id.clone()
}

/// The base properties every event carries (stripped before the
/// whole-object run comparisons).
const BASE_KEYS: [&str; 13] = [
    "version",
    "os_family",
    "architecture",
    "install_method",
    "execution_mode",
    "libc",
    "libc_version",
    "cpu_baseline",
    "os_release",
    "os_product_version",
    "build_channel",
    "workload_origin",
    "schema_revision",
];

fn assistant_message() -> AssistantMessage {
    AssistantMessage {
        content: vec![AssistantContentBlock::Text(TextContent {
            text: "private assistant text".to_string(),
            text_signature: None,
            cache_breakpoint: None,
        })],
        api: "test".to_string(),
        provider: "openai".to_string(),
        model: "gpt-test".to_string(),
        response_model: None,
        response_id: None,
        provider_thinking_level: None,
        thinking_level: None,
        diagnostics: None,
        usage: Usage {
            input: 100,
            output: 20,
            cache_read: 50,
            cache_write: 0,
            cache_write_1h: None,
            reasoning: None,
            total_tokens: 170,
            cost: UsageCost::default(),
        },
        stop_reason: StopReason::Stop,
        deferred: None,
        error_message: None,
        raw_stop_reason: None,
        end_turn: None,
        timestamp: 0,
        duration_ms: None,
    }
}

fn assistant_with_error(error: Option<&str>) -> AssistantMessage {
    let mut message = assistant_message();
    message.stop_reason = StopReason::Error;
    message.error_message = error.map(str::to_string);
    message
}

fn user_message() -> Message {
    Message::User(UserMessage {
        content: UserContent::Text("private prompt".to_string()),
        timestamp: 0,
    })
}

fn assistant_entry(message: &AssistantMessage) -> EntryRecord {
    EntryRecord {
        model: Some(vec![Message::Assistant(message.clone())]),
        data: None,
        edits: None,
        kind: "pi.message".to_string(),
        id: EntryId::from_number(1),
        conversation_id: ConversationId::from_number(1),
        head: None,
        by_task_id: None,
    }
}

fn tool_result_entry(tool_call_id: &str, tool_name: &str, is_error: bool) -> EntryRecord {
    EntryRecord {
        model: Some(vec![Message::ToolResult(ToolResultMessage {
            tool_call_id: tool_call_id.to_string(),
            tool_name: tool_name.to_string(),
            content: Vec::new(),
            details: None,
            usage: None,
            nested_calls: None,
            is_error,
            timestamp: 0,
            duration_ms: None,
        })]),
        data: None,
        edits: None,
        kind: "pi.toolResult".to_string(),
        id: EntryId::from_number(2),
        conversation_id: ConversationId::from_number(1),
        head: None,
        by_task_id: None,
    }
}

fn run_start() -> AgentEvent {
    AgentEvent::RunStart {
        inputs: vec![SubmissionId::from_number(1)],
    }
}

fn run_end() -> AgentEvent {
    AgentEvent::RunEnd {
        inputs: vec![SubmissionId::from_number(1)],
    }
}

fn user_start() -> AgentEvent {
    AgentEvent::MessageStart {
        message: user_message(),
    }
}

fn text_delta_update() -> AgentEvent {
    AgentEvent::MessageUpdate {
        usage: Usage::default(),
        changes: vec![MessageChange::TextDelta {
            content_index: 0,
            delta: "private streamed text".to_string(),
        }],
    }
}

fn thinking_delta_update() -> AgentEvent {
    AgentEvent::MessageUpdate {
        usage: Usage::default(),
        changes: vec![MessageChange::ThinkingDelta {
            content_index: 0,
            delta: "private reasoning".to_string(),
        }],
    }
}

fn message_end(message: &AssistantMessage) -> AgentEvent {
    AgentEvent::MessageEnd {
        entry: assistant_entry(message),
    }
}

/// One tool call: its start, then its end (a result entry reporting
/// `is_error`, or none for a faulted/orphaned task).
fn tool_events(tool: &str, is_error: Option<bool>) -> (AgentEvent, AgentEvent) {
    let call_id = format!("{tool}-1");
    (
        AgentEvent::ToolExecutionStart {
            call: ToolEventCall {
                tool_call_id: call_id.clone(),
                tool_name: tool.to_string(),
                task_id: None,
                parent_tool_call_id: None,
                parent_task_id: None,
            },
            args: json!({ "command": "private command" }).into(),
        },
        AgentEvent::ToolExecutionEnd {
            call: ToolEventCall {
                tool_call_id: call_id.clone(),
                tool_name: tool.to_string(),
                task_id: None,
                parent_tool_call_id: None,
                parent_task_id: None,
            },
            entry: is_error.map(|is_error| tool_result_entry(&call_id, tool, is_error)),
            result: None,
        },
    )
}

fn retry_start(at: f64, error_message: &str) -> AgentEvent {
    AgentEvent::AutoRetryStart {
        attempt: 1,
        at,
        error_message: error_message.to_string(),
    }
}

/// Wait for the telemetry worker to drain tracked events, then read.
async fn event_properties(mock: &MockSink, name: &str) -> Vec<serde_json::Map<String, Value>> {
    tokio::time::sleep(Duration::from_millis(10)).await;
    mock.events()
        .iter()
        .filter(|event| event.name == name)
        .map(|event| {
            serde_json::to_value(&event.properties)
                .expect("properties serialize")
                .as_object()
                .expect("properties are an object")
                .clone()
        })
        .collect()
}

/// The run's properties minus the base properties every event carries.
fn run_properties(properties: &serde_json::Map<String, Value>) -> serde_json::Map<String, Value> {
    properties
        .iter()
        .filter(|(key, _)| !BASE_KEYS.contains(&key.as_str()) && *key != "schema_version")
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect()
}

/// `agent started` (v2): the session id and the skill adoption counts.
#[tokio::test]
async fn agent_started_properties() {
    let mock = Arc::new(MockSink::new());
    let clock = TestClock::default();
    let now: Arc<dyn Fn() -> u64 + Send + Sync> = {
        let millis = clock.millis.clone();
        Arc::new(move || millis.load(std::sync::atomic::Ordering::Relaxed))
    };
    let telemetry = install(
        &TelemetryWiring {
            client: client_for(&mock),
            execution_mode: None,
            now: Some(now),
            telemetry_enabled: None,
        },
        Some(SkillCounts {
            skill_count: 2,
            python_skill_count: 1,
        }),
        Arc::new(SessionCounters::default()),
    );
    let started = event_properties(&mock, "agent started").await;
    assert_eq!(started.len(), 1);
    assert_eq!(started[0]["skill_count"], json!(2));
    assert_eq!(started[0]["python_skill_count"], json!(1));
    assert!(started[0]["session_id"]
        .as_str()
        .is_some_and(|id| !id.is_empty()));
    assert_eq!(started[0]["execution_mode"], json!(EXECUTION_MODE_UNKNOWN));
    drop(telemetry);
}

/// One run through the full durable event sequence, the WHOLE
/// `agent run completed` property object asserted, and no content leak.
#[tokio::test]
async fn one_full_run_emits_the_whole_completed_object() {
    let fixture = fixture();
    let assistant = assistant_message();

    fixture.clock.set(1_000);
    emit(&fixture, &run_start());
    emit(&fixture, &user_start());
    fixture.clock.set(1_010);
    emit(&fixture, &AgentEvent::TurnStart);
    fixture.clock.set(1_035);
    emit(&fixture, &text_delta_update());
    let (tool_start, tool_end) = tool_events("bash", Some(false));
    fixture.clock.set(1_050);
    emit(&fixture, &tool_start);
    fixture.clock.set(1_055);
    emit(&fixture, &tool_end);
    fixture.clock.set(1_100);
    emit(&fixture, &message_end(&assistant));
    fixture.clock.set(1_125);
    emit(&fixture, &run_end());
    // Deferred finalize: RunEnd alone must not seal the run yet (the
    // post-run compaction window stays open).
    assert!(event_properties(&fixture.mock, "agent run completed")
        .await
        .is_empty());

    // The next run start finalizes the open run.
    fixture.clock.set(1_200);
    emit(&fixture, &run_start());

    let runs = event_properties(&fixture.mock, "agent run completed").await;
    assert_eq!(runs.len(), 1);
    let run = run_properties(&runs[0]);
    let sid = session_id(&fixture);
    let mut expected = json!({
        "session_id": sid,
        "outcome": "success",
        "duration_ms": 125,
        "visible_ttft_ms": 25,
        "first_model_event_ms": 25,
        "model_latency_ms": 90,
        "max_model_latency_ms": 90,
        "model_call_count": 1,
        "turn_count": 1,
        "tool_call_count": 1,
        "tool_error_count": 0,
        "input_tokens": 100,
        "output_tokens": 20,
        "cache_read_tokens": 50,
        "cache_write_tokens": 0,
        "total_tokens": 170,
        "compaction_count": 0,
        "retry_count": 0,
        "failover_count": 0,
        "provider_category": "openai",
        "model_category": "gpt",
        "error_category": null,
        "run_index": 1,
        "trigger": "prompt",
        "stop_reason": "stop",
        "terminal_outcome": "success",
        "successful_model_call_count": 1,
        "usage_complete": true,
        "first_reasoning_ms": null,
        "run_to_first_text_ms": 35,
        "tool_duration_ms": 5,
        "retry_wait_ms": 0,
        "max_stream_gap_ms": null,
        "compaction_duration_ms": 0,
        "model_latency_p50_ms": 90,
        "model_error_count": 0,
        "tool_bash_call_count": 1,
        "tool_bash_error_count": 0,
        "tool_bash_duration_ms": 5,
        "tool_bash_max_duration_ms": 5,
    });
    // The run id is a fresh uuid: pin only its presence.
    let run_id = run
        .get("run_id")
        .and_then(Value::as_str)
        .unwrap_or_default();
    assert!(!run_id.is_empty());
    expected
        .as_object_mut()
        .unwrap()
        .insert("run_id".to_string(), json!(run_id));
    assert_eq!(run, *expected.as_object().unwrap());

    // Privacy: no private prompt/tool/assistant text anywhere.
    let all = serde_json::to_string(&fixture.mock.events()).unwrap();
    assert!(!all.contains("private"));

    // Session end finalizes the second (still open) run and the totals.
    fixture.clock.set(1_300);
    fixture.telemetry.end().await.unwrap();
    let ended = event_properties(&fixture.mock, "agent session ended").await;
    assert_eq!(ended.len(), 1);
    assert_eq!(ended[0]["duration_ms"], json!(1_300));
    assert_eq!(ended[0]["prompt_count"], json!(1));
    assert_eq!(ended[0]["run_count"], json!(2));
    assert_eq!(ended[0]["successful_run_count"], json!(2));
    assert_eq!(ended[0]["tool_call_count"], json!(1));
    assert_eq!(ended[0]["total_tokens"], json!(170));
    assert_eq!(ended[0]["terminal_outcome"], json!("success"));
}

/// An error run whose final assistant carries no error message keeps
/// the #2117 `error_subtype` through the `AutoRetryStart` error text.
#[tokio::test]
async fn error_subtype_falls_back_to_the_retry_error_text() {
    let fixture = fixture();
    emit(&fixture, &run_start());
    emit(&fixture, &user_start());
    fixture.clock.set(1_000);
    emit(&fixture, &AgentEvent::TurnStart);
    fixture.clock.set(1_100);
    emit(&fixture, &message_end(&assistant_with_error(None)));
    fixture.clock.set(1_200);
    emit(&fixture, &retry_start(1_700.0, "429 Too Many Requests"));
    emit(&fixture, &AgentEvent::AutoRetryEnd { attempt: 1 });
    fixture.clock.set(1_300);
    emit(&fixture, &run_end());
    fixture.clock.set(1_400);
    emit(&fixture, &run_start());

    let runs = event_properties(&fixture.mock, "agent run completed").await;
    assert_eq!(runs.len(), 1);
    assert_eq!(runs[0]["outcome"], json!("error"));
    assert_eq!(runs[0]["stop_reason"], json!("error"));
    assert_eq!(runs[0]["error_subtype"], json!("rate_limited"));
    assert_eq!(runs[0]["retry_count"], json!(1));
    assert_eq!(runs[0]["retry_wait_ms"], json!(500));
}

/// An aborted run maps onto the #2117 terminal `cancelled`.
#[tokio::test]
async fn aborted_outcome_maps_to_cancelled() {
    let fixture = fixture();
    let mut aborted = assistant_message();
    aborted.stop_reason = StopReason::Aborted;
    emit(&fixture, &run_start());
    emit(&fixture, &message_end(&aborted));
    emit(&fixture, &run_end());
    emit(&fixture, &run_start());

    let runs = event_properties(&fixture.mock, "agent run completed").await;
    assert_eq!(runs.len(), 1);
    assert_eq!(runs[0]["outcome"], json!("aborted"));
    assert_eq!(runs[0]["error_category"], Value::Null);
    assert_eq!(runs[0]["terminal_outcome"], json!("cancelled"));
    assert_eq!(runs[0]["stop_reason"], json!("aborted"));
}

/// Tool calls fold into the run: built-in tools by name, MCP and custom
/// tools only as aggregates, and no raw tool name rides any event.
/// `is_error` derives from the absent entry (a faulted task) or the
/// tool-result message's flag.
#[tokio::test]
async fn tool_calls_fold_into_run_aggregates() {
    let fixture = fixture();
    emit(&fixture, &run_start());
    emit(&fixture, &user_start());
    // (tool, entry-is-error / None = no entry, start, end)
    for (tool, is_error, start, end) in [
        ("bash", Some(false), 1_000, 1_040),
        ("bash", Some(true), 1_100, 1_110),
        ("edit", None, 1_200, 1_205),
        ("mcp__github__create_issue", Some(false), 1_300, 1_350),
        ("private-extension-tool", Some(false), 1_400, 1_401),
    ] {
        let (tool_start, tool_end) = tool_events(tool, is_error);
        fixture.clock.set(start);
        emit(&fixture, &tool_start);
        fixture.clock.set(end);
        emit(&fixture, &tool_end);
    }
    emit(&fixture, &message_end(&assistant_message()));
    emit(&fixture, &run_end());
    emit(&fixture, &run_start());
    let runs = event_properties(&fixture.mock, "agent run completed").await;
    let run = &runs[0];
    assert_eq!(run["tool_call_count"], json!(5));
    assert_eq!(run["tool_error_count"], json!(2));
    assert_eq!(run["tool_bash_call_count"], json!(2));
    assert_eq!(run["tool_bash_error_count"], json!(1));
    assert_eq!(run["tool_bash_duration_ms"], json!(50));
    assert_eq!(run["tool_bash_max_duration_ms"], json!(40));
    assert_eq!(run["tool_edit_call_count"], json!(1));
    // The faulted task (no entry) counts as the tool's error.
    assert_eq!(run["tool_edit_error_count"], json!(1));
    assert_eq!(run["mcp_tool_call_count"], json!(1));
    assert_eq!(run["custom_tool_call_count"], json!(1));
    assert!(
        run.get("tool_read_call_count").is_none(),
        "unused tools stay absent"
    );
    assert_eq!(
        fixture.mock.event_names(),
        ["agent started", "agent run completed"],
        "no per-call events"
    );
    let all = serde_json::to_string(&fixture.mock.events()).unwrap();
    assert!(!all.contains("github"));
    assert!(!all.contains("private-extension-tool"));
}

/// TS one-run-per-turn: durable retries stay inside one run; two
/// `AutoRetryStart`s count `retry_count` 2 and their scheduled waits sum
/// into `retry_wait_ms`, and the recovered attempt keeps the turn's
/// cost.
#[tokio::test]
async fn retries_stay_inside_one_run() {
    let fixture = fixture();
    let failed = assistant_with_error(Some(
        "API Error: 429 rate limit exceeded with /home/user/secret",
    ));
    emit(&fixture, &run_start());
    emit(&fixture, &user_start());
    fixture.clock.set(1_000);
    emit(&fixture, &AgentEvent::TurnStart);
    fixture.clock.set(1_100);
    emit(&fixture, &message_end(&failed));
    fixture.clock.set(1_200);
    emit(&fixture, &retry_start(1_700.0, "429 Too Many Requests"));
    emit(&fixture, &AgentEvent::AutoRetryEnd { attempt: 1 });
    fixture.clock.set(1_800);
    emit(&fixture, &message_end(&failed));
    fixture.clock.set(1_900);
    emit(
        &fixture,
        &AgentEvent::AutoRetryStart {
            attempt: 2,
            at: 2_900.0,
            error_message: "429 Too Many Requests".to_string(),
        },
    );
    emit(&fixture, &AgentEvent::AutoRetryEnd { attempt: 2 });
    let mut recovered = assistant_message();
    recovered.usage.cost.total = 0.012;
    fixture.clock.set(3_000);
    emit(&fixture, &message_end(&recovered));
    emit(&fixture, &run_end());
    fixture.telemetry.end().await.unwrap();

    let runs = event_properties(&fixture.mock, "agent run completed").await;
    assert_eq!(runs.len(), 1, "one run per turn");
    let run = &runs[0];
    assert_eq!(run["outcome"], json!("success"));
    assert_eq!(run["error_category"], Value::Null);
    assert_eq!(run["retry_count"], json!(2));
    assert_eq!(run["failover_count"], json!(0), "no failover facts yet");
    assert_eq!(run["retry_wait_ms"], json!(1_500));
    assert_eq!(run["model_call_count"], json!(3));
    assert_eq!(run["model_error_count"], json!(2));
    assert_eq!(run["error_rate_limit_count"], json!(2));
    assert_eq!(run["usage_complete"], json!(true));
    assert_eq!(run["estimated_cost_usd"], json!(0.012));
    let ended = event_properties(&fixture.mock, "agent session ended").await;
    assert_eq!(ended[0]["run_count"], json!(1));
    assert_eq!(ended[0]["successful_run_count"], json!(1));
    assert_eq!(ended[0]["failed_run_count"], json!(0));
    assert_eq!(ended[0]["retry_count"], json!(2));
    // The privacy contract: no raw provider text anywhere.
    let all = serde_json::to_string(&fixture.mock.events()).unwrap();
    assert!(!all.contains("API Error"));
    assert!(!all.contains("/home/user/secret"));
}

/// A compaction inside the run counts (once, at its end event) with the
/// duration measured between the two event observations; a compaction
/// with no active run counts nothing.
#[tokio::test]
async fn compactions_count_with_the_observed_duration() {
    let fixture = fixture();
    // Before any run: never counted.
    emit(
        &fixture,
        &AgentEvent::CompactionStart {
            task_id: TaskId::from_number(8),
            reason: CompactionReason::Manual,
            blocking: false,
        },
    );
    emit(
        &fixture,
        &AgentEvent::CompactionEnd {
            task_id: TaskId::from_number(8),
            reason: CompactionReason::Manual,
        },
    );
    emit(&fixture, &run_start());
    fixture.clock.set(1_000);
    emit(
        &fixture,
        &AgentEvent::CompactionStart {
            task_id: TaskId::from_number(7),
            reason: CompactionReason::Manual,
            blocking: true,
        },
    );
    fixture.clock.set(1_045);
    emit(
        &fixture,
        &AgentEvent::CompactionEnd {
            task_id: TaskId::from_number(7),
            reason: CompactionReason::Manual,
        },
    );
    emit(&fixture, &message_end(&assistant_message()));
    emit(&fixture, &run_end());
    emit(&fixture, &run_start());

    let runs = event_properties(&fixture.mock, "agent run completed").await;
    assert_eq!(runs.len(), 1);
    assert_eq!(runs[0]["compaction_count"], json!(1));
    assert_eq!(runs[0]["compaction_duration_ms"], json!(45));
    fixture.telemetry.end().await.unwrap();
    let ended = event_properties(&fixture.mock, "agent session ended").await;
    assert_eq!(ended[0]["compaction_count"], json!(1));
}

/// A continuation run (the retry re-entry: no user message inside the
/// window) reports the continuation trigger; a prompt run reports
/// prompt.
#[tokio::test]
async fn trigger_prompt_versus_continuation() {
    let fixture = fixture();
    emit(&fixture, &run_start());
    emit(&fixture, &AgentEvent::TurnStart);
    emit(&fixture, &message_end(&assistant_message()));
    emit(&fixture, &run_end());
    emit(&fixture, &run_start());
    emit(&fixture, &user_start());
    emit(&fixture, &AgentEvent::TurnStart);
    emit(&fixture, &message_end(&assistant_message()));
    emit(&fixture, &run_end());
    emit(&fixture, &run_start());

    let runs = event_properties(&fixture.mock, "agent run completed").await;
    assert_eq!(runs.len(), 2);
    assert_eq!(runs[0]["trigger"], json!("continuation"));
    assert_eq!(runs[1]["trigger"], json!("prompt"));
}

/// The stream timings from `MessageUpdate` changes: the visible TTFT and
/// run-to-first-text from a `TextDelta`, the first-reasoning from a
/// `ThinkingDelta`, and the largest quiet stretch between updates.
#[tokio::test]
async fn stream_timings_come_from_the_update_changes() {
    let fixture = fixture();
    let assistant = assistant_message();
    fixture.clock.set(1_000);
    emit(&fixture, &run_start());
    fixture.clock.set(1_010);
    emit(&fixture, &AgentEvent::TurnStart);
    fixture.clock.set(1_020);
    emit(&fixture, &thinking_delta_update());
    fixture.clock.set(1_030);
    emit(&fixture, &text_delta_update());
    fixture.clock.set(1_050);
    emit(&fixture, &text_delta_update());
    fixture.clock.set(1_200);
    emit(&fixture, &text_delta_update());
    emit(&fixture, &message_end(&assistant));
    emit(&fixture, &run_end());
    emit(&fixture, &run_start());

    let runs = event_properties(&fixture.mock, "agent run completed").await;
    assert_eq!(runs[0]["first_reasoning_ms"], json!(10));
    assert_eq!(runs[0]["visible_ttft_ms"], json!(20));
    assert_eq!(runs[0]["run_to_first_text_ms"], json!(30));
    assert_eq!(runs[0]["first_model_event_ms"], json!(10));
    assert_eq!(runs[0]["max_stream_gap_ms"], json!(150));
}

/// The run state machine stops recording while telemetry is off: runs
/// and tool calls in the off period never report, `end()` while off
/// severs an open run, and a later enable sends only what the on
/// period recorded.
#[tokio::test]
async fn off_period_run_facts_never_send() {
    let on = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let switch: Arc<dyn Fn() -> bool + Send + Sync> = {
        let on = Arc::clone(&on);
        Arc::new(move || on.load(std::sync::atomic::Ordering::Relaxed))
    };
    let fixture = fixture_with_switch(Some(RecordingSwitch::test(Arc::clone(&switch))));
    let assistant = assistant_message();

    // A whole run while off: start, a turn, a tool call, and its end.
    fixture.clock.set(1_000);
    emit(&fixture, &run_start());
    emit(&fixture, &AgentEvent::TurnStart);
    let (tool_start, tool_end) = tool_events("bash", Some(false));
    emit(&fixture, &tool_start);
    emit(&fixture, &tool_end);
    fixture.clock.set(1_100);
    emit(&fixture, &message_end(&assistant));
    emit(&fixture, &run_end());

    // On again: the next run records normally.
    on.store(true, std::sync::atomic::Ordering::Relaxed);
    fixture.clock.set(2_000);
    emit(&fixture, &run_start());
    fixture.clock.set(2_050);
    emit(&fixture, &AgentEvent::TurnStart);
    fixture.clock.set(2_100);
    emit(&fixture, &message_end(&assistant));
    fixture.clock.set(2_150);
    emit(&fixture, &run_end());

    // Off before the session ends: the second (open, ended) run severs
    // instead of reporting.
    on.store(false, std::sync::atomic::Ordering::Relaxed);
    fixture.clock.set(2_200);
    fixture.telemetry.end().await.unwrap();

    assert!(
        event_properties(&fixture.mock, "agent run completed")
            .await
            .is_empty(),
        "the run open across the opt-out never reports"
    );
    let ended = event_properties(&fixture.mock, "agent session ended").await;
    assert_eq!(ended.len(), 1);
    assert_eq!(ended[0]["run_count"], json!(0));
    assert_eq!(ended[0]["tool_call_count"], json!(0));
}

/// A run active when telemetry goes off is severed, not merged: the
/// next on-period run starts clean with only its own facts.
#[tokio::test]
async fn a_run_active_when_telemetry_turns_off_is_severed_not_merged() {
    let on = Arc::new(std::sync::atomic::AtomicBool::new(true));
    let switch: Arc<dyn Fn() -> bool + Send + Sync> = {
        let on = Arc::clone(&on);
        Arc::new(move || on.load(std::sync::atomic::Ordering::Relaxed))
    };
    let fixture = fixture_with_switch(Some(RecordingSwitch::test(switch)));
    let assistant = assistant_message();

    // Run 1 starts while on: one turn, one tool call in flight.
    fixture.clock.set(1_000);
    emit(&fixture, &run_start());
    fixture.clock.set(1_050);
    emit(&fixture, &AgentEvent::TurnStart);
    let (tool_start, _tool_end) = tool_events("bash", Some(false));
    emit(&fixture, &tool_start);
    fixture.clock.set(1_100);
    emit(&fixture, &message_end(&assistant));

    // Telemetry goes off: run 1's tool end, its end, and the next
    // run's start all happen in the off period.
    on.store(false, std::sync::atomic::Ordering::Relaxed);
    fixture.clock.set(1_200);
    let (_tool_start2, tool_end) = tool_events("bash", Some(false));
    emit(&fixture, &tool_end);
    emit(&fixture, &run_end());
    fixture.clock.set(1_300);
    emit(&fixture, &run_start());

    // Back on: the next run reports only its own window.
    on.store(true, std::sync::atomic::Ordering::Relaxed);
    fixture.clock.set(2_000);
    emit(&fixture, &run_start());
    fixture.clock.set(2_050);
    emit(&fixture, &AgentEvent::TurnStart);
    fixture.clock.set(2_100);
    emit(&fixture, &message_end(&assistant));
    fixture.clock.set(2_150);
    emit(&fixture, &run_end());

    fixture.clock.set(2_200);
    fixture.telemetry.end().await.unwrap();

    let runs = event_properties(&fixture.mock, "agent run completed").await;
    assert_eq!(runs.len(), 1, "only the on-period run reports");
    assert_eq!(runs[0]["turn_count"], json!(1));
    assert_eq!(
        runs[0]["duration_ms"],
        json!(150),
        "the severed run never merges: the duration stays in run 2's window"
    );
    let ended = event_properties(&fixture.mock, "agent session ended").await;
    assert_eq!(ended[0]["run_count"], json!(1));
    assert_eq!(
        ended[0]["tool_call_count"],
        json!(0),
        "the off-period tool end never counts"
    );
}

/// Skills, RLM child usage, MCP connector use, kernel boots, and
/// feature outcomes count into `agent session ended` instead of their
/// own events.
#[tokio::test]
async fn session_counters_ride_session_ended() {
    let fixture = fixture();
    fixture.telemetry.note_skill_used();
    fixture.telemetry.note_skill_used();
    fixture
        .telemetry
        .note_child_usage_attributed(50_208, 2_929, 0, 0, 0.008_995_7);
    fixture.counters.note_mcp_connector_use();
    fixture.counters.note_kernel_bootstrap(true, true, 1_200);
    fixture.counters.note_kernel_bootstrap(false, false, 300);
    fixture
        .telemetry
        .note_feature_outcome("goal", "completed", Some("create"));
    fixture
        .telemetry
        .note_feature_outcome("not-a-feature", "completed", None);
    fixture.clock.set(500);
    fixture.telemetry.end().await.unwrap();
    let ended = &event_properties(&fixture.mock, "agent session ended").await[0];
    assert_eq!(ended["duration_ms"], json!(500));
    assert_eq!(ended["skill_use_count"], json!(2));
    assert_eq!(ended["rlm_child_usage_count"], json!(1));
    assert_eq!(ended["rlm_child_input_tokens"], json!(50_208));
    assert_eq!(ended["rlm_child_output_tokens"], json!(2_929));
    assert!((ended["rlm_child_cost"].as_f64().unwrap() - 0.008_995_7).abs() < 1e-9);
    assert_eq!(ended["mcp_connector_use_count"], json!(1));
    assert_eq!(ended["kernel_bootstrap_count"], json!(2));
    assert_eq!(ended["kernel_bootstrap_cold_count"], json!(1));
    assert_eq!(ended["kernel_bootstrap_failed_count"], json!(1));
    assert_eq!(ended["kernel_bootstrap_max_ms"], json!(1_200));
    assert_eq!(ended["feature_goal_completed_count"], json!(1));
}

/// The TUI counters' rule: while telemetry is off nothing counts, so
/// turning it on later never sends what happened while it was off.
#[tokio::test]
async fn off_period_session_counters_never_count() {
    let on = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let switch: Arc<dyn Fn() -> bool + Send + Sync> = {
        let on = Arc::clone(&on);
        Arc::new(move || on.load(std::sync::atomic::Ordering::Relaxed))
    };
    let fixture = fixture_with_switch(Some(RecordingSwitch::test(Arc::clone(&switch))));
    fixture.counters.set_telemetry_enabled(switch);

    // Off: a skill use, a connector use, a kernel boot, a feature
    // outcome, and a child usage row all record nothing.
    fixture.telemetry.note_skill_used();
    fixture.counters.note_mcp_connector_use();
    fixture.counters.note_kernel_bootstrap(true, true, 1_200);
    fixture
        .telemetry
        .note_feature_outcome("goal", "completed", Some("create"));
    fixture
        .telemetry
        .note_child_usage_attributed(50_208, 2_929, 0, 0, 0.008_995_7);

    // On: the same seams record again.
    on.store(true, std::sync::atomic::Ordering::Relaxed);
    fixture.telemetry.note_skill_used();
    fixture.telemetry.note_skill_used();

    fixture.telemetry.end().await.unwrap();
    let ended = &event_properties(&fixture.mock, "agent session ended").await[0];
    assert_eq!(ended["skill_use_count"], json!(2));
    assert_eq!(
        ended["mcp_connector_use_count"],
        json!(0),
        "the off-period connector use never counted"
    );
    assert_eq!(ended["kernel_bootstrap_count"], json!(0));
    assert_eq!(ended["rlm_child_usage_count"], json!(0));
    let feature_keys: Vec<_> = ended
        .keys()
        .filter(|key| key.starts_with("feature_"))
        .collect();
    assert!(
        feature_keys.is_empty(),
        "the off-period feature outcome never counted"
    );
}

/// `session archived` (schema v1): the archive path emits its own
/// event, then `end()` the ended event exactly once.
#[tokio::test]
async fn session_archived_emits_before_the_end() {
    let fixture = fixture();
    fixture.clock.set(1_000);
    fixture.telemetry.note_archived();
    fixture.clock.set(1_400);
    fixture.telemetry.end().await.unwrap();
    // end() twice: only one ended event.
    fixture.telemetry.end().await.unwrap();
    assert_eq!(
        fixture.mock.event_names(),
        ["agent started", "session archived", "agent session ended"]
    );
    let archived = &event_properties(&fixture.mock, "session archived").await[0];
    // The clock starts at 0 at install; the archive lands at 1_000.
    assert_eq!(archived["duration_ms"], json!(1_000));
    let ended = &event_properties(&fixture.mock, "agent session ended").await;
    assert_eq!(ended.len(), 1);
}

/// The model-latency p50: the median of the run's call latencies (the
/// lower middle for an even count).
#[tokio::test]
async fn median_model_latencies_odd_and_even() {
    let fixture = fixture();
    // Run 1: three calls of 10, 90, 100 → p50 90.
    emit(&fixture, &run_start());
    for latency in [10, 90, 100] {
        fixture.clock.set(1_000);
        emit(&fixture, &AgentEvent::TurnStart);
        fixture.clock.set(1_000 + latency);
        emit(&fixture, &message_end(&assistant_message()));
    }
    emit(&fixture, &run_end());
    // Run 2: two calls of 100, 10 → p50 10 (the lower middle).
    emit(&fixture, &run_start());
    for latency in [100, 10] {
        fixture.clock.set(2_000);
        emit(&fixture, &AgentEvent::TurnStart);
        fixture.clock.set(2_000 + latency);
        emit(&fixture, &message_end(&assistant_message()));
    }
    emit(&fixture, &run_end());
    emit(&fixture, &run_start());

    let runs = event_properties(&fixture.mock, "agent run completed").await;
    assert_eq!(runs.len(), 2);
    assert_eq!(runs[0]["model_latency_p50_ms"], json!(90));
    assert_eq!(runs[1]["model_latency_p50_ms"], json!(10));
}

/// A generation `TaskFailed` counts a model error into the active run
/// (with its error-category count); other task kinds report through
/// their own tool events.
#[tokio::test]
async fn generation_task_failures_count_model_errors() {
    let fixture = fixture();
    emit(&fixture, &run_start());
    emit(&fixture, &user_start());
    emit(
        &fixture,
        &AgentEvent::TaskFailed {
            task_id: TaskId::from_number(5),
            kind: "pi.generation".to_string(),
            message: "429 Too Many Requests".to_string(),
        },
    );
    emit(
        &fixture,
        &AgentEvent::TaskFailed {
            task_id: TaskId::from_number(6),
            kind: "pi.tool".to_string(),
            message: "tool blew up".to_string(),
        },
    );
    emit(&fixture, &run_end());
    emit(&fixture, &run_start());

    let runs = event_properties(&fixture.mock, "agent run completed").await;
    assert_eq!(runs.len(), 1);
    assert_eq!(runs[0]["model_error_count"], json!(1));
    assert_eq!(runs[0]["error_rate_limit_count"], json!(1));
    // The recorded text feeds error_subtype when the final assistant
    // has none: this run never got an assistant message at all, so the
    // outcome is the no-assistant error.
    assert_eq!(runs[0]["outcome"], json!("error"));
    assert_eq!(runs[0]["error_subtype"], json!("rate_limited"));
}

/// The snapshot event (and the other no-fact events) are no-ops that
/// still respect the recording gate.
#[tokio::test]
async fn snapshot_is_a_no_op() {
    let fixture = fixture();
    emit(
        &fixture,
        &AgentEvent::Snapshot(SnapshotEvent {
            entries: Vec::new(),
            run: None,
            generation: None,
            tools: Vec::new(),
            nested_tools: Vec::new(),
            compactions: Vec::new(),
            inbox: Vec::new(),
            agent: AgentState::default(),
            usage: UsageState::default(),
        }),
    );
    emit(&fixture, &AgentEvent::TurnEnd);
    emit(&fixture, &AgentEvent::DeferredPoll { poll_at: 1.0 });
    assert_eq!(fixture.mock.event_names(), Vec::<String>::new());
    // And the state machine still works afterwards.
    emit(&fixture, &run_start());
    emit(&fixture, &message_end(&assistant_message()));
    emit(&fixture, &run_end());
    emit(&fixture, &run_start());
    assert_eq!(
        event_properties(&fixture.mock, "agent run completed")
            .await
            .len(),
        1
    );
}

/// One child-usage attribution entry appended in the conversation feeds
/// the `rlm_child_*` counters on `agent session ended` (the durable
/// replacement of the old daemon-side producer feed); a torn row counts
/// nothing.
#[tokio::test]
async fn child_usage_attribution_entries_feed_the_counters() {
    use super::super::rlm_usage::{ChildUsageAttributionData, CHILD_USAGE_ATTRIBUTED_KIND};

    let fixture = fixture();
    let attribution = ChildUsageAttributionData {
        target_id: EntryId::from_number(10),
        child_usage: Usage {
            input: 50_208,
            output: 2_929,
            cache_read: 0,
            cache_write: 0,
            cache_write_1h: None,
            reasoning: None,
            total_tokens: 53_137,
            cost: UsageCost {
                total: 0.008_995_7,
                ..UsageCost::default()
            },
        },
        aggregate_usage: Usage::default(),
        origin: None,
    };
    emit(
        &fixture,
        &AgentEvent::EntryAppended {
            entry: EntryRecord {
                model: None,
                data: Some(eukhe_chord::json::to_json(&attribution).unwrap()),
                edits: None,
                kind: CHILD_USAGE_ATTRIBUTED_KIND.to_string(),
                id: EntryId::from_number(11),
                conversation_id: ConversationId::from_number(1),
                head: None,
                by_task_id: None,
            },
        },
    );
    // A torn row counts nothing.
    emit(
        &fixture,
        &AgentEvent::EntryAppended {
            entry: EntryRecord {
                model: None,
                data: Some(eukhe_chord::json::to_json("torn").unwrap()),
                edits: None,
                kind: CHILD_USAGE_ATTRIBUTED_KIND.to_string(),
                id: EntryId::from_number(12),
                conversation_id: ConversationId::from_number(1),
                head: None,
                by_task_id: None,
            },
        },
    );
    fixture.telemetry.end().await.unwrap();
    let ended = &event_properties(&fixture.mock, "agent session ended").await[0];
    assert_eq!(ended["rlm_child_usage_count"], json!(1));
    assert_eq!(ended["rlm_child_input_tokens"], json!(50_208));
    assert_eq!(ended["rlm_child_output_tokens"], json!(2_929));
    assert!((ended["rlm_child_cost"].as_f64().unwrap() - 0.008_995_7).abs() < 1e-9);
}

/// `observe_batch` feeds one commit's events in order — the same
/// per-event state machine.
#[tokio::test]
async fn observe_batch_feeds_events_in_order() {
    let fixture = fixture();
    let assistant = assistant_message();
    fixture.telemetry.observe_batch(&[
        run_start(),
        user_start(),
        AgentEvent::TurnStart,
        message_end(&assistant),
        run_end(),
    ]);
    fixture.telemetry.end().await.unwrap();
    let runs = event_properties(&fixture.mock, "agent run completed").await;
    assert_eq!(runs.len(), 1);
    assert_eq!(runs[0]["trigger"], json!("prompt"));
}
