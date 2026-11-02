//! The incident classifier of eukhe-types run with the compiled core's
//! shapes ([`super::INCIDENT_RULES`]): its classification tests (the TS
//! `incident.test.ts` unit-level checks) and the per-daemon log line
//! parse, moved here because eukhe-types cannot call the core.

use super::INCIDENT_RULES;
use eukhe_types::incident::{
    collect_incident_events, collect_worker_pid_map, compute_incident_anomalies,
    parse_incident_daemon_log_line, parse_incident_log_line, worker_id_from_socket_path,
    IncidentEvent, IncidentLogEntry, IncidentSeverity, WorkerPidMap,
};

fn events_of(entries: &[IncidentLogEntry], pids: &WorkerPidMap) -> Vec<IncidentEvent> {
    collect_incident_events(INCIDENT_RULES, entries, pids)
}

fn pids_of(entries: &[IncidentLogEntry]) -> WorkerPidMap {
    collect_worker_pid_map(INCIDENT_RULES, entries)
}

fn log_line(fields: &[(&str, serde_json::Value)]) -> IncidentLogEntry {
    let mut record = serde_json::Map::new();
    record.insert(
        "ts".to_string(),
        serde_json::Value::String("2026-09-10T20:00:00.000Z".to_string()),
    );
    record.insert(
        "level".to_string(),
        serde_json::Value::String("warn".to_string()),
    );
    for (key, value) in fields {
        record.insert((*key).to_string(), value.clone());
    }
    parse_incident_log_line(&serde_json::Value::Object(record).to_string())
        .expect("the fixture line parses")
}

fn supervisor_line(ts: &str, msg: &str, extra: &[(&str, serde_json::Value)]) -> IncidentLogEntry {
    let mut fields: Vec<(&str, serde_json::Value)> = vec![
        ("ts", serde_json::json!(ts)),
        (
            "component",
            serde_json::json!("coding-agent.daemon-supervisor"),
        ),
        ("msg", serde_json::json!(msg)),
        ("pid", serde_json::json!(15026)),
    ];
    for (key, value) in extra {
        fields.push((key, value.clone()));
    }
    log_line(&fields)
}

fn worker_start_line(ts: &str, socket_path: &str, pid: i64) -> IncidentLogEntry {
    log_line(&[
        ("ts", serde_json::json!(ts)),
        ("component", serde_json::json!("coding-agent.daemon")),
        ("socketPath", serde_json::json!(socket_path)),
        ("pid", serde_json::json!(pid)),
        (
            "msg",
            serde_json::json!(format!("Eukhe daemon listening on {socket_path}")),
        ),
    ])
}

fn provider_failure_line(ts: &str, pid: i64) -> IncidentLogEntry {
    log_line(&[
        ("ts", serde_json::json!(ts)),
        ("level", serde_json::json!("error")),
        ("component", serde_json::json!("ai.provider")),
        ("pid", serde_json::json!(pid)),
        ("msg", serde_json::json!("provider stream failure")),
        ("kind", serde_json::json!("rate_limit")),
        ("status", serde_json::json!(429)),
    ])
}

#[test]
fn attributes_provider_failures_to_the_pid_owner() {
    let entries = vec![
        worker_start_line(
            "2026-09-10T19:42:09.064Z",
            "/tmp/eukhe-501/worker-98ed5cb228d2-5b1d3aeb91ee.sock",
            53615,
        ),
        provider_failure_line("2026-09-10T20:02:53.374Z", 53615),
    ];
    let events = events_of(&entries, &pids_of(&entries));
    assert!(events
        .iter()
        .any(|event| event.summary.contains("for worker 5b1d3aeb91ee")));
}

#[test]
fn attributes_provider_failures_to_the_worker_owning_the_pid_at_that_time() {
    let worker_a = "/tmp/eukhe-501/worker-98ed5cb228d2-aaaaaaaaaaaa.sock";
    let worker_b = "/tmp/eukhe-501/worker-98ed5cb228d2-bbbbbbbbbbbb.sock";
    let entries = vec![
        worker_start_line("2026-09-10T20:00:00.000Z", worker_a, 53615),
        provider_failure_line("2026-09-10T20:01:00.000Z", 53615),
        // The same pid is reused by a replacement worker an hour later.
        worker_start_line("2026-09-10T21:00:00.000Z", worker_b, 53615),
        provider_failure_line("2026-09-10T21:01:00.000Z", 53615),
    ];
    let events = events_of(&entries, &pids_of(&entries));
    let summaries: Vec<&str> = events
        .iter()
        .filter(|event| event.event_class == "provider")
        .map(|event| event.summary.as_str())
        .collect();
    assert_eq!(
        summaries,
        vec![
            "provider stream failure (rate_limit 429) for worker aaaaaaaaaaaa",
            "provider stream failure (rate_limit 429) for worker bbbbbbbbbbbb",
        ]
    );
}

#[test]
fn a_later_sighting_never_owns_an_earlier_failure() {
    let worker_b = "/tmp/eukhe-501/worker-98ed5cb228d2-bbbbbbbbbbbb.sock";
    let entries = vec![
        provider_failure_line("2026-09-10T10:00:00.000Z", 53615),
        // The pid's only sighting is a worker that starts ten minutes
        // later; a future sighting is never evidence of ownership at
        // 10:00.
        worker_start_line("2026-09-10T10:10:00.000Z", worker_b, 53615),
    ];
    let events = events_of(&entries, &pids_of(&entries));
    let summaries: Vec<&str> = events
        .iter()
        .filter(|event| event.event_class == "provider")
        .map(|event| event.summary.as_str())
        .collect();
    assert_eq!(
        summaries,
        vec!["provider stream failure (rate_limit 429) for pid 53615"]
    );
}

#[test]
fn worker_ids_parse_from_unix_socket_paths() {
    assert_eq!(
        worker_id_from_socket_path(
            INCIDENT_RULES,
            Some("/tmp/eukhe-501/worker-98ed5cb228d2-5b1d3aeb91ee.sock")
        ),
        Some("5b1d3aeb91ee".to_string())
    );
    assert_eq!(
        worker_id_from_socket_path(INCIDENT_RULES, Some("/tmp/eukhe-501/daemon.sock")),
        None
    );
    assert_eq!(worker_id_from_socket_path(INCIDENT_RULES, None), None);
}

#[test]
fn a_same_component_restart_within_two_seconds_is_a_real_event() {
    let socket_path = "/tmp/eukhe-501/worker-98ed5cb228d2-5b1d3aeb91ee.sock";
    let entries = vec![
        worker_start_line("2026-09-10T20:00:00.000Z", socket_path, 100),
        worker_start_line("2026-09-10T20:00:01.000Z", socket_path, 200),
    ];
    let events = events_of(&entries, &pids_of(&entries));
    assert_eq!(events.len(), 2);
    // The cross-component duplicate drops instead: the same crash is
    // logged by the worker and forwarded over stderr.
    let crashed = vec![
        log_line(&[
            ("ts", serde_json::json!("2026-09-10T20:23:24.945Z")),
            ("component", serde_json::json!("coding-agent.daemon")),
            ("socketPath", serde_json::json!(socket_path)),
            ("pid", serde_json::json!(53615)),
            (
                "msg",
                serde_json::json!("uncaught exception: Error: write EPIPE"),
            ),
        ]),
        supervisor_line(
            "2026-09-10T20:23:24.945Z",
            "Session worker 5b1d3aeb91ee stderr: uncaught exception: Error: write EPIPE",
            &[],
        ),
    ];
    let events = events_of(&crashed, &pids_of(&crashed));
    assert_eq!(events.len(), 1);
    assert_eq!(events[0].event_class, "worker-crash");
    assert_eq!(events[0].severity, IncidentSeverity::Critical);
}

#[test]
fn unknown_worker_diagnostics_key_on_the_worker_not_the_socket() {
    let socket_path = "/tmp/eukhe-501/worker-98ed5cb228d2-aaaaaaaaaaaa.sock";
    let entries: Vec<IncidentLogEntry> = (1..=3)
        .map(|index| {
            log_line(&[
                (
                    "ts",
                    serde_json::json!(format!("2026-09-10T20:0{index}:00.000Z")),
                ),
                ("component", serde_json::json!("coding-agent.daemon")),
                ("socketPath", serde_json::json!(socket_path)),
                ("pid", serde_json::json!(53615)),
                (
                    "msg",
                    serde_json::json!(format!("unrecognized worker diagnostic {index}")),
                ),
            ])
        })
        .collect();
    let events = events_of(&entries, &pids_of(&entries));
    assert!(events
        .iter()
        .all(|event| event.subject == "worker aaaaaaaaaaaa"));
    let anomalies = compute_incident_anomalies(&events);
    assert!(anomalies.iter().any(|anomaly| anomaly
        .summary
        .starts_with("worker aaaaaaaaaaaa: 3 warnings/errors over 2m")));
    assert!(anomalies
        .iter()
        .all(|anomaly: &IncidentEvent| !anomaly.summary.contains(socket_path)));
}

#[test]
fn command_failures_classify_by_their_error_body() {
    let entry = |msg: &str| supervisor_line("2026-09-10T20:02:39.764Z", msg, &[]);
    let cases = [
            (
                "Supervisor command attach failed: Error: Timed out waiting for daemon worker response to attach",
                "timeout",
                IncidentSeverity::Error,
                "command attach failed: timed out waiting for worker response",
            ),
            (
                "Supervisor command list_agent_peers failed: Error: Worker authentication failed",
                "auth",
                IncidentSeverity::Error,
                "command list_agent_peers failed: worker authentication failed",
            ),
            (
                "Supervisor command send_message failed: Error: Session worker is starting",
                "command-failure",
                IncidentSeverity::Warn,
                "command send_message failed: session worker is starting",
            ),
            (
                "Supervisor command send_message failed: Error: Session worker is recovering",
                "command-failure",
                IncidentSeverity::Warn,
                "command send_message failed: session worker is recovering",
            ),
            (
                "Supervisor command send_message failed: Error: Unknown active session: aabbccddeeff",
                "command-failure",
                IncidentSeverity::Warn,
                "command send_message failed: unknown active session aabbccddeeff",
            ),
        ];
    for (msg, event_class, severity, summary) in cases {
        let events = events_of(&[entry(msg)], &WorkerPidMap::default());
        assert_eq!(events.len(), 1, "{msg}");
        assert_eq!(events[0].event_class, event_class, "{msg}");
        assert_eq!(events[0].severity, severity, "{msg}");
        assert_eq!(events[0].summary, summary, "{msg}");
    }
    // Quoted session names ride along as tokens.
    let events = events_of(
        &[entry(
            r#"Supervisor command set_session_name failed: Error: Agent name "Faerie" is unavailable"#,
        )],
        &WorkerPidMap::default(),
    );
    assert_eq!(events[0].tokens, vec!["Faerie".to_string()]);
}

#[test]
fn recovery_breakdown_ranks_and_caps_the_operations() {
    // The motivating incident's held backlog: 533 uncertain operations
    // across four kinds (TS `incident.test.ts`'s fixture).
    let operations = std::iter::repeat_n("tool_execution_start", 408)
        .chain(std::iter::repeat_n("auto_retry_end", 62))
        .chain(std::iter::repeat_n("agent_end", 47))
        .chain(std::iter::repeat_n("message_start", 16))
        .collect::<Vec<_>>()
        .join(", ");
    let entry = supervisor_line(
        "2026-09-10T20:23:29.521Z",
        &format!(
            "Recovered worker 5b1d3aeb91ee without replaying uncertain operations: {operations}"
        ),
        &[],
    );
    let events = events_of(&[entry], &WorkerPidMap::default());
    assert_eq!(
            events[0].summary,
            "worker 5b1d3aeb91ee recovered; 533 uncertain operations not replayed (tool_execution_start x408, auto_retry_end x62, agent_end x47, message_start x16)"
        );
    // The cap kicks in past the fourth kind.
    let five_kinds = supervisor_line(
        "2026-09-10T20:23:29.521Z",
        "Recovered worker 5b1d3aeb91ee without replaying uncertain operations: b, b, a, c, d, e",
        &[],
    );
    let events = events_of(&[five_kinds], &WorkerPidMap::default());
    assert_eq!(
            events[0].summary,
            "worker 5b1d3aeb91ee recovered; 6 uncertain operations not replayed (b x2, a x1, c x1, d x1, +1 more)"
        );
}

#[test]
fn passivation_tokens_skip_the_empty_name() {
    let entry = supervisor_line(
        "2026-09-10T20:05:00.000Z",
        r#"Session worker 5b1d3aeb91ee stderr: Passivated idle child sessionId=feedface1234 name="" idleMinutes=5"#,
        &[],
    );
    let events = events_of(&[entry], &WorkerPidMap::default());
    assert_eq!(
        events[0].tokens,
        vec!["5b1d3aeb91ee".to_string(), "feedface1234".to_string()]
    );
    assert_eq!(
        events[0].summary,
        "passivated idle child session feedface1234 (idle 5m)"
    );
    let named = supervisor_line(
        "2026-09-10T20:05:00.000Z",
        r#"Session worker 5b1d3aeb91ee stderr: Passivated idle child sessionId=feedface1234 name="Faerie" idleMinutes=5"#,
        &[],
    );
    let events = events_of(&[named], &WorkerPidMap::default());
    assert_eq!(
        events[0].tokens,
        vec![
            "5b1d3aeb91ee".to_string(),
            "feedface1234".to_string(),
            "Faerie".to_string()
        ]
    );
}

#[test]
fn stack_frame_lines_belong_to_the_previous_event() {
    let entries = vec![
            supervisor_line(
                "2026-09-10T20:23:24.945Z",
                "Session worker 5b1d3aeb91ee stderr: uncaught exception: Error: write EPIPE",
                &[],
            ),
            supervisor_line(
                "2026-09-10T20:23:24.946Z",
                "Session worker 5b1d3aeb91ee stderr:     at afterWriteDispatched (node:internal/stream_base_commons:159:15)",
                &[],
            ),
        ];
    let events = events_of(&entries, &WorkerPidMap::default());
    assert_eq!(events.len(), 1);
}

#[test]
fn daemon_log_line_parses_supervisor_and_worker_lines() {
    let supervisor = parse_incident_daemon_log_line(
        INCIDENT_RULES,
        "[2026-09-10T20:02:39.765Z] supervisor: Supervisor command attach failed: Error: Timed out waiting for daemon worker response to attach",
    )
    .expect("supervisor line");
    assert_eq!(supervisor.component, "coding-agent.daemon-supervisor");
    assert_eq!(
        supervisor.msg,
        "Supervisor command attach failed: Error: Timed out waiting for daemon worker response to attach"
    );
    assert_eq!(supervisor.time_ms, 1_789_070_559_765);
    assert_eq!(supervisor.level, "warn");
    assert_eq!(supervisor.pid, None);

    let worker = parse_incident_daemon_log_line(
        INCIDENT_RULES,
        "[2026-09-10T20:23:24.945Z] uncaught exception: Error: write EPIPE",
    )
    .expect("worker line");
    assert_eq!(worker.component, "coding-agent.daemon");
    assert_eq!(worker.msg, "uncaught exception: Error: write EPIPE");
}

#[test]
fn daemon_log_line_skips_malformed_lines() {
    let parse = |line| parse_incident_daemon_log_line(INCIDENT_RULES, line);
    assert!(parse("not a log line").is_none());
    assert!(parse("[not-a-timestamp] supervisor: msg").is_none());
    assert!(parse("[]").is_none());
    assert!(parse("[2026-09-10T20:00:00Z]   ").is_none());
    assert!(parse("[2026-09-10T20:00:00Z] supervisor:").is_none());
}
