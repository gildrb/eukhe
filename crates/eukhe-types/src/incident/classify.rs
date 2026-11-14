//! Log-entry classification into incident events (TS
//! `classifyIncidentEntry` and its helpers).

use super::rules::{IncidentRules, IncidentShape};
use super::{
    error_message, first_line, lifecycle_classes, truncate_text, IncidentCategory, IncidentEvent,
    IncidentLogEntry, IncidentSeverity, RECOVERY_BREAKDOWN_LIMIT, SUMMARY_TRUNCATION,
};
use std::collections::HashMap;

/// The shapes a worker stderr body's first line is asked, in order.
const BODY_SHAPES: [IncidentShape; 6] = [
    IncidentShape::WorkerListening,
    IncidentShape::CrashLine,
    IncidentShape::ShutdownExit,
    IncidentShape::SignalShutdown,
    IncidentShape::StopRequested,
    IncidentShape::Passivated,
];

/// The shapes a log message's first line is asked, in order.
const LINE_SHAPES: [IncidentShape; 18] = [
    IncidentShape::SupervisorListening,
    IncidentShape::StartupFailed,
    IncidentShape::SupervisorCommand,
    IncidentShape::DaemonCommand,
    IncidentShape::CatchUp,
    IncidentShape::HeartbeatsList,
    IncidentShape::Recovered,
    IncidentShape::RecoveredPlain,
    IncidentShape::AdoptFailed,
    IncidentShape::RecoverFailed,
    IncidentShape::FailedAfterRetries,
    IncidentShape::Unresponsive,
    IncidentShape::Reclaimed,
    IncidentShape::Migrated,
    IncidentShape::Replacement,
    IncidentShape::Woke,
    IncidentShape::EvictedIdle,
    IncidentShape::EvictedEmpty,
];

/// The first of `shapes` that fits `text` (one core call): the shape and
/// its captures (numbered from 1).
fn first_shape(
    rules: IncidentRules,
    text: &str,
    shapes: &[IncidentShape],
) -> Option<(IncidentShape, Captures)> {
    let fit = (rules.first)(text, shapes)?;
    let shape = *shapes.get(fit.index)?;
    Some((shape, Captures(fit.captures)))
}

/// The texts of a fit's captures.
struct Captures(Vec<Option<String>>);

impl Captures {
    /// Capture `k` (from 1), or the empty text when it took no part.
    fn get(&self, k: usize) -> &str {
        k.checked_sub(1)
            .and_then(|i| self.0.get(i))
            .and_then(Option::as_deref)
            .unwrap_or("")
    }

    /// Capture `k` (from 1), if it read something.
    fn opt(&self, k: usize) -> Option<&str> {
        self.0.get(k.checked_sub(1)?)?.as_deref()
    }
}

/// The worker id a socket path names, if any (TS
/// `workerIdFromSocketPath`): the last `/` segment of the path.
#[must_use]
pub fn worker_id_from_socket_path(
    rules: IncidentRules,
    socket_path: Option<&str>,
) -> Option<String> {
    let socket_path = socket_path?;
    let name = socket_path.rsplit('/').next().unwrap_or(socket_path);
    let (_, captures) = first_shape(rules, name, &[IncidentShape::WorkerSocket])?;
    captures.opt(1).map(str::to_string)
}

/// One log sighting of a worker id owning a pid at a timestamp (TS
/// `WorkerPidSighting`).
#[derive(Debug, Clone, PartialEq)]
pub struct WorkerPidSighting {
    pub time_ms: i64,
    pub worker_id: String,
}

/// pid -> worker-id sightings, ordered by time (TS `WorkerPidMap`). A pid
/// can be reused by a later worker, so attribution picks the owner at
/// the event time, not the union of every id ever seen on the pid.
pub type WorkerPidMap = HashMap<i64, Vec<WorkerPidSighting>>;

/// Map pid -> worker-id sightings from entries whose socket path names a
/// worker socket (TS `collectWorkerPidMap`).
#[must_use]
pub fn collect_worker_pid_map(rules: IncidentRules, entries: &[IncidentLogEntry]) -> WorkerPidMap {
    let mut map: WorkerPidMap = WorkerPidMap::new();
    for entry in entries {
        let Some(worker_id) = worker_id_from_socket_path(rules, entry.socket_path.as_deref())
        else {
            continue;
        };
        let Some(pid) = entry.pid else {
            continue;
        };
        map.entry(pid).or_default().push(WorkerPidSighting {
            time_ms: entry.time_ms,
            worker_id,
        });
    }
    for sightings in map.values_mut() {
        sightings.sort_by_key(|sighting| sighting.time_ms);
    }
    map
}

/// The worker that owned `pid` at `time_ms`: the latest sighting at or
/// before it (TS `workerIdForPid`).
fn worker_id_for_pid(worker_pids: &WorkerPidMap, pid: Option<i64>, time_ms: i64) -> Option<String> {
    let pid = pid?;
    let sightings = worker_pids.get(&pid)?;
    let mut worker_id: Option<&WorkerPidSighting> = None;
    for sighting in sightings {
        if sighting.time_ms <= time_ms {
            worker_id = Some(sighting);
        } else {
            break;
        }
    }
    worker_id.map(|sighting| sighting.worker_id.clone())
}

/// One classified worker stderr body (TS `classifyWorkerStderrBody`'s
/// return shape: an event without time or category).
#[derive(Debug, Clone, PartialEq)]
struct WorkerStderrEvent {
    severity: IncidentSeverity,
    event_class: &'static str,
    subject: String,
    summary: String,
    tokens: Vec<String>,
}

impl WorkerStderrEvent {
    /// The supervisor event of this body, at the entry's time.
    fn into_event(self, entry: &IncidentLogEntry) -> IncidentEvent {
        incident_event(
            entry,
            self.severity,
            IncidentCategory::Supervisor,
            self.event_class,
            self.subject,
            self.summary,
            self.tokens,
        )
    }
}

/// Build an event from an entry (TS `event`).
fn event(
    entry: &IncidentLogEntry,
    severity: IncidentSeverity,
    category: IncidentCategory,
    event_class: &str,
    subject: impl Into<String>,
    summary: impl Into<String>,
) -> IncidentEvent {
    incident_event(
        entry,
        severity,
        category,
        event_class,
        subject,
        summary,
        Vec::new(),
    )
}

/// Build an event from an entry with filter tokens.
fn incident_event(
    entry: &IncidentLogEntry,
    severity: IncidentSeverity,
    category: IncidentCategory,
    event_class: &str,
    subject: impl Into<String>,
    summary: impl Into<String>,
    tokens: Vec<String>,
) -> IncidentEvent {
    IncidentEvent {
        time_ms: entry.time_ms,
        severity,
        category,
        event_class: event_class.to_string(),
        subject: subject.into(),
        summary: summary.into(),
        tokens,
    }
}

/// Build an event about `worker`, its one filter token.
fn worker_event(
    entry: &IncidentLogEntry,
    severity: IncidentSeverity,
    category: IncidentCategory,
    event_class: &str,
    worker: &str,
    summary: impl Into<String>,
) -> IncidentEvent {
    incident_event(
        entry,
        severity,
        category,
        event_class,
        format!("worker {worker}"),
        summary,
        vec![worker.to_string()],
    )
}

/// Key events on the entry's socket path so anomalies and aggregation
/// never mix entries from different daemons sharing one agent.jsonl;
/// entries without a socket field (the per-daemon fallback log) key on
/// `daemon` (TS `daemonSubject`).
fn daemon_subject(entry: &IncidentLogEntry) -> String {
    entry
        .socket_path
        .clone()
        .unwrap_or_else(|| "daemon".to_string())
}

/// The error a failed command reports when its worker never answered.
const WORKER_TIMEOUT: &str = "Timed out waiting for daemon worker response";

/// A failure that timed out waiting for a worker is an error `timeout`;
/// any other is a warning `command-failure`.
fn failure_class(err: &str) -> (IncidentSeverity, &'static str) {
    if err.contains(WORKER_TIMEOUT) {
        (IncidentSeverity::Error, "timeout")
    } else {
        (IncidentSeverity::Warn, "command-failure")
    }
}

/// The first line of an error, without its `Error:` prefix, shortened for
/// a summary.
fn error_summary(err: &str) -> String {
    truncate_text(error_message(first_line(err)), 100)
}

/// The classification of a command failure (TS
/// `classifyCommandFailure`'s return shape).
struct CommandFailure {
    severity: IncidentSeverity,
    event_class: &'static str,
    summary: String,
    tokens: Vec<String>,
}

impl CommandFailure {
    /// The supervisor event of this failure about `subject`.
    fn into_event(self, entry: &IncidentLogEntry, subject: String) -> IncidentEvent {
        incident_event(
            entry,
            self.severity,
            IncidentCategory::Supervisor,
            self.event_class,
            subject,
            self.summary,
            self.tokens,
        )
    }
}

/// Classify the error body of a failed supervisor/daemon command (TS
/// `classifyCommandFailure`).
fn classify_command_failure(rules: IncidentRules, command: &str, error: &str) -> CommandFailure {
    let err = first_line(error);
    if err.contains(WORKER_TIMEOUT) {
        return CommandFailure {
            severity: IncidentSeverity::Error,
            event_class: "timeout",
            summary: format!("command {command} failed: timed out waiting for worker response"),
            tokens: Vec::new(),
        };
    }
    let fit = first_shape(
        rules,
        err,
        &[IncidentShape::AuthFailed, IncidentShape::UnknownSession],
    );
    let shape = fit.as_ref().map(|(shape, _)| *shape);
    if shape == Some(IncidentShape::AuthFailed) {
        return CommandFailure {
            severity: IncidentSeverity::Error,
            event_class: "auth",
            summary: format!("command {command} failed: worker authentication failed"),
            tokens: Vec::new(),
        };
    }
    if err.contains("Session worker is starting") {
        return CommandFailure {
            severity: IncidentSeverity::Warn,
            event_class: "command-failure",
            summary: format!("command {command} failed: session worker is starting"),
            tokens: Vec::new(),
        };
    }
    if err.contains("Session worker is recovering") {
        return CommandFailure {
            severity: IncidentSeverity::Warn,
            event_class: "command-failure",
            summary: format!("command {command} failed: session worker is recovering"),
            tokens: Vec::new(),
        };
    }
    if let Some((IncidentShape::UnknownSession, captures)) = &fit {
        let session_id = captures.get(1).to_string();
        return CommandFailure {
            severity: IncidentSeverity::Warn,
            event_class: "command-failure",
            summary: format!("command {command} failed: unknown active session {session_id}"),
            tokens: vec![session_id],
        };
    }
    // Quoted strings can carry session names (e.g. Agent name "Faerie").
    let quoted_names: Vec<String> = err
        .match_indices('"')
        .filter_map(|(index, _)| {
            let rest = &err[index + 1..];
            let end = rest.find('"')?;
            let name = &rest[..end];
            (!name.contains('\n') && !name.is_empty()).then(|| name.to_string())
        })
        .collect();
    CommandFailure {
        severity: IncidentSeverity::Warn,
        event_class: "command-failure",
        summary: format!("command {command} failed: {}", error_summary(err)),
        tokens: quoted_names,
    }
}

/// Classify the body of a `Session worker <id> stderr: <body>` log line
/// (TS `classifyWorkerStderrBody`).
fn classify_worker_stderr_body(
    rules: IncidentRules,
    worker_id: &str,
    body: &str,
    include_generic: bool,
) -> Option<WorkerStderrEvent> {
    let tokens = vec![worker_id.to_string()];
    if body.trim().is_empty() || first_shape(rules, body, &[IncidentShape::StackFrame]).is_some() {
        // Stack frames and blank lines belong to the previous stderr
        // event.
        return None;
    }
    let line = first_line(body);
    let fit = first_shape(rules, line, &BODY_SHAPES);
    let shape = fit.as_ref().map(|(shape, _)| *shape);
    if shape == Some(IncidentShape::WorkerListening) {
        return Some(WorkerStderrEvent {
            severity: IncidentSeverity::Info,
            event_class: "worker-start",
            subject: format!("worker {worker_id}"),
            summary: format!("worker {worker_id} started"),
            tokens,
        });
    }
    if shape == Some(IncidentShape::CrashLine) {
        return Some(WorkerStderrEvent {
            severity: IncidentSeverity::Critical,
            event_class: "worker-crash",
            subject: format!("worker {worker_id}"),
            summary: format!("worker {worker_id} crashed: {}", truncate_text(line, 100)),
            tokens,
        });
    }
    if let Some((IncidentShape::ShutdownExit, captures)) = &fit {
        let exit = captures.get(1);
        let sessions = captures.get(2);
        return Some(WorkerStderrEvent {
            severity: IncidentSeverity::Info,
            event_class: "worker-stop",
            subject: format!("worker {worker_id}"),
            summary: format!(
                "worker {worker_id} stopped (exit {exit}, {sessions} session(s) closed)"
            ),
            tokens,
        });
    }
    if let Some((IncidentShape::SignalShutdown, captures)) = &fit {
        let signal = captures.get(1);
        return Some(WorkerStderrEvent {
            severity: IncidentSeverity::Info,
            event_class: "worker-stop",
            subject: format!("worker {worker_id}"),
            summary: format!("worker {worker_id} received {signal}; shutting down"),
            tokens,
        });
    }
    if let Some((IncidentShape::StopRequested, captures)) = &fit {
        let sessions = captures.get(1);
        return Some(WorkerStderrEvent {
            severity: IncidentSeverity::Info,
            event_class: "worker-stop",
            subject: format!("worker {worker_id}"),
            summary: format!("worker {worker_id} stop requested ({sessions} active session(s))"),
            tokens,
        });
    }
    if let Some((IncidentShape::Passivated, captures)) = &fit {
        let session_id = captures.get(1);
        let idle_minutes = captures.get(3);
        // A missing session name logs as `name=""`; that empty token must
        // not become a filter key.
        let name = captures.get(2).trim_matches('"');
        let mut passivated_tokens = vec![worker_id.to_string(), session_id.to_string()];
        if !name.is_empty() {
            passivated_tokens.push(name.to_string());
        }
        return Some(WorkerStderrEvent {
            severity: IncidentSeverity::Info,
            event_class: "worker-passivation",
            subject: format!("session {session_id}"),
            summary: format!("passivated idle child session {session_id} (idle {idle_minutes}m)"),
            tokens: passivated_tokens,
        });
    }
    if !include_generic {
        return None;
    }
    Some(WorkerStderrEvent {
        severity: IncidentSeverity::Warn,
        event_class: "worker-stderr",
        subject: format!("worker {worker_id}"),
        summary: format!("worker {worker_id} stderr: {}", truncate_text(line, 100)),
        tokens,
    })
}

/// Break a `Recovered ... uncertain operations: <list>` body into a count
/// and a ranked breakdown (TS `recoveryBreakdown`).
fn recovery_breakdown(operations: &str) -> (usize, String) {
    let list: Vec<&str> = operations
        .split(',')
        .map(str::trim)
        .filter(|operation| !operation.is_empty())
        .collect();
    if list.is_empty() {
        return (0, "none listed".to_string());
    }
    let mut counts: Vec<(&str, usize)> = Vec::new();
    for operation in &list {
        if let Some(entry) = counts.iter_mut().find(|(name, _)| name == operation) {
            entry.1 += 1;
        } else {
            counts.push((operation, 1));
        }
    }
    counts.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(b.0)));
    let top = &counts[..RECOVERY_BREAKDOWN_LIMIT.min(counts.len())];
    let shown_count: usize = top.iter().map(|(_, count)| *count).sum();
    let rest = if counts.len() > RECOVERY_BREAKDOWN_LIMIT {
        format!(", +{} more", list.len() - shown_count)
    } else {
        String::new()
    };
    let breakdown = top
        .iter()
        .map(|(operation, count)| format!("{operation} x{count}"))
        .collect::<Vec<_>>()
        .join(", ");
    (list.len(), format!("{breakdown}{rest}"))
}

/// Classify a provider-failure entry into an aggregate-friendly anomaly
/// event (TS `providerFailureEvent`).
fn provider_failure_event(entry: &IncidentLogEntry, worker_pids: &WorkerPidMap) -> IncidentEvent {
    let worker_id = worker_id_for_pid(worker_pids, entry.pid, entry.time_ms);
    let subject = match (&worker_id, entry.pid) {
        (Some(worker_id), _) => format!("worker {worker_id}"),
        (None, Some(pid)) => format!("pid {pid}"),
        (None, None) => "provider".to_string(),
    };
    if entry.msg != "provider stream failure" {
        return event(
            entry,
            IncidentSeverity::Error,
            IncidentCategory::Anomaly,
            "provider",
            subject,
            truncate_text(first_line(&entry.msg), SUMMARY_TRUNCATION),
        );
    }
    let kind = entry
        .fields
        .get("kind")
        .and_then(serde_json::Value::as_str)
        .unwrap_or("unknown");
    let status_text = match entry
        .fields
        .get("status")
        .and_then(serde_json::Value::as_i64)
    {
        Some(status) => format!(" {status}"),
        None => String::new(),
    };
    IncidentEvent {
        time_ms: entry.time_ms,
        severity: IncidentSeverity::Error,
        category: IncidentCategory::Anomaly,
        event_class: "provider".to_string(),
        summary: format!("provider stream failure ({kind}{status_text}) for {subject}"),
        tokens: worker_id.into_iter().collect(),
        subject,
    }
}

/// Classify one log entry into an incident event; `None` when the entry is
/// noise (TS `classifyIncidentEntry`).
#[must_use]
pub fn classify_incident_entry(
    rules: IncidentRules,
    entry: &IncidentLogEntry,
    worker_pids: &WorkerPidMap,
) -> Option<IncidentEvent> {
    if entry.component == "ai.provider" {
        return Some(provider_failure_event(entry, worker_pids));
    }
    if let Some((_, captures)) = first_shape(rules, &entry.msg, &[IncidentShape::StderrForward]) {
        let body = classify_worker_stderr_body(rules, captures.get(1), captures.get(2), true)?;
        return Some(body.into_event(entry));
    }
    let worker_id = worker_id_from_socket_path(rules, entry.socket_path.as_deref());
    let worker_id = worker_id.as_deref();
    first_shape(rules, first_line(&entry.msg), &LINE_SHAPES)
        .and_then(|(shape, captures)| line_event(rules, entry, worker_id, shape, &captures))
        .or_else(|| daemon_event(rules, entry, worker_id))
}

/// The event of a log line that fits `shape`, one of [`LINE_SHAPES`];
/// `None` for any other shape.
fn line_event(
    rules: IncidentRules,
    entry: &IncidentLogEntry,
    worker_id: Option<&str>,
    shape: IncidentShape,
    captures: &Captures,
) -> Option<IncidentEvent> {
    use IncidentCategory::{Recovery, Supervisor};
    use IncidentSeverity::{Error, Info, Warn};
    let msg = first_line(&entry.msg);
    // Capture 1 of every worker shape names the worker.
    let worker = captures.get(1);
    let on_daemon = |severity, category, event_class, summary: String| {
        event(
            entry,
            severity,
            category,
            event_class,
            daemon_subject(entry),
            summary,
        )
    };
    let on_worker = |severity, category, event_class, summary: String| {
        worker_event(entry, severity, category, event_class, worker, summary)
    };
    Some(match shape {
        IncidentShape::SupervisorListening => {
            let summary = "daemon supervisor listening".to_string();
            on_daemon(Info, Supervisor, "supervisor-start", summary)
        }
        IncidentShape::StartupFailed => startup_failed_event(entry, captures.get(1)),
        IncidentShape::SupervisorCommand => {
            classify_command_failure(rules, captures.get(1), captures.get(2))
                .into_event(entry, daemon_subject(entry))
        }
        IncidentShape::DaemonCommand => daemon_command_event(rules, entry, worker_id, captures),
        IncidentShape::CatchUp => catch_up_event(entry, captures.opt(1), captures.get(2)),
        IncidentShape::HeartbeatsList => {
            let err = captures.get(1);
            let (severity, event_class) = failure_class(err);
            let summary = format!("worker heartbeat list failed: {}", error_summary(err));
            on_daemon(severity, Supervisor, event_class, summary)
        }
        IncidentShape::Recovered => {
            let (count, breakdown) = recovery_breakdown(captures.get(2));
            let plural = if count == 1 { "" } else { "s" };
            let summary = format!(
                "worker {worker} recovered; {count} uncertain operation{plural} not replayed ({breakdown})"
            );
            on_worker(Warn, Recovery, "recovery-replay", summary)
        }
        IncidentShape::RecoveredPlain => {
            let summary = format!("worker {worker} recovered");
            on_worker(Info, Recovery, "recovery-replay", summary)
        }
        IncidentShape::AdoptFailed => {
            let err = error_summary(captures.get(2));
            let summary = format!("could not adopt worker {worker}: {err}");
            on_worker(Warn, Recovery, "recovery-failure", summary)
        }
        IncidentShape::RecoverFailed => {
            let err = error_summary(captures.get(2));
            let summary = format!("could not recover worker {worker}: {err}");
            on_worker(Error, Recovery, "recovery-failure", summary)
        }
        IncidentShape::FailedAfterRetries => {
            let summary = format!("worker {worker} failed after three recovery attempts");
            on_worker(Error, Recovery, "recovery-failure", summary)
        }
        IncidentShape::Unresponsive => {
            on_worker(Error, Recovery, "recovery-failure", msg.to_string())
        }
        IncidentShape::Reclaimed => {
            let summary = format!("reclaimed stale registration for stopped worker {worker}");
            on_worker(Info, Recovery, "recovery-action", summary)
        }
        IncidentShape::Migrated => {
            let jobs = captures.get(1);
            let summary = format!("migrated {jobs} scheduled jobs into session artifacts");
            on_daemon(Info, Recovery, "recovery-action", summary)
        }
        IncidentShape::Replacement => on_daemon(Info, Recovery, "recovery-action", msg.to_string()),
        // A scheduled wake is a supervisor lifecycle action, not crash
        // recovery.
        IncidentShape::Woke => on_daemon(Info, Supervisor, "supervisor-action", msg.to_string()),
        IncidentShape::EvictedIdle => {
            let (idle, sessions) = (captures.get(2), captures.get(3));
            let summary =
                format!("evicted idle worker {worker} (idle {idle}m, {sessions} session(s))");
            on_worker(Info, Supervisor, "worker-stop", summary)
        }
        IncidentShape::EvictedEmpty => {
            let summary = format!("evicted empty session worker {worker} on last detach");
            on_worker(Info, Supervisor, "worker-stop", summary)
        }
        IncidentShape::WorkerSocket
        | IncidentShape::StderrForward
        | IncidentShape::WorkerListening
        | IncidentShape::CrashLine
        | IncidentShape::CrashPrefix
        | IncidentShape::ShutdownExit
        | IncidentShape::SignalShutdown
        | IncidentShape::StopRequested
        | IncidentShape::Passivated
        | IncidentShape::AuthFailed
        | IncidentShape::UnknownSession
        | IncidentShape::StackFrame
        | IncidentShape::DaemonLine => return None,
    })
}

/// The event of a `Daemon supervisor startup failed: <err>` line.
fn startup_failed_event(entry: &IncidentLogEntry, err: &str) -> IncidentEvent {
    // TS tests the message case-insensitively
    // (/lock file is already being held/i): real log lines carry
    // "Lock file is already being held".
    let (severity, summary) = if err
        .to_ascii_lowercase()
        .contains("lock file is already being held")
    {
        (
            IncidentSeverity::Warn,
            "supervisor startup blocked: another daemon holds the lock".to_string(),
        )
    } else {
        (
            IncidentSeverity::Error,
            format!("supervisor startup failed: {}", error_summary(err)),
        )
    };
    event(
        entry,
        severity,
        IncidentCategory::Supervisor,
        "supervisor-start",
        daemon_subject(entry),
        summary,
    )
}

/// The event of a `daemon command "<command>" failed: <error>` line, on
/// the worker of the entry's socket.
fn daemon_command_event(
    rules: IncidentRules,
    entry: &IncidentLogEntry,
    worker_id: Option<&str>,
    captures: &Captures,
) -> IncidentEvent {
    let failure = classify_command_failure(rules, captures.get(1), captures.get(2));
    let subject = worker_id.map_or_else(
        || "worker".to_string(),
        |worker_id| format!("worker {worker_id}"),
    );
    CommandFailure {
        // Keep the session ids/names classified out of the error, not
        // just the worker id.
        tokens: worker_id
            .map(str::to_string)
            .into_iter()
            .chain(failure.tokens)
            .collect(),
        ..failure
    }
    .into_event(entry, subject)
}

/// The event of a failed client catch-up, for `session_id` if the line
/// names one.
fn catch_up_event(entry: &IncidentLogEntry, session_id: Option<&str>, err: &str) -> IncidentEvent {
    let (severity, event_class) = failure_class(err);
    let for_session = session_id.map_or_else(String::new, |id| format!(" for session {id}"));
    incident_event(
        entry,
        severity,
        IncidentCategory::Supervisor,
        event_class,
        session_id.map_or_else(
            || daemon_subject(entry),
            |session_id| format!("session {session_id}"),
        ),
        format!(
            "client catch-up failed{for_session}: {}",
            error_summary(err)
        ),
        session_id.map(str::to_string).into_iter().collect(),
    )
}

/// The event of a daemon line no line shape fits: the worker's own
/// lifecycle line or crash, else a summary of the diagnostic. `None` for
/// a line of any other component.
fn daemon_event(
    rules: IncidentRules,
    entry: &IncidentLogEntry,
    worker_id: Option<&str>,
) -> Option<IncidentEvent> {
    let msg = first_line(&entry.msg);
    let own = match entry.component.as_str() {
        // The worker logs its own lifecycle lines; reusing the stderr-body
        // classifier gives them the same summaries as the supervisor's
        // stderr forward, so the duplicated log pair collapses in the
        // timeline.
        "coding-agent.daemon" => match worker_id {
            Some(worker_id) => classify_worker_stderr_body(rules, worker_id, msg, false)
                .map(|body| body.into_event(entry)),
            None => first_shape(rules, msg, &[IncidentShape::CrashPrefix]).map(|_| {
                event(
                    entry,
                    IncidentSeverity::Critical,
                    IncidentCategory::Supervisor,
                    "worker-crash",
                    "worker",
                    format!("worker crashed: {}", truncate_text(msg, 100)),
                )
            }),
        },
        "coding-agent.daemon-supervisor" => None,
        _ => return None,
    };
    // Unknown diagnostics still matter during an incident; summarize them.
    Some(own.unwrap_or_else(|| {
        event(
            entry,
            if entry.level == "error" {
                IncidentSeverity::Error
            } else {
                IncidentSeverity::Warn
            },
            IncidentCategory::Supervisor,
            "diagnostic",
            worker_id.map_or_else(
                || daemon_subject(entry),
                |worker_id| format!("worker {worker_id}"),
            ),
            truncate_text(msg, SUMMARY_TRUNCATION),
        )
    }))
}

/// Classify every entry, dropping the duplicate event the daemon writes
/// both to the structured log and to the worker stderr forward (same
/// summary, same second) (TS `collectIncidentEvents`).
#[must_use]
pub fn collect_incident_events(
    rules: IncidentRules,
    entries: &[IncidentLogEntry],
    worker_pids: &WorkerPidMap,
) -> Vec<IncidentEvent> {
    let mut events: Vec<IncidentEvent> = Vec::new();
    let mut last_seen: HashMap<String, (i64, String)> = HashMap::new();
    for entry in entries {
        let Some(incident) = classify_incident_entry(rules, entry, worker_pids) else {
            continue;
        };
        // The daemon writes the same lifecycle event both to the
        // structured log (coding-agent.daemon) and to the worker stderr
        // forward (coding-agent.daemon-supervisor); drop the second copy
        // when it lands within 2s. A repeat from the SAME component is a
        // real lifecycle transition — a worker restarted on its durable
        // id within 2s — and is never a duplicate.
        if lifecycle_classes().contains(incident.event_class.as_str()) {
            let key = format!("{}|{}", incident.category.as_str(), incident.summary);
            let previous = last_seen.get(&key);
            if let Some((previous_time_ms, previous_component)) = previous {
                if previous_component != &entry.component
                    && (incident.time_ms - previous_time_ms).abs() <= 2000
                {
                    continue;
                }
            }
            last_seen.insert(key, (incident.time_ms, entry.component.clone()));
        }
        events.push(incident);
    }
    events
}
