//! The agent-roster vocabulary shared by the supervisor's roster store and
//! every viewing surface (the TUI agents view, agent observation). Port of
//! `modes/daemon/agent-roster.ts`: the one status formula every surface
//! shares, the roster agent-id formula, and the wire entry shape carried by
//! `roster_subscribe` responses and `roster_update` pushes.

use crate::JsonMap;
use serde::{Deserialize, Serialize};
use serde_json::Value;

/// One status formula output (TS `AgentRosterStatus`). Surfaces adapt their
/// inputs and never reimplement the classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum AgentRosterStatus {
    Running,
    Idle,
    Inactive,
}

/// The inputs to the status formula (TS `AgentStatusInput`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AgentStatusInput {
    /// A live runtime exists for the agent.
    pub resident: bool,
    /// An admitted child run whose session has not materialized yet.
    pub queued_child: bool,
    /// Actively working: streaming or running tools/bash.
    pub busy: bool,
}

/// The one status formula (TS `classifyAgentStatus`).
#[must_use]
pub fn classify_agent_status(input: AgentStatusInput) -> AgentRosterStatus {
    if input.queued_child {
        return AgentRosterStatus::Running;
    }
    if !input.resident {
        return AgentRosterStatus::Inactive;
    }
    if input.busy {
        AgentRosterStatus::Running
    } else {
        AgentRosterStatus::Idle
    }
}

/// The `activity` of a wire summary; any other label is idle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
enum Activity {
    Working,
    #[serde(other)]
    Other,
}

/// The `runtimeKind` of a wire summary; any other kind is top-level. Open
/// on the wire: an unknown kind stays in [`RuntimeKind::Other`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeKind {
    /// A child agent session.
    Subagent,
    /// Any other kind (top-level sessions and unknown wire words), kept
    /// as written.
    Other(String),
}

impl RuntimeKind {
    /// The top-level kind (no `runtimeKind` on the wire).
    pub const TOP_LEVEL: Self = Self::Other(String::new());

    /// The wire word.
    #[must_use]
    pub fn as_str(&self) -> &str {
        match self {
            Self::Subagent => "subagent",
            Self::Other(kind) => kind,
        }
    }

    /// The kind named by a wire word; unknown words land in
    /// [`Self::Other`](enum@Self::Other).
    #[must_use]
    pub fn parse(kind: &str) -> Self {
        match kind {
            "subagent" => Self::Subagent,
            other => Self::Other(other.to_owned()),
        }
    }
}

impl Serialize for RuntimeKind {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.as_str())
    }
}

impl<'de> Deserialize<'de> for RuntimeKind {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(Self::parse(&String::deserialize(deserializer)?))
    }
}

impl Activity {
    fn parse(activity: &str) -> Self {
        match activity {
            "working" => Self::Working,
            _ => Self::Other,
        }
    }
}

/// The `lifecycle` of a wire summary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
enum Lifecycle {
    Archived,
    #[serde(other)]
    Other,
}

/// The `taskState` of a wire summary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
enum TaskState {
    Error,
    Completed,
    #[serde(other)]
    Other,
}

/// The `workerState` of a wire summary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
enum WorkerState {
    Ready,
    #[serde(other)]
    Other,
}

/// One summary field as `T`; absent, null or another shape is `None`.
fn field<'a, T: Deserialize<'a>>(summary: &'a Value, key: &str) -> Option<T> {
    summary
        .get(key)
        .and_then(|value| T::deserialize(value).ok())
}

/// One boolean summary field; absent or another shape is false.
fn flag(summary: &Value, key: &str) -> bool {
    summary.get(key).and_then(Value::as_bool) == Some(true)
}

/// Classify one session summary (TS `classifySessionRosterStatus`): a
/// resident session is busy when its activity is `working` or the session
/// reports an active turn.
#[must_use]
pub fn classify_session_roster_status(
    resident: bool,
    activity: &str,
    session_active: bool,
    queued_child: bool,
) -> AgentRosterStatus {
    classify_agent_status(AgentStatusInput {
        resident,
        queued_child,
        busy: Activity::parse(activity) == Activity::Working || session_active,
    })
}

/// Classify a summary in its wire (JSON) form: `Value` in, status out.
#[must_use]
pub fn classify_summary_value(summary: &Value, queued_child: bool) -> AgentRosterStatus {
    let resident = summary
        .get("activeSessionId")
        .is_some_and(|id| !id.is_null() && id.as_str() != Some(""));
    let working = field(summary, "activity") == Some(Activity::Working);
    classify_agent_status(AgentStatusInput {
        resident,
        queued_child,
        busy: working || flag(summary, "isSessionActive"),
    })
}

/// The roster agent id (TS `rosterAgentIdForSummary`): child ids are only
/// unique per parent, so the parent key (canonical session path, or the
/// live parent id for no-session parents) qualifies them daemon-wide;
/// top-level sessions key by session id. The caller passes the parent path
/// already canonicalized.
#[must_use]
pub fn roster_agent_id(
    session_id: &str,
    runtime_kind: RuntimeKind,
    rlm_child_id: Option<&str>,
    parent_key: Option<&str>,
) -> String {
    agent_id(session_id, runtime_kind, rlm_child_id, parent_key)
}

fn agent_id(
    session_id: &str,
    runtime_kind: RuntimeKind,
    rlm_child_id: Option<&str>,
    parent_key: Option<&str>,
) -> String {
    match (runtime_kind, rlm_child_id) {
        // No-session parents have no path (and no ledger edge); their live
        // parent id still disambiguates.
        (RuntimeKind::Subagent, Some(child_id)) => match parent_key {
            Some(key) if !key.is_empty() => format!("{key}#{child_id}"),
            _ => child_id.to_owned(),
        },
        (RuntimeKind::Subagent, None) | (RuntimeKind::Other(_), _) => session_id.to_owned(),
    }
}

/// The roster agent id for a summary in its wire (JSON) form.
#[must_use]
pub fn roster_agent_id_for_summary(summary: &Value) -> String {
    let session_id = field(summary, "sessionId").unwrap_or_default();
    let runtime_kind = field(summary, "runtimeKind").unwrap_or(RuntimeKind::TOP_LEVEL);
    let non_empty = |key| field::<&str>(summary, key).filter(|text| !text.is_empty());
    let parent_key = non_empty("parentSessionPath").or_else(|| non_empty("parentActiveSessionId"));
    agent_id(
        session_id,
        runtime_kind,
        field(summary, "rlmChildId"),
        parent_key,
    )
}

/// View-specific labels for the shared activity branch table below (TS
/// `SessionActivityOptions`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SessionActivityOptions {
    /// Label for a row with an armed heartbeat (the agents view adds a
    /// live countdown; a static table has no next-run timer).
    pub heartbeat_label: String,
    /// Fallback when no branch fires (the agents view says "needs input";
    /// the sessions table leaves the cell empty because its status column
    /// already says idle).
    pub idle_label: String,
}

/// The one activity branch table (TS `sessionActivityDetail`): what a
/// session is doing right now, read from the wire summary's runtime flags.
/// The agents view status label and the CLI sessions table activity column
/// both derive from it, so a state added here serves every surface. The
/// TS action branch (agents-view-only labels over `sessionActions`) rides
/// with that view's port; the roster rows this table reads carry an empty
/// action snapshot, so no branch is missing.
///
/// `statusLabel` and `lastHeardFromAt` stay with the caller: the agents
/// view returns them before delegating, the sessions table gives them
/// their own columns.
#[must_use]
pub fn session_activity_detail(summary: &Value, options: &SessionActivityOptions) -> String {
    activity_label(summary, options).to_owned()
}

fn activity_label<'a>(summary: &'a Value, options: &'a SessionActivityOptions) -> &'a str {
    let active = |key: &str| flag(summary, key);
    // A non-ready worker cannot report fresh runtime flags; its state is
    // the row's story. A row already carrying the ledger mark keeps that
    // mark out of the activity (its surface shows it as the status).
    if let (Some(worker_state), Some(WorkerState::Other), None) = (
        field::<&str>(summary, "workerState"),
        field(summary, "workerState"),
        field::<&str>(summary, "statusLabel"),
    ) {
        return worker_state;
    }
    if active("isCompacting") {
        return "compacting";
    }
    if active("isStreaming") {
        return if active("isRunningTools") {
            "running tools"
        } else {
            "thinking"
        };
    }
    // Tool/bash activity classifies the session as running; the label must
    // agree with that classification instead of claiming it needs input.
    if active("isRunningTools") {
        return "running tools";
    }
    if active("isBashRunning") {
        return "running bash";
    }
    // The session's own turn ended, but its subagents still work: the
    // worker reports `activity: "working"` for it, and the label says why.
    if active("hasRunningSubagents") {
        return "subagents running";
    }
    if field(summary, "lifecycle") == Some(Lifecycle::Archived) {
        return "archived";
    }
    if active("hasActiveHeartbeat") {
        return &options.heartbeat_label;
    }
    if field(summary, "runtimeKind") == Some(RuntimeKind::Subagent) && active("repliedSinceTask") {
        return "replied";
    }
    if field(summary, "activity") == Some(Activity::Working) {
        return "working";
    }
    match field(summary, "taskState") {
        Some(TaskState::Error) => "error",
        Some(TaskState::Completed) => "completed",
        Some(TaskState::Other) | None => &options.idle_label,
    }
}

/// The work in flight a session summary (wire form) reports, if any: a
/// compaction, a user shell command, a turn waiting out a usage limit, a
/// turn retrying its provider, a turn, running subagents, or the
/// background work its turn left (`waitingOn`: jobs, kernel commands,
/// children, workflow runs). A field the summary lacks reports no work.
#[must_use]
pub fn summary_work(summary: &Value) -> Option<&'static str> {
    let flag = |key: &str| flag(summary, key);
    let present = |key: &str| summary.get(key).is_some_and(|value| !value.is_null());
    if flag("isCompacting") {
        Some("a compaction")
    } else if flag("isBashRunning") {
        Some("a shell command")
    } else if flag("isQuotaParked") {
        Some("a turn waiting out a usage limit")
    } else if present("retry") {
        Some("a turn retrying its provider")
    } else if flag("isStreaming")
        || flag("isRunningTools")
        || field(summary, "activity") == Some(Activity::Working)
    {
        Some("a turn")
    } else if flag("hasRunningSubagents") {
        Some("running subagents")
    } else if present("waitingOn") {
        Some("background work")
    } else {
        None
    }
}

/// One roster entry (TS `AgentRosterEntry`): the agent's slim session
/// summary with the supervisor's classification. `statusLabel` is set only
/// for exceptional states; viewers key label display on its presence.
/// `lastHeardFromAt` is when the supervisor last accepted a delta from the
/// row's worker (absent for a row no worker wrote yet).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentRosterEntry {
    pub agent_id: String,
    /// `true` marks an admitted child run whose session has not
    /// materialized yet.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub queued_child: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub seeded_cwd: Option<bool>,
    /// The slim session summary (the wire summary without
    /// `streamingMessage`/`sessionActions`/`diagnostics`).
    pub summary: Value,
    pub status: AgentRosterStatus,
    /// `queued` / `recovering` / `failed` (TS `statusLabel`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub status_label: Option<String>,
    /// When the supervisor last heard from the row's worker (RFC 3339): a
    /// running agent whose stamp stops moving has gone quiet.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_heard_from_at: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub worker_id: Option<String>,
    #[serde(flatten)]
    pub rest: JsonMap,
}

/// The slim summary a worker reports for the roster (TS
/// `workerRosterEntryFromSummary`): the full summary minus the
/// streaming-message, session-actions, and diagnostics fields.
#[must_use]
pub fn slim_roster_summary(summary: Value) -> Value {
    let mut summary = summary;
    if let Value::Object(map) = &mut summary {
        map.remove("streamingMessage");
        map.remove("sessionActions");
        map.remove("diagnostics");
    }
    summary
}

/// Where an agent's model request stands against its provider's
/// admission (`providerMaxInFlight`; an unlimited provider admits at
/// once): the summary's `admission` field, absent while the agent has no
/// model request waiting or in flight.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ModelAdmission {
    /// Waiting for a free slot of the provider.
    Queued,
    /// Holding a slot: the request is out.
    Generating,
}

/// The `admission` field of a summary in its wire (JSON) form; `None` when
/// absent or unrecognized.
#[must_use]
pub fn summary_admission(summary: &Value) -> Option<ModelAdmission> {
    summary
        .get("admission")
        .and_then(|admission| ModelAdmission::deserialize(admission).ok())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn status_formula_matches_ts() {
        use AgentRosterStatus::*;
        let input = |resident, queued_child, busy| AgentStatusInput {
            resident,
            queued_child,
            busy,
        };
        assert_eq!(classify_agent_status(input(false, false, false)), Inactive);
        assert_eq!(classify_agent_status(input(false, true, false)), Running);
        assert_eq!(classify_agent_status(input(true, false, false)), Idle);
        assert_eq!(classify_agent_status(input(true, false, true)), Running);
        // A queued child stays running even without a resident runtime.
        assert_eq!(classify_agent_status(input(true, true, false)), Running);
    }

    #[test]
    fn session_classification_reads_activity_and_active_turn() {
        let summary = json!({ "activeSessionId": "a1", "activity": "working" });
        assert_eq!(
            classify_summary_value(&summary, false),
            AgentRosterStatus::Running
        );
        let summary = json!({ "activeSessionId": "a1", "activity": "idle" });
        assert_eq!(
            classify_summary_value(&summary, false),
            AgentRosterStatus::Idle
        );
        // An active turn marks running even when the activity label is idle.
        let summary =
            json!({ "activeSessionId": "a1", "activity": "idle", "isSessionActive": true });
        assert_eq!(
            classify_summary_value(&summary, false),
            AgentRosterStatus::Running
        );
        // Own turn done, subagents still running: the worker reports the
        // session as working, so it classifies running.
        let summary = json!({
            "activeSessionId": "a1",
            "activity": "working",
            "isSessionActive": false,
            "hasRunningSubagents": true,
        });
        assert_eq!(
            classify_summary_value(&summary, false),
            AgentRosterStatus::Running
        );
        // No active session id: not resident.
        let summary = json!({ "activity": "working" });
        assert_eq!(
            classify_summary_value(&summary, false),
            AgentRosterStatus::Inactive
        );
    }

    #[test]
    fn agent_ids_qualify_children_by_parent_key() {
        // Top-level: session id.
        assert_eq!(
            roster_agent_id("s1", RuntimeKind::parse("top-level"), None, None),
            "s1"
        );
        // Subagent: parent path + child id.
        assert_eq!(
            roster_agent_id(
                "s2",
                RuntimeKind::Subagent,
                Some("7"),
                Some("/x/sess.jsonl")
            ),
            "/x/sess.jsonl#7"
        );
        // No-session parent: live parent id qualifies.
        assert_eq!(
            roster_agent_id("s2", RuntimeKind::Subagent, Some("7"), Some("a1")),
            "a1#7"
        );
        // No parent key at all: bare child id.
        assert_eq!(
            roster_agent_id("s2", RuntimeKind::Subagent, Some("7"), None),
            "7"
        );
    }

    #[test]
    fn agent_id_from_summary_wire_form() {
        let summary = json!({
            "sessionId": "s2",
            "runtimeKind": "subagent",
            "rlmChildId": "7",
            "parentActiveSessionId": "a1",
        });
        assert_eq!(roster_agent_id_for_summary(&summary), "a1#7");
        // parentSessionPath wins over the live parent id.
        let summary = json!({
            "sessionId": "s2",
            "runtimeKind": "subagent",
            "rlmChildId": "7",
            "parentSessionPath": "/x/sess.jsonl",
            "parentActiveSessionId": "a1",
        });
        assert_eq!(roster_agent_id_for_summary(&summary), "/x/sess.jsonl#7");
    }

    /// The minimal wire summary the branch table reads; tests merge field
    /// overrides into it.
    fn activity_summary(overrides: Value) -> Value {
        let mut summary = json!({
            "id": "s",
            "lifecycle": "live",
            "activity": "idle",
            "isStreaming": false,
            "isCompacting": false,
        });
        match (&mut summary, overrides) {
            (Value::Object(base), Value::Object(over)) => {
                for (key, value) in over {
                    base.insert(key, value);
                }
            }
            _ => panic!("summary fixtures must be objects"),
        }
        summary
    }

    #[test]
    fn summary_work_names_each_kind_of_reported_work() {
        let work = |overrides: Value| summary_work(&activity_summary(overrides));
        assert_eq!(
            [
                work(json!({})),
                work(json!({ "waitingOn": null, "retry": null })),
                work(json!({ "isCompacting": true, "activity": "working" })),
                work(json!({ "isBashRunning": true })),
                work(json!({ "isQuotaParked": true })),
                work(json!({ "retry": { "attempt": 1 } })),
                work(json!({ "isStreaming": true })),
                work(json!({ "isRunningTools": true })),
                work(json!({ "activity": "working" })),
                work(json!({ "hasRunningSubagents": true })),
                work(json!({ "waitingOn": { "jobs": 1 } })),
            ],
            [
                None,
                None,
                Some("a compaction"),
                Some("a shell command"),
                Some("a turn waiting out a usage limit"),
                Some("a turn retrying its provider"),
                Some("a turn"),
                Some("a turn"),
                Some("a turn"),
                Some("running subagents"),
                Some("background work"),
            ]
        );
    }

    #[test]
    fn activity_detail_branches_match_the_shared_wording() {
        let options = SessionActivityOptions {
            heartbeat_label: "heartbeat".to_string(),
            idle_label: String::new(),
        };
        let detail =
            |overrides: Value| session_activity_detail(&activity_summary(overrides), &options);
        assert_eq!(
            detail(json!({ "activity": "working", "isStreaming": true, "isRunningTools": true })),
            "running tools"
        );
        assert_eq!(
            detail(json!({ "activity": "working", "isStreaming": true })),
            "thinking"
        );
        assert_eq!(
            detail(json!({ "activity": "working", "isBashRunning": true })),
            "running bash"
        );
        assert_eq!(
            detail(json!({ "activity": "working", "isCompacting": true })),
            "compacting"
        );
        assert_eq!(
            detail(json!({ "activity": "working", "hasRunningSubagents": true })),
            "subagents running"
        );
        assert_eq!(
            detail(json!({ "activity": "working", "workerState": "starting" })),
            "starting"
        );
        assert_eq!(detail(json!({ "lifecycle": "archived" })), "archived");
        assert_eq!(
            detail(json!({ "runtimeKind": "subagent", "repliedSinceTask": true })),
            "replied"
        );
        assert_eq!(detail(json!({ "activity": "working" })), "working");
        assert_eq!(detail(json!({ "taskState": "error" })), "error");
        assert_eq!(detail(json!({ "taskState": "completed" })), "completed");
        // No branch fires: the surface's idle fallback.
        assert_eq!(detail(json!({})), "");
    }

    #[test]
    fn activity_detail_labels_carry_the_surface_options() {
        let view = SessionActivityOptions {
            heartbeat_label: "heartbeat \u{b7} next 3m".to_string(),
            idle_label: "needs input".to_string(),
        };
        assert_eq!(
            session_activity_detail(
                &activity_summary(json!({ "hasActiveHeartbeat": true })),
                &view
            ),
            "heartbeat \u{b7} next 3m"
        );
        assert_eq!(
            session_activity_detail(&activity_summary(json!({})), &view),
            "needs input"
        );
        let table = SessionActivityOptions {
            heartbeat_label: "heartbeat".to_string(),
            idle_label: String::new(),
        };
        assert_eq!(
            session_activity_detail(
                &activity_summary(json!({ "hasActiveHeartbeat": true })),
                &table
            ),
            "heartbeat"
        );
        assert_eq!(
            session_activity_detail(&activity_summary(json!({})), &table),
            ""
        );
    }

    #[test]
    fn activity_detail_worker_state_waits_for_no_ledger_mark() {
        let options = SessionActivityOptions {
            heartbeat_label: "heartbeat".to_string(),
            idle_label: String::new(),
        };
        // A ready worker is not the row's story: the runtime flags are.
        assert_eq!(
            session_activity_detail(
                &activity_summary(json!({ "workerState": "ready" })),
                &options
            ),
            ""
        );
        // A row already carrying the ledger mark keeps the worker state
        // out of the activity: its surface shows the mark as the status.
        assert_eq!(
            session_activity_detail(
                &activity_summary(
                    json!({ "statusLabel": "queued", "workerState": "starting", "activity": "working" })
                ),
                &options,
            ),
            "working"
        );
        // Without the mark, a non-ready worker is the story.
        assert_eq!(
            session_activity_detail(
                &activity_summary(json!({ "workerState": "recovering" })),
                &options
            ),
            "recovering"
        );
    }

    #[test]
    fn entry_round_trips_the_wire_shape() {
        let entry = AgentRosterEntry {
            agent_id: "s1".to_string(),
            queued_child: None,
            seeded_cwd: None,
            summary: json!({ "sessionId": "s1" }),
            status: AgentRosterStatus::Idle,
            status_label: None,
            last_heard_from_at: None,
            worker_id: Some("w1".to_string()),
            rest: JsonMap::default(),
        };
        let value = serde_json::to_value(&entry).unwrap();
        assert_eq!(value["agentId"], "s1");
        assert_eq!(value["status"], "idle");
        assert_eq!(value["workerId"], "w1");
        let back: AgentRosterEntry = serde_json::from_value(value).unwrap();
        assert_eq!(back, entry);
    }

    #[test]
    fn slim_summary_drops_view_only_fields() {
        let summary = json!({
            "sessionId": "s1",
            "streamingMessage": { "role": "assistant" },
            "sessionActions": { "queuedCount": 0 },
            "diagnostics": [],
        });
        let slim = slim_roster_summary(summary);
        assert_eq!(slim["sessionId"], "s1");
        assert!(slim.get("streamingMessage").is_none());
        assert!(slim.get("sessionActions").is_none());
        assert!(slim.get("diagnostics").is_none());
    }
}

#[cfg(test)]
mod runtime_kind_tests {
    use super::RuntimeKind;

    #[test]
    fn runtime_kind_round_trips_known_and_unknown_words() {
        let known = RuntimeKind::parse("subagent");
        assert_eq!(known, RuntimeKind::Subagent);
        assert_eq!(
            serde_json::to_string(&known).expect("serialize"),
            "\"subagent\""
        );
        let unknown = RuntimeKind::parse("cron-runner");
        assert_eq!(unknown, RuntimeKind::Other("cron-runner".to_owned()));
        assert_eq!(
            serde_json::to_string(&unknown).expect("serialize"),
            "\"cron-runner\""
        );
    }
}
