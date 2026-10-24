//! Responses and outbound events: `DaemonResponse`, `DaemonErrorInfo`, session
//! snapshot payloads, and the `DaemonOutbound` event union.

#[cfg(test)]
use super::rt;
use super::{
    AgentMessage, DaemonClientId, DaemonCommandId, DaemonEventCursor, DaemonEventId,
    DaemonEventMeta, DaemonEventSequence, DaemonProtocolInfo, DaemonReplayInfo,
    DaemonServerCapability, Deserialize, JsonMap, Serialize, SessionEvent, Value,
};

// ---------------------------------------------------------------------------
// Responses and outbound events
// ---------------------------------------------------------------------------

/// `type: "response"`: success or failure outcome of one command.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DaemonResponse {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    pub command: String,
    pub success: bool,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub data: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error_info: Option<DaemonErrorInfo>,
}

/// The session-addressed lanes' refusal when the session's kernel is not
/// running (the lane never builds one: `factory_activity` answers without
/// booting an idle kernel). A definitive answer, not a transient failure —
/// the kernel owns its run registry in memory, so a session without a
/// kernel carries no live runs; clients read it as such (the TUI's
/// `/factory off` guard counts zero instead of an unreadable count).
pub const KERNEL_NOT_RUNNING_MESSAGE: &str = "Kernel is not running";

/// Structured failure info carried on error responses, tagged by `code`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "code",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum DaemonErrorInfo {
    MissingSessionCwd {
        issue: Value,
    },
    SessionImportFileNotFound {
        file_path: String,
    },
    SessionAlreadyActive {
        session_path: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
    },
    SessionRecovering {
        active_session_id: String,
    },
    CommandResultUncertain {
        client_id: DaemonClientId,
        command_id: DaemonCommandId,
    },
    /// `set_model` resolved the model but its provider has no credential
    /// (and none is stale): a sign-in refusal, not a dead end — the
    /// client offers the provider's sign-in flow (the TUI's `/login`)
    /// and retries the switch once the login lands.
    ModelProviderUnauthenticated {
        provider: String,
    },
    /// The supervisor refused to enqueue a request-shaped client command
    /// because the target worker is at its in-flight bound: the request
    /// never left the supervisor, so a retry cannot duplicate it. The
    /// supervisor's answer to a saturated route (the Codex
    /// `-32001 "Server overloaded; retry later."` analog on our wire).
    WorkerOverloaded,
    /// A `shutdown` with `ifIdle` found a session with work (a run, a
    /// compaction, queued input, a background job, an unsettled child)
    /// or a worker that could not answer: nothing stopped, every session
    /// keeps running.
    DaemonBusy,
    /// `answer_shell_approval` named a question the session no longer
    /// holds: a client answered it first, its step ended, or every
    /// interactive client detached. Nothing to answer; the client drops
    /// its panel (the `shell_approval_settled` frame usually beat it).
    ShellApprovalGone,
    /// A `code` this build does not know (a newer daemon's typed
    /// refusal): forwards-compatibility — the unknown code must degrade
    /// to the plain refusal message that rides the same response instead
    /// of failing the response's deserialization, which would drop the
    /// refusal and leave the request riding to its timeout.
    #[serde(other)]
    Unknown,
}

/// Saved-session row pushed by `session_list_item` progress events.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DaemonSavedSessionInfo {
    pub path: String,
    pub id: String,
    pub cwd: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub state: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parent_session_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rlm_depth: Option<u64>,
    pub created: String,
    pub modified: String,
    pub message_count: u64,
    pub first_message: String,
    pub all_messages_text: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub usage: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model: Option<Value>,
    #[serde(flatten)]
    pub rest: JsonMap,
}

/// Full session snapshot (attach, replacement, resync).
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DaemonSessionSnapshot {
    pub active_session_id: String,
    pub summary: Value,
    pub state: Value,
    pub messages: Vec<AgentMessage>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub session_context: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub session_tree: Option<Value>,
    pub last_event_sequence: DaemonEventSequence,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_event_cursor: Option<DaemonEventCursor>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub parent: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub children: Option<Value>,
    #[serde(flatten)]
    pub rest: JsonMap,
}

/// Process identity of the daemon build, published in `daemon_hello`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DaemonRuntimeIdentity {
    pub build_id: String,
    pub executable_path: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub entrypoint_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub launcher_path: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum DaemonClosingReason {
    Shutdown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum DaemonSessionClosedReason {
    Killed,
    Shutdown,
    Completed,
    Replaced,
}

/// How one session stop ended at ADR 0011's kill boundary: the
/// cooperative `shutdown` request first, the process-group kill after the
/// grace. A `kill` response carries it as `data.stopOutcome`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum StopOutcome {
    /// The worker settled the cooperative shutdown inside the grace.
    Settled,
    /// The worker missed the grace and was killed with its process group:
    /// the effects of whatever it was running may or may not have landed.
    ForcedEffectsUnknown,
    /// The process outlived the escalation or cannot be identity-verified:
    /// its tombstoned descriptor carries the stop to the next boot.
    Survived,
}

/// Single-use credential for one direct TUI-to-worker connection.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DaemonPeerTransportTicket {
    pub purpose: String,
    pub socket_path: String,
    pub socket_identity: SocketIdentity,
    pub worker_instance_id: String,
    pub active_session_id: String,
    pub grant_id: String,
    pub token: String,
    pub expires_at: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct SocketIdentity {
    pub dev: u64,
    pub ino: u64,
}

/// Purpose tag of a `session_snapshot_begin` record. The catch-up value is
/// `resync` on the wire (`daemon-protocol.ts`:
/// `"attach" | "replacement" | "resync"`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum SnapshotPurpose {
    Attach,
    Replacement,
    #[serde(rename = "resync")]
    Catchup,
}

/// `type: "event"` envelope wrapping a [`DaemonOutbound`].
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DaemonEventEnvelope {
    pub id: DaemonEventId,
    pub protocol: DaemonProtocolInfo,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub active_session_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sequence: Option<DaemonEventSequence>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cursor: Option<DaemonEventCursor>,
    pub emitted_at: String,
    pub event: DaemonOutbound,
}

/// Supervisor -> client frames, tagged by `type`.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "type",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum DaemonOutbound {
    Response {
        #[serde(flatten)]
        response: DaemonResponse,
    },
    SessionListProgress {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        command: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        loaded: u64,
        total: u64,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SessionListItem {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        command: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        session: DaemonSavedSessionInfo,
        #[serde(flatten)]
        rest: JsonMap,
    },
    DaemonHello {
        socket_path: String,
        protocol: DaemonProtocolInfo,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        schema_id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        schema_revision: Option<u64>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        app_version: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        runtime: Option<DaemonRuntimeIdentity>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        supervisor_generation: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        supervisor_pid: Option<u64>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        supervisor_owner_token: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        supervisor_process_start_id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        supervisor_socket_path: Option<String>,
        client_id: DaemonClientId,
        server_capabilities: Vec<DaemonServerCapability>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    DaemonClosing {
        reason: DaemonClosingReason,
        #[serde(flatten)]
        rest: JsonMap,
    },
    HeartbeatsChanged {
        #[serde(flatten)]
        rest: JsonMap,
    },
    RosterUpdate {
        changed: Value,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        removed: Option<Vec<String>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        resync: Option<bool>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SessionEvent {
        active_session_id: String,
        event: SessionEvent,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        meta: Option<DaemonEventMeta>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SideQuestionEvent {
        active_session_id: String,
        event: Value,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native, advertised by the `shell_approval` capability: the
    /// session's `bash` tool asks the attached clients whether one step
    /// may run. Unsequenced, like `side_question_event`: the first
    /// `answer_shell_approval` for its request id wins. A subagent's
    /// question reaches the clients of the nearest session up its chain
    /// that has one; `agent` then names the subagent that asks.
    ShellApproval {
        active_session_id: String,
        request: crate::shell::ShellApprovalRequest,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        agent: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native, advertised by the `shell_approval` capability: the
    /// question `request_id` of the session is no longer pending (a
    /// client answered it, its step ended or was cancelled, or every
    /// interactive client detached and it went elsewhere): every client
    /// drops it. Unsequenced, like `shell_approval`.
    ShellApprovalSettled {
        active_session_id: String,
        request_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native, advertised by the `state_tree` capability: the new
    /// records of the session state tree, sent only to the connections
    /// that sent `subscribe_state_tree` for the session. It carries no
    /// event sequence: it is not a session event, and clients that do not
    /// subscribe never see a gap.
    StateTreeUpdate {
        active_session_id: String,
        update: super::StateTreeRecords,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SessionReplaced {
        active_session_id: String,
        state: Value,
        messages: Vec<AgentMessage>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        snapshot_follows: Option<bool>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        meta: Option<DaemonEventMeta>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SessionResynced {
        active_session_id: String,
        snapshot: DaemonSessionSnapshot,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        meta: Option<DaemonEventMeta>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SessionAttached {
        active_session_id: String,
        state: Value,
        messages: Vec<AgentMessage>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        snapshot: Option<DaemonSessionSnapshot>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        replay: Option<DaemonReplayInfo>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        last_event_sequence: Option<DaemonEventSequence>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SessionSnapshotBegin {
        active_session_id: String,
        snapshot_id: String,
        #[serde(flatten)]
        snapshot: Value,
        message_count: u64,
        target_chunk_bytes: u64,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        purpose: Option<SnapshotPurpose>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SessionSnapshotChunk {
        active_session_id: String,
        snapshot_id: String,
        index: u64,
        messages: Vec<AgentMessage>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SessionSnapshotEnd {
        active_session_id: String,
        snapshot_id: String,
        chunk_count: u64,
        last_event_sequence: DaemonEventSequence,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        last_event_cursor: Option<DaemonEventCursor>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SessionSnapshotFailed {
        active_session_id: String,
        snapshot_id: String,
        error: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SessionDetached {
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// The stale-id rebind notice (Rust-only extension over the TS wire): a
    /// worker replacement rebound a session, and the id the client holds is
    /// superseded. Old clients ignore the unknown type; attached clients
    /// re-attach to the session's current id so their event routing follows
    /// it.
    SessionBinding {
        previous_active_session_id: String,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        session_id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        session_file: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SessionClosed {
        active_session_id: String,
        reason: DaemonSessionClosedReason,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        meta: Option<DaemonEventMeta>,
        #[serde(flatten)]
        rest: JsonMap,
    },
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn response_and_error_info_roundtrip() {
        rt::<DaemonOutbound>(
            r#"{"type":"response","id":"r1","command":"prompt","success":true,"data":{"x":1}}"#,
        );
        rt::<DaemonOutbound>(
            r#"{"type":"response","id":"r2","command":"attach","success":false,"error":"boom","errorInfo":{"code":"session_already_active","sessionPath":"/s.jsonl","activeSessionId":"a"}}"#,
        );
        rt::<DaemonOutbound>(
            r#"{"type":"response","command":"import_jsonl","success":false,"error":"e","errorInfo":{"code":"session_import_file_not_found","filePath":"/x"}}"#,
        );
    }

    #[test]
    fn snapshot_purpose_tags_match_the_wire() {
        assert_eq!(
            serde_json::to_value(SnapshotPurpose::Attach).unwrap(),
            json!("attach")
        );
        assert_eq!(
            serde_json::to_value(SnapshotPurpose::Replacement).unwrap(),
            json!("replacement")
        );
        // The catch-up purpose is `resync` on the wire, never `catchup`.
        assert_eq!(
            serde_json::to_value(SnapshotPurpose::Catchup).unwrap(),
            json!("resync")
        );
        assert_eq!(
            serde_json::from_value::<SnapshotPurpose>(json!("resync")).unwrap(),
            SnapshotPurpose::Catchup
        );
    }

    #[test]
    fn hello_and_snapshot_roundtrip() {
        rt::<DaemonOutbound>(
            r#"{"type":"daemon_hello","socketPath":"/sock","protocol":{"name":"eukhe.daemon","version":7},"schemaId":"protocol-7-schema-28-92bc5368a082","schemaRevision":28,"appVersion":"1.0","supervisorGeneration":"g","supervisorPid":42,"clientId":"c","serverCapabilities":["attach_snapshot","event_sequence"]}"#,
        );
        let msg = r#"{"role":"user","content":"hi","timestamp":1}"#;
        rt::<DaemonOutbound>(&format!(
            r#"{{"type":"session_attached","activeSessionId":"s","state":{{"a":1}},"messages":[{msg}],"replay":{{"status":"complete","toSequence":5}},"lastEventSequence":5}}"#
        ));
        rt::<DaemonOutbound>(
            r#"{"type":"session_snapshot_chunk","activeSessionId":"s","snapshotId":"sn","index":0,"messages":[{"role":"assistant","content":[{"type":"text","text":"t"}],"api":"a","provider":"p","model":"m","usage":{"input":0,"output":0,"cacheRead":0,"cacheWrite":0,"totalTokens":0,"cost":{"input":0,"output":0,"cacheRead":0,"cacheWrite":0,"total":0}},"stopReason":"stop","timestamp":1}]}"#,
        );
    }

    /// A typed refusal this build does not know degrades to
    /// [`DaemonErrorInfo::Unknown`] instead of failing the response's
    /// deserialization: a newer daemon's unknown `code` must leave the
    /// plain refusal message (which rides the same response) to classify
    /// the rejection, never drop the response to the request timeout.
    #[test]
    fn an_unknown_error_info_code_degrades_to_unknown() {
        let parsed: DaemonErrorInfo =
            serde_json::from_str(r#"{"code":"some_future_code"}"#).expect("parse");
        assert_eq!(parsed, DaemonErrorInfo::Unknown);
        // The known codes keep their typed shape.
        let typed: DaemonErrorInfo =
            serde_json::from_str(r#"{"code":"worker_overloaded"}"#).expect("parse");
        assert_eq!(typed, DaemonErrorInfo::WorkerOverloaded);
    }
}
