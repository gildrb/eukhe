//! Worker protocol: the supervisor <-> worker command/event unions and worker
//! descriptors.

#[cfg(test)]
use super::rt;
use super::{DaemonClientCapability, Deserialize, JsonMap, Serialize, SnapshotPurpose, Value};

// ---------------------------------------------------------------------------
// Worker protocol (supervisor <-> worker)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum DaemonWorkerLifecycle {
    Starting,
    Ready,
    Recovering,
    Stopping,
    Failed,
}

/// Worker -> supervisor roster frames, outside the client-facing schema.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "type",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum DaemonWorkerRosterOutbound {
    RosterDelta {
        entries: Value,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        removed_agent_ids: Option<Vec<String>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        snapshot: Option<bool>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    RosterHeartbeat {
        #[serde(flatten)]
        rest: JsonMap,
    },
}

/// Frame header the worker writes to the supervisor pipe, tagging the payload
/// that follows in the same frame.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum DaemonWorkerFrameHeader {
    Command {
        request_id: String,
        command_type: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Outbound {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        request_id: Option<String>,
        outbound_type: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        snapshot_id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        session_event_type: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        payload_encoding: Option<PayloadEncoding>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        snapshot_purpose: Option<SnapshotPurpose>,
        #[serde(flatten)]
        rest: JsonMap,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum PayloadEncoding {
    Jsonl,
    AssistantDelta,
}

/// A single-use, worker-memory-only admission for one direct peer.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DaemonWorkerPeerGrant {
    pub grant_id: String,
    pub token: String,
    pub expires_at: String,
    pub purpose: String,
    pub worker_instance_id: String,
    pub active_session_id: String,
    pub issuer_generation: String,
}

/// Commands a direct peer may send before it holds an authenticated role.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "type",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum DaemonPeerCommand {
    PeerAuth {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        grant_id: String,
        token: String,
        worker_instance_id: String,
        purpose: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
}

/// Worker lifecycle commands on the supervisor -> worker channel.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "type",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum DaemonWorkerCommand {
    WorkerAuth {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        token: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        worker_instance_id: Option<String>,
        supervisor_generation: String,
        supervisor_pid: u64,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        supervisor_process_start_id: Option<String>,
        supervisor_socket_path: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    WorkerSubscribe {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        capabilities: Option<Vec<DaemonClientCapability>>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    WorkerUnsubscribe {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    WorkerRegisterPeerTransport {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        grant: DaemonWorkerPeerGrant,
        #[serde(flatten)]
        rest: JsonMap,
    },
    WorkerArchiveAndShutdown {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    WorkerPassivateIdleChildren {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        idle_eviction_minutes: Value,
        now: u64,
        limit: u64,
        #[serde(flatten)]
        rest: JsonMap,
    },
    WorkerDeliverMessage {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        target_active_session_id: String,
        message: String,
        sender: Value,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        delivery_mode: Option<Value>,
        #[serde(flatten)]
        rest: JsonMap,
    },
}

/// The subset of `create` persisted in the durable worker descriptor.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DurableDaemonCreateCommand {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub session_path: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub no_session: Option<bool>,
    #[serde(flatten)]
    pub rest: JsonMap,
}

/// Durable supervisor-side worker record (recovery journal), version 1 or 2.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DaemonWorkerDescriptor {
    pub version: u32,
    pub worker_id: String,
    pub pid: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub process_start_id: Option<String>,
    pub socket_path: String,
    pub recovery_journal_path: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub orphan_process_journal_path: Option<String>,
    pub supervisor_socket_path: String,
    pub authentication_token: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub worker_instance_id: Option<String>,
    pub root_active_session_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub owner_client_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub root_session_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub session_file: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub session_dir: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub telemetry_disabled: Option<bool>,
    pub created_at: String,
    pub updated_at: String,
    pub lifecycle: DaemonWorkerLifecycle,
    pub create_command: DurableDaemonCreateCommand,
    pub consecutive_failures: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stop_requested_at: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub archive_on_stop: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_failure_at: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub last_error: Option<String>,
    #[serde(flatten)]
    pub rest: JsonMap,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn worker_frames_roundtrip() {
        rt::<DaemonWorkerFrameHeader>(
            r#"{"kind":"outbound","requestId":"r","outboundType":"session_event","activeSessionId":"s","payloadEncoding":"jsonl","snapshotPurpose":"attach"}"#,
        );
        rt::<DaemonWorkerCommand>(
            r#"{"type":"worker_auth","token":"t","supervisorGeneration":"g","supervisorPid":1,"supervisorSocketPath":"/s"}"#,
        );
        rt::<DaemonWorkerDescriptor>(
            r#"{"version":2,"workerId":"w","pid":9,"socketPath":"/w.sock","recoveryJournalPath":"/j","supervisorSocketPath":"/s","authenticationToken":"t","rootActiveSessionId":"a","createdAt":"c","updatedAt":"u","lifecycle":"ready","createCommand":{"sessionPath":"/p"},"consecutiveFailures":0}"#,
        );
        rt::<DaemonPeerCommand>(
            r#"{"type":"peer_auth","grantId":"g","token":"t","workerInstanceId":"w","purpose":"session_client"}"#,
        );
    }
}
