//! Client commands: envelope, frame types, and the full `DaemonCommand` union.
//! Wire shapes match the TS daemon protocol exactly.

#[cfg(test)]
use super::rt;
use super::{
    AgentMessage, DaemonClientCapability, DaemonClientId, DaemonCommandId, DaemonProtocolInfo,
    DaemonResumeCursor, Deserialize, JsonMap, Serialize, Value,
};

// ---------------------------------------------------------------------------
// Commands (client/worker -> supervisor/worker)
// ---------------------------------------------------------------------------

/// `type: "command"` envelope wrapping a [`DaemonCommand`].
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DaemonCommandEnvelope {
    /// Fixed `"command"` frame tag.
    #[serde(rename = "type")]
    pub frame_type: DaemonCommandFrameType,
    pub id: DaemonCommandId,
    pub protocol: DaemonProtocolInfo,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub client_id: Option<DaemonClientId>,
    pub command: DaemonCommand,
}

/// Frame tag of [`DaemonCommandEnvelope`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum DaemonCommandFrameType {
    #[serde(rename = "command")]
    Command,
}

/// A bare command or a command envelope, both accepted on one socket line.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum DaemonCommandWire {
    Command(DaemonCommand),
    Envelope(DaemonCommandEnvelope),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum StreamingBehavior {
    Steer,
    FollowUp,
}

/// The rows a `list_agent_peers` answers with.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum AgentPeerScope {
    /// Every other live connected worker's root row (the TS peer roster).
    Live,
    /// Every supervisor roster row — live, seeded passivated children,
    /// and the requester's own row — the source of the family mesh.
    Roster,
}

/// The class of a model request asking for provider admission
/// ([`DaemonCommand::ProviderAdmissionAcquire`]). Interactive requests are
/// served in arrival order; a background request is admitted only while
/// no interactive request of its provider holds or waits for a slot, and
/// the next interactive request that comes preempts it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum AdmissionPriority {
    /// A session's model request (root turns and subagents alike).
    #[default]
    Interactive,
    /// The chat-memory compactor's.
    Background,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DaemonSessionLifecycle {
    Resident,
    ClientOwned,
}

/// `prompt`/`steer`/`follow_up`-family input payload.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PromptInput {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub content: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub images: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub streaming_behavior: Option<StreamingBehavior>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub queue_if_busy: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub expand_prompt_templates: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub source: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub agent_message_id: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub custom_message: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub queue_key: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub prefix_messages: Option<Value>,
    /// Unique only when the caller needs cancellable pre-ownership admission.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub admission_id: Option<String>,
    /// One-shot capability ONLY the daemon's own RLM children delivery
    /// mints (`child_status_notices`, same worker process as the queue
    /// admission): the parent worker accepts a reserved child-status
    /// custom row exclusively with a live mint. Never a client field —
    /// a caller-supplied value can never name a live mint, so the
    /// reserved-kind intake rejects it all the same.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rlm_notice_nonce: Option<String>,
    /// The live session whose user sent this prompt as an `@name` message
    /// (Rust-native): the run's final answer returns there as a durable
    /// `agent_reply` row (shown to the user, logged to chat memory, never
    /// a turn of its own).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reply_to: Option<String>,
}

/// Client commands, tagged by `type`. Every variant also carries `id` (when
/// sent as a bare command) and a catch-all for unknown fields, so wire
/// round-trips are lossless across schema revisions.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(
    tag = "type",
    rename_all = "snake_case",
    rename_all_fields = "camelCase"
)]
pub enum DaemonCommand {
    List {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        all: Option<bool>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cwd: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        session_dir: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        include_client_owned: Option<bool>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// `list_saved_sessions` (session-addressed or cwd-addressed forms share
    /// this shape; unaddressed fields stay absent).
    ListSavedSessions {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cwd: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        session_dir: Option<String>,
        #[serde(default)]
        scope: Value,
        #[serde(flatten)]
        rest: JsonMap,
    },
    ListAgentPeers {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        /// The requester's worker token; optional on the wire (the TS
        /// supervisor arm reads an absent token as an authentication
        /// failure, not a parse one).
        #[serde(default)]
        worker_token: String,
        /// Which rows answer; absent is [`AgentPeerScope::Live`].
        #[serde(default, skip_serializing_if = "Option::is_none")]
        scope: Option<AgentPeerScope>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetDirectWorkerTransport {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// The supervisor's process-level liveness verdict on the worker that
    /// hosts one session ([`super::WorkerLiveness`]), answered by the
    /// supervisor from the worker's pid without routing to the worker: a
    /// parent whose requests to a child fail asks this before it treats
    /// the child as gone.
    GetWorkerLiveness {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Worker-to-worker peer ticket (thin-supervisor stage 3): a worker
    /// acting for its session asks the supervisor to mint a single-use
    /// `worker`-purpose grant for a target worker's direct socket so the
    /// delivery bypasses the supervisor's route plane. Authenticated by
    /// the requester's worker token, like `list_agent_peers`.
    GetWorkerPeerTransport {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        worker_token: String,
        target_active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    RosterSubscribe {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Worker -> supervisor idle-passivation request (TS's whole-worker
    /// idle eviction, worker-driven): a parent-owned child worker whose
    /// park arm proved the idle state and whose idle clock crossed the
    /// `idleEvictionMinutes` threshold asks the supervisor to run the
    /// graceful stop (`stop_worker`: tombstone, routed shutdown, registry
    /// retirement, roster passivation). The supervisor verifies the worker
    /// token and the parent-owned descriptor before stopping. Clients
    /// never send this command; it rides the worker's supervisor link.
    WorkerIdlePassivation {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        worker_token: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        idle_minutes: Option<u64>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Worker -> supervisor roster delta (the Rust-native form of the TS
    /// `roster_delta` worker frame): the worker pushes its slim session
    /// summary so the supervisor's roster tracks live status without
    /// polling. Authenticated by the worker token, like `worker_register`.
    WorkerRosterDelta {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        worker_token: String,
        summary: Value,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        removed: Option<Vec<String>>,
        /// The worker's monotonic roster-delta sequence: the per-request
        /// supervisor links deliver deltas unordered, so the supervisor
        /// drops a stale delta (a newer one already applied) instead of
        /// letting a delayed older snapshot overwrite it. The sequence is
        /// stamped under the worker's push-order lock together with the
        /// snapshot it describes, so sequence order is snapshot order.
        /// Absent means unsequenced (always applied).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        sequence: Option<u64>,
        /// The sending worker process instance: a replacement process
        /// reuses the resident worker id but restarts its sequence, so the
        /// supervisor's stale-delta gate names the current generation in
        /// one bounded slot per worker (flipped at the replacement's
        /// registration) — a predecessor's in-flight deltas drop on the
        /// generation mismatch.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        worker_instance_id: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Worker -> supervisor provider admission (Rust-native): one model
    /// request of the worker's session (or of the chat-memory compactor the
    /// worker runs) asks for a slot of `provider_id` (`providerMaxInFlight`)
    /// in its `priority` class. The supervisor answers once the slot is
    /// taken (a `provider_admission_queued` frame first when it has to
    /// wait) or the queue is full, and holds the slot until this
    /// connection closes. A background slot an interactive request takes
    /// back gets a `provider_admission_preempted` frame. Authenticated by
    /// the worker token.
    ProviderAdmissionAcquire {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        worker_token: String,
        provider_id: String,
        /// Absent: interactive.
        #[serde(default)]
        priority: AdmissionPriority,
        #[serde(flatten)]
        rest: JsonMap,
    },
    RosterUnsubscribe {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Create {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        session_path: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        continue_recent: Option<bool>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        no_session: Option<bool>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        name: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        config: Option<Value>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        runtime_metadata: Option<Value>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        lifecycle: Option<DaemonSessionLifecycle>,
        /// Allowlisted client env vars (`env`), carried on create only.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        env: Option<std::collections::BTreeMap<String, String>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        launch_env: Option<std::collections::BTreeMap<String, String>>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Attach {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        client_id: Option<DaemonClientId>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        capabilities: Option<Vec<DaemonClientCapability>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        resume_cursor: Option<DaemonResumeCursor>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        recovery_config: Option<Value>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        env: Option<std::collections::BTreeMap<String, String>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        launch_env: Option<std::collections::BTreeMap<String, String>>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Reattach {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        target_active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        client_id: Option<DaemonClientId>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        capabilities: Option<Vec<DaemonClientCapability>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        resume_cursor: Option<DaemonResumeCursor>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        recovery_config: Option<Value>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        env: Option<std::collections::BTreeMap<String, String>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        launch_env: Option<std::collections::BTreeMap<String, String>>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Detach {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    CompleteOwnedSession {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    PromoteOwnedSession {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Kill {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Rename {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        name: String,
        /// Who directed the rename (`renamedBy` on the wire, TS
        /// `AgentFamilyRelationship` — only `"parent"` is sent): set when a
        /// parent session renames one of its direct children, so the
        /// renamed session's transcript notice can name it.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        renamed_by: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Prompt {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        message: String,
        #[serde(flatten)]
        input: PromptInput,
        #[serde(flatten)]
        rest: JsonMap,
    },
    CancelPromptAdmission {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        admission_id: String,
        /// Cancel session-owned work too when it has not started delivery.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cancel_owned: Option<bool>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    PromptAndWait {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        message: String,
        #[serde(flatten)]
        input: PromptInput,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Steer {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        message: String,
        #[serde(flatten)]
        input: PromptInput,
        #[serde(flatten)]
        rest: JsonMap,
    },
    FollowUp {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        message: String,
        #[serde(flatten)]
        input: PromptInput,
        #[serde(flatten)]
        rest: JsonMap,
    },
    RestoreNextTurn {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        messages: Vec<AgentMessage>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    RestoreActions {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        snapshot: Value,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AppendCustomMessage {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        message: Value,
        #[serde(flatten)]
        rest: JsonMap,
    },
    ResumeQueue {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SendMessage {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        target_active_session_id: String,
        message: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        from_active_session_id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        agent_origin: Option<bool>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        delivery_mode: Option<Value>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AgentMessagesStatus {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AgentMessagesPause {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AgentMessagesResume {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AgentMessagesClear {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Abort {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// `abort_and_send_queued` (schema 29, capability-gated in TS): abort
    /// the active run and deliver the visible queued steering batch at the
    /// turn boundary; a plain abort when no steering is queued (TS
    /// `AgentSession.abortAndSendQueued`).
    AbortAndSendQueued {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    StartSideQuestion {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        // Optional on the wire (the TS runtime validates nothing at
        // parse; a routing miss answers before the payload is read).
        #[serde(default)]
        side_question_id: String,
        #[serde(default)]
        question: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        previous_turns: Option<Value>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AbortSideQuestion {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        // Optional on the wire, like `start_side_question`'s payload.
        #[serde(default)]
        side_question_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    ExecuteBash {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        command: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        exclude_from_context: Option<bool>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        transient: Option<bool>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        run_id: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AbortBash {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native extension, advertised by the `kernel_bash_activity` capability.
    ListKernelBash {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    TailKernelBash {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        activity_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        lines: Option<u32>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    KillKernelBash {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        activity_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// The `/factory` view's bridge lane over the session kernel's factory
    /// executor (`graph`/`status`/`watch`/`run`/`stop`/`resume`).
    /// Rust-native extension, advertised by the `factory_activity` capability.
    FactoryActivity {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        action: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        run_id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        spec_id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        timeout_ms: Option<u64>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    CancelRlmChild {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        child_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    DeleteRlmSubagent {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        child_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    WaitForIdle {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        /// Also hold until every RLM child run of the session settled
        /// (the `wait_for_headless_completion` barrier of the same name).
        #[serde(default, skip_serializing_if = "Option::is_none")]
        wait_for_rlm_quiescence: Option<bool>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    WaitForHeadlessCompletion {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        wait_for_rlm_quiescence: Option<bool>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetSessionHeader {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetState {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetConnectionState {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetMessages {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetRlmChildren {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetSessionStats {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetContextTree {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetCommands {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetResourceSnapshot {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetMcpConnections {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// The inline paste flow: install a pasted static token for one
    /// pasteable catalog service (`server`), binding it to the service
    /// endpoint and verifying with a real MCP handshake.
    SetMcpStaticToken {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        server: String,
        token: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Remove one MCP connection: its credential and its connection record
    /// (the durable endpoint pin), in one step.
    RemoveMcpConnection {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        server: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    ReplaceAcpMcpServers {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        owner_id: String,
        servers: Value,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetModelCatalog {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetAvailableModels {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetQueue {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    MutateQueuedMessage {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        lane: Value,
        index: u64,
        expected_text: String,
        mutation: Value,
        #[serde(flatten)]
        rest: JsonMap,
    },
    ClearQueue {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AbortAndClearQueue {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AcquireSessionInputPause {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        lease_key: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    ReleaseSessionInputPause {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        pause_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    CronList {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        include_inactive: Option<bool>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    HeartbeatsList {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    HeartbeatManage {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        job_id: String,
        action: Value,
        #[serde(flatten)]
        rest: JsonMap,
    },
    CronAdd {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        schedule: String,
        prompt: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        promote_owned_session: Option<bool>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    CronCancel {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        job_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    HeartbeatGet {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    HeartbeatSet {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        schedule: String,
        prompt: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        delivery_mode: Option<Value>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        promote_owned_session: Option<bool>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    HeartbeatUpdate {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        action: Value,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SetModel {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        provider: String,
        model_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    CycleModel {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        direction: Option<CycleDirection>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SetScopedModels {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        scoped_models: Value,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SetThinkingLevel {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        // Optional on the wire (the TS runtime reads it after routing).
        #[serde(default)]
        level: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SetServiceTier {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        service_tier: Option<crate::ai::ServiceTier>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    CycleThinkingLevel {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SetTransport {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        transport: crate::ai::Transport,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SetSteeringMode {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        mode: Value,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SetFollowUpMode {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        mode: Value,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SetAutoCompaction {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        enabled: bool,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SetAutoRetry {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        enabled: bool,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Run a cvar command list (`eukhe_types::cvar`) for the session:
    /// its own sets and aliases, or with `global` the global config.cfg
    /// (`set` / `toggle` only). Answers `{ values, errors }`; a rejected
    /// command fails with `data: { kind, id?, message }` (`CvarFailureData`).
    Cvar {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        line: String,
        #[serde(default)]
        global: bool,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Write the session's own sets of persisting cvars to its
    /// `agents/<agent>.cfg`.
    CvarSave {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Compact {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        custom_instructions: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Refine {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        instructions: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        rollback_id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        global: Option<bool>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AbortCompaction {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AbortBranchSummary {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AbortRetry {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    ExecuteBashAndWait {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        command: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Reload {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    NewSession {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        parent_session: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SwitchSession {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        session_path: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cwd_override: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Fork {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        entry_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        position: Option<ForkPosition>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    NavigateTree {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        target_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        summarize: Option<bool>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        custom_instructions: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        replace_instructions: Option<bool>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        label: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    ImportJsonl {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        input_path: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        cwd_override: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    ExportHtml {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        output_path: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    ExportJsonl {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        output_path: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SetSessionName {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        name: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        worker_token: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetRlmMaxDepthStatus {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SetRlmMaxDepth {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        max_depth: u64,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        global: Option<bool>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    RenameSavedSession {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        session_path: String,
        name: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    DeleteSavedSession {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        active_session_id: Option<String>,
        session_path: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetSessionContext {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetSessionTree {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetUserMessagesForForking {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetLastAssistantText {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native: the session's run outcome, read from its durable
    /// state (its run in flight, its last run's terminal, its pending
    /// background jobs); the parent's child-settle watch reads it.
    GetRunOutcome {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetSystemPrompt {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native extension, advertised by the `chat_view` capability:
    /// the chat memory's current view, for the interactive client's
    /// startup block (reply: [`super::ChatViewReply`]).
    GetChatView {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native extension, advertised by the `memory` capability: the
    /// chat memory's status and view, or one zoom into it, for `/memory`
    /// and the status gauge (reply: [`super::MemoryReply`]).
    GetMemory {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        zoom: Option<super::MemoryZoom>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native extension, advertised by the `memory_tree` capability:
    /// one level of the chat memory's tree -- the view's lines, or what the
    /// line `node` opens into -- each line dated and with its message kinds,
    /// for the `/memory` tree and the dashboard (reply:
    /// [`super::MemoryTreeReply`]).
    GetMemoryTree {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        node: Option<super::MemoryZoom>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native extension, advertised by the `state_tree` capability:
    /// the session state tree, whole, or the records after the client
    /// cursor `since` (reply: [`super::StateTreeReply`]).
    GetStateTree {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        since: Option<u64>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native extension, advertised by the `state_tree` capability:
    /// subscribe this connection to the session state tree. The reply is
    /// the `get_state_tree` reply (the snapshot, or the records after
    /// `since`); from then on the connection gets each new record batch as
    /// a `state_tree_update` frame (reply: [`super::StateTreeReply`]).
    SubscribeStateTree {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        since: Option<u64>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native extension, advertised by the `state_tree` capability:
    /// end this connection's state tree subscription for the session. A
    /// closed connection ends its subscriptions too.
    UnsubscribeStateTree {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native extension, advertised by the `state_tree` capability:
    /// what a rewind of the state tree to `cursor` does (reply:
    /// [`super::StateRewindPlanReply`]).
    GetStateRewindPlan {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        cursor: u64,
        #[serde(flatten)]
        rest: JsonMap,
    },
    GetToolDefinition {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        name: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    SetSessionEntryLabel {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        entry_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        label: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native client command (operator directive 2026-09-29): the
    /// interactive client's report that it just drew the Anthropic
    /// subscription ban-risk warning — the worker persists the session's
    /// once-per-lifecycle marker row so a reattach, a resume, or a worker
    /// replacement of the same session skips the warning (the TS gate is
    /// per interactive-mode instance, so the TS protocol has no
    /// counterpart; an older daemon rejects the frame and the client
    /// degrades to its per-instance gate).
    MarkAnthropicWarningShown {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native worker command: a subagent that messaged another
    /// non-root agent of its family asks the family root's worker to show
    /// the exchange (the root emits the display-only `agent_relay` session
    /// event; never model input, never chat memory).
    AgentRelay {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        /// The family root's live session.
        active_session_id: String,
        from: String,
        to: String,
        text: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Rust-native worker command: an agent's final answer to a user's
    /// `@name` message, delivered to the session the user sent it from.
    /// The session commits it as an `agent_reply` row once per `reply_id`
    /// (a redelivery is a no-op); it never starts a turn.
    AgentReply {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        /// The session the user's message came from.
        active_session_id: String,
        /// The answering agent's display name.
        from: String,
        text: String,
        /// The owed reply's durable id (the row's dedupe key).
        reply_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    AckResult {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        command_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    RetryWorker {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Restart {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    Shutdown {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        force: Option<bool>,
        #[serde(flatten)]
        rest: JsonMap,
    },
    /// Session-worker self-registration (worker -> supervisor). A booting
    /// worker presents its supervisor-issued identity so the supervisor can
    /// rebuild its roster; the same command re-registers the worker after a
    /// supervisor restart (the token was issued when the supervisor spawned
    /// or adopted the worker, so only the real worker can present it).
    WorkerRegister {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        id: Option<String>,
        active_session_id: String,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        session_id: Option<String>,
        socket_path: String,
        worker_instance_id: String,
        token: String,
        pid: u64,
        #[serde(flatten)]
        rest: JsonMap,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum CycleDirection {
    Forward,
    Backward,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ForkPosition {
    Before,
    At,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prompt_family_roundtrip() {
        rt::<DaemonCommand>(
            r#"{"type":"steer","activeSessionId":"s1","message":"m","content":[{"type":"text","text":"x"}],"streamingBehavior":"steer","queueKey":"q","admissionId":"a1"}"#,
        );
        rt::<DaemonCommand>(
            r#"{"type":"cancel_prompt_admission","activeSessionId":"s1","admissionId":"a1","cancelOwned":true}"#,
        );
    }

    #[test]
    fn worker_register_roundtrip() {
        rt::<DaemonCommand>(
            r#"{"type":"worker_register","activeSessionId":"abc123def456","sessionId":"s-uuid","socketPath":"/tmp/w.sock","workerInstanceId":"inst-1","token":"tok","pid":4242}"#,
        );
    }

    #[test]
    fn mark_anthropic_warning_shown_roundtrip() {
        rt::<DaemonCommand>(r#"{"type":"mark_anthropic_warning_shown","activeSessionId":"s1"}"#);
    }

    #[test]
    fn agent_relay_and_roster_scope_roundtrip() {
        rt::<DaemonCommand>(
            r#"{"type":"agent_relay","activeSessionId":"root","from":"scout","to":"builder","text":"hi"}"#,
        );
        rt::<DaemonCommand>(r#"{"type":"list_agent_peers","workerToken":"t","scope":"roster"}"#);
    }

    #[test]
    fn agent_reply_and_prompt_reply_to_roundtrip() {
        rt::<DaemonCommand>(
            r#"{"type":"agent_reply","activeSessionId":"root","from":"alpha","text":"42","replyId":"r1"}"#,
        );
        rt::<DaemonCommand>(
            r#"{"type":"prompt","activeSessionId":"alpha","message":"what number?","replyTo":"root"}"#,
        );
    }

    #[test]
    fn get_chat_view_roundtrip() {
        rt::<DaemonCommand>(r#"{"type":"get_chat_view","activeSessionId":"s1"}"#);
    }

    #[test]
    fn get_memory_roundtrip() {
        rt::<DaemonCommand>(r#"{"type":"get_memory","activeSessionId":"s1"}"#);
        rt::<DaemonCommand>(
            r#"{"type":"get_memory","activeSessionId":"s1","zoom":{"id":40,"count":8}}"#,
        );
    }

    #[test]
    fn get_memory_tree_roundtrip() {
        rt::<DaemonCommand>(r#"{"type":"get_memory_tree","activeSessionId":"s1"}"#);
        rt::<DaemonCommand>(
            r#"{"type":"get_memory_tree","activeSessionId":"s1","node":{"id":40,"count":8}}"#,
        );
    }

    #[test]
    fn get_state_tree_and_rewind_plan_roundtrip() {
        rt::<DaemonCommand>(r#"{"type":"get_state_tree","activeSessionId":"s1"}"#);
        rt::<DaemonCommand>(r#"{"type":"get_state_tree","activeSessionId":"s1","since":12}"#);
        rt::<DaemonCommand>(
            r#"{"type":"get_state_rewind_plan","activeSessionId":"s1","cursor":0}"#,
        );
        rt::<DaemonCommand>(r#"{"type":"subscribe_state_tree","activeSessionId":"s1","since":3}"#);
        rt::<DaemonCommand>(r#"{"type":"unsubscribe_state_tree","activeSessionId":"s1"}"#);
    }
}
