//! `rlm.*` reply shapes (strict `snake_case`, parsed by the Python `rlm`
//! module); ported from `session_engine/rlm_host.rs`.

/// `rlm.spawn` handle returned once the child task is admitted.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct RlmSpawnHandle {
    pub rlm_child_id: String,
    pub name: String,
    pub session_dir: String,
    pub model: String,
}

/// One roster row of `rlm.list_subagents`.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct RlmSubagentEntry {
    pub rlm_child_id: String,
    pub active_session_id: Option<String>,
    pub session_id: Option<String>,
    pub session_name: String,
    pub session_dir: String,
    /// `running` | `completed` | `error` | `cancelled`.
    pub status: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub activity: Option<RlmSubagentActivity>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool_use_count: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub duration_ms: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub answer_preview: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub replied_since_task: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub progress_note: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_activity_at: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub activity_stale_ms: Option<u64>,
}

/// Live child activity projected onto the roster row.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct RlmSubagentActivity {
    /// `waiting` | `writing` | `executing`.
    pub kind: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool_name: Option<String>,
}

/// `rlm.delete_subagent` reply: the deleted row plus the outcome.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct RlmDeleteSubagentResult {
    pub subagent: RlmSubagentEntry,
    /// `deleted`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub outcome: Option<&'static str>,
}

/// One `rlm.collect` result envelope.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize)]
pub struct RlmChildResult {
    pub rlm_child_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub session_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub session_dir: Option<String>,
    /// `queued` | `running` | `done` | `error` | `cancelled`.
    pub status: &'static str,
    pub settled: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub answer_preview: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub duration_ms: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tool_use_count: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub replied_since_task: Option<bool>,
}
