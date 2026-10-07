//! The live session's state block: the event sequence, the shown
//! conversation's view (the durable event mirror the attach snapshot and
//! the summaries read), and the worker-side session identity. Every access
//! is through the core mutex; the event bridge emits under it, so the
//! sequence and the view always advance together.

use serde_json::Value;

use super::durable_host::bridge::QueuedInput;
use super::durable_host::ShownView;
use crate::types::SessionActionSnapshot;

pub(crate) struct SessionCore {
    pub(crate) active_session_id: String,
    /// The per-process event generation (resume cursors from another
    /// process replay from the snapshot).
    pub(crate) generation: String,
    pub(crate) last_event_sequence: u64,
    pub(crate) created: bool,
    /// The durable session id (`UUIDv7`); empty before `create`.
    pub(crate) session_id: String,
    /// The durable storage directory; `None` for `noSession` sessions.
    pub(crate) session_dir: Option<std::path::PathBuf>,
    /// The session name (`eukhe.daemon.session` doc mirror).
    pub(crate) session_name: Option<String>,
    /// Whether the Anthropic subscription warning was shown (doc mirror).
    pub(crate) anthropic_warning_shown: bool,
    /// When the session was created here (ISO), for the summary.
    pub(crate) created_at: Option<String>,
    /// The shown conversation's event mirror; `None` before `create`.
    pub(crate) view: Option<ShownView>,
    /// Inputs an `abort` withdrew from the inbox: they stay visible in the
    /// queue and resubmit on `resume_queue` (or the next steered prompt),
    /// like the TS suspended session-input pump.
    pub(crate) suspended: Vec<QueuedInput>,
    pub(crate) cwd: String,
    pub(crate) attached_client_ids: Vec<String>,
    pub(crate) shutdown_requested: bool,
    /// The wall-clock ms of this session's last activity (run end);
    /// zero before any.
    pub(crate) last_activity_ms: u64,
    /// The last broadcast queue snapshot: `session_action_update` fires
    /// only when the projection changed.
    pub(crate) last_action_snapshot: Option<SessionActionSnapshot>,
    /// This session's RLM recursion depth (children run at depth + 1).
    pub(crate) rlm_depth: u32,
    /// `top-level` | `subagent` (summary `runtimeKind`).
    pub(crate) runtime_kind: String,
    /// The subagent runtime identity (create `runtimeMetadata`).
    pub(crate) rlm_child_id: Option<String>,
    pub(crate) parent_active_session_id: Option<String>,
    pub(crate) parent_session_id: Option<String>,
    /// The create command's `childScript` (scripted RLM children).
    pub(crate) child_script: Option<String>,
    /// The service-tier preference (`None` = settings default "auto").
    pub(crate) service_tier: Option<eukhe_types::ai::ServiceTier>,
    /// The ACTIVE tier: the preference clamped to the current model.
    pub(crate) active_service_tier: Option<eukhe_types::ai::ServiceTier>,
    /// The scoped model list `{ model, thinkingLevel? }` the cycler uses.
    pub(crate) scoped_models: Vec<Value>,
}

impl SessionCore {
    pub(crate) fn new(active_session_id: String) -> Self {
        SessionCore {
            active_session_id,
            generation: crate::util::new_display_id(),
            last_event_sequence: 0,
            created: false,
            session_id: String::new(),
            session_dir: None,
            session_name: None,
            anthropic_warning_shown: false,
            created_at: None,
            cwd: String::new(),
            view: None,
            suspended: Vec::new(),
            attached_client_ids: Vec::new(),
            shutdown_requested: false,
            last_activity_ms: 0,
            // The empty projection: a fresh session's first empty snapshot
            // is not an update.
            last_action_snapshot: Some(SessionActionSnapshot::default()),
            rlm_depth: 0,
            runtime_kind: "top-level".to_string(),
            rlm_child_id: None,
            parent_active_session_id: None,
            parent_session_id: None,
            child_script: None,
            service_tier: None,
            active_service_tier: None,
            scoped_models: Vec::new(),
        }
    }

    /// A run is active on the shown conversation.
    pub(crate) fn is_busy(&self) -> bool {
        self.view.as_ref().is_some_and(ShownView::is_busy)
    }

    /// A compaction is running on the shown conversation.
    pub(crate) fn is_compacting(&self) -> bool {
        self.view
            .as_ref()
            .is_some_and(|view| view.translator.mirror().is_compacting())
    }

    /// Whether a run, compaction, or queued input is in flight (the
    /// supervisor-lost exit waits for it to settle).
    pub(crate) fn has_ongoing_work(&self) -> bool {
        self.is_busy()
            || self.is_compacting()
            || self
                .view
                .as_ref()
                .is_some_and(|view| !view.inbox.is_empty())
    }

    /// The session's storage path as the summaries report it
    /// (`sessionFile`): the durable storage directory.
    pub(crate) fn session_file(&self) -> Option<String> {
        self.session_dir
            .as_ref()
            .map(|dir| dir.to_string_lossy().into_owned())
    }

    /// A created session core for command modules' unit tests.
    #[cfg(test)]
    pub(crate) fn test_core(cwd: String) -> Self {
        let mut core = SessionCore::new("test-session".to_string());
        core.created = true;
        core.cwd = cwd;
        core
    }
}
