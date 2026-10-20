//! `eukhe.children`: RLM child sessions on the durable Harness.
//!
//! Children stay separate supervised sessions (the daemon's
//! [`RlmSubagentHost`]); what the parent owes a child lives in the parent's
//! durable state: one background `eukhe.rlm.child` task per child (spawn,
//! prompt, settle watch, report) and the `eukhe.rlm.children` registry
//! document the `rlm.*` kernel host requests read. A restarted parent
//! resumes every child task where it stopped, so a report owed for a child
//! still running at the crash is delivered exactly once.

mod commands;
mod depth;
mod host;
mod notice;
pub mod parent_notice;
mod progress;
mod registry;
mod rename;
mod requests;
mod task;
mod watch;
mod wire;
mod work;

#[cfg(test)]
mod tests;

use std::sync::Arc;

use eukhe_ai::models::Models;
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::Extension;

pub use commands::{
    cancel_child, delete_inactive_child, find_child, list_children, mark_child_replied,
    DeleteChildOutcome, RlmChildRecord,
};
pub use depth::{read_max_depth_override, set_max_depth_override};
pub use host::{
    NoRlmChildren, RlmChildActivityKind, RlmChildCancelRequest, RlmChildDeleteRequest,
    RlmChildHandbackRequest, RlmChildIdentity, RlmChildListing, RlmChildObservation,
    RlmChildOutcome, RlmChildPromptRequest, RlmChildRunState, RlmChildSession,
    RlmChildSpawnRequest, RlmChildWaitRequest, RlmCreateSessionHandle, RlmCreateSessionRequest,
    RlmHostFuture, RlmRenameRequest, RlmRenameTarget, RlmSpawnCapacity, RlmSubagentHost,
    RLM_CHILD_ANSWER_MAX_BYTES,
};
pub use registry::{
    has_unsettled_children, unsettled_child_tasks, unsettled_children, UnsettledChildren,
};
/// A test of another module (`zoom("Name")`) registers a child row.
#[cfg(test)]
pub(crate) use registry::{tx_put_row, ChildRow, ChildStatus};
pub use wire::{
    RlmChildResult, RlmDeleteSubagentResult, RlmSpawnHandle, RlmSubagentActivity, RlmSubagentEntry,
};
pub use work::WorkLedger;

use super::deps::{HarnessCell, HostDeps, HostRequestRegistry, ProgressNoteSink, SessionClosing};
use crate::durable::observe::semantic_edges::SemanticEdgeRecorder;
use crate::durable::settings::EukheSettings;
use task::{child_task, ChildTask, ChildrenServices};

/// The extension name.
pub const EXTENSION_NAME: &str = "eukhe.children";

/// The children services of one session, shared by the `rlm.*` handlers.
pub(crate) struct Children {
    services: Arc<ChildrenServices>,
    /// Whether the session has a real child runtime (a daemon host).
    has_runtime: bool,
    task: ChildTask,
    harness: HarnessCell,
    models: Models,
    /// Told every accepted progress note of this session.
    progress_note: Option<ProgressNoteSink>,
}

/// Inputs of [`Children::new`].
pub(crate) struct ChildrenConfig {
    pub(crate) host: Option<Arc<dyn RlmSubagentHost>>,
    pub(crate) parent_session_id: String,
    pub(crate) rlm_depth: u32,
    pub(crate) rlm_max_depth: u32,
    pub(crate) harness: HarnessCell,
    pub(crate) models: Models,
    /// The session's semantic-edge recorder: a spawn anchors to the
    /// parent's in-flight request id, and a child's return is claimed on
    /// the ledger before its notice.
    pub(crate) semantic_edges: Option<Arc<SemanticEdgeRecorder>>,
    pub(crate) progress_note: Option<ProgressNoteSink>,
    pub(crate) settings: Arc<EukheSettings>,
    /// The session's closing gate: a closing parent admits no report.
    pub(crate) closing: SessionClosing,
}

impl Children {
    pub(crate) fn new(config: ChildrenConfig) -> Arc<Self> {
        let has_runtime = config.host.is_some();
        let services = Arc::new(ChildrenServices {
            host: config.host.unwrap_or_else(|| Arc::new(NoRlmChildren)),
            parent_session_id: config.parent_session_id,
            rlm_depth: config.rlm_depth,
            rlm_max_depth: config.rlm_max_depth,
            semantic_edges: config.semantic_edges,
            closing: config.closing,
            settings: config.settings,
            polled: std::sync::Mutex::default(),
        });
        let task = child_task(&services);
        Arc::new(Self {
            services,
            has_runtime,
            task,
            harness: config.harness,
            models: config.models,
            progress_note: config.progress_note,
        })
    }

    /// The extension carrying the `eukhe.rlm.child` task; registers the
    /// `rlm.*` handlers onto `host_requests`.
    pub(crate) fn install(self: &Arc<Self>, host_requests: &HostRequestRegistry) -> Arc<Extension> {
        requests::register(host_requests, self);
        define_extension(Extension {
            tasks: vec![self.task.erase()],
            ..Extension::named(EXTENSION_NAME)
        })
    }
}

/// The `eukhe.children` extension of a session: the `eukhe.rlm.child` task
/// and the `rlm.*` host requests (registered on `deps.host_requests`).
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    Children::new(ChildrenConfig {
        host: deps.children.clone(),
        parent_session_id: deps.session_id.clone(),
        rlm_depth: deps.role.rlm_depth,
        rlm_max_depth: deps.role.rlm_max_depth,
        harness: deps.harness.clone(),
        models: deps.models.clone(),
        semantic_edges: Some(Arc::clone(&deps.semantic_edges)),
        progress_note: deps.progress_note.clone(),
        settings: Arc::clone(&deps.settings),
        closing: deps.closing.clone(),
    })
    .install(&deps.host_requests)
}
