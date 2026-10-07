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
mod progress;
mod registry;
mod requests;
mod task;
mod wire;

#[cfg(test)]
mod tests;

use std::sync::Arc;

use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::Extension;
use eukhe_pi_ai::models::Models;

pub use commands::{
    cancel_child, delete_inactive_child, find_child, list_children, DeleteChildOutcome,
    RlmChildRecord,
};
pub use depth::{read_max_depth_override, set_max_depth_override};
pub use host::{
    NoRlmChildren, RlmChildActivityKind, RlmChildCancelRequest, RlmChildDeleteRequest,
    RlmChildIdentity, RlmChildListing, RlmChildObservation, RlmChildPromptRequest,
    RlmChildRunState, RlmChildSession, RlmChildSpawnRequest, RlmChildWaitRequest,
    RlmCreateSessionHandle, RlmCreateSessionRequest, RlmHostFuture, RlmSubagentHost,
};
pub use registry::has_unsettled_children;
pub use wire::{
    RlmChildResult, RlmDeleteSubagentResult, RlmSpawnHandle, RlmSubagentActivity, RlmSubagentEntry,
};

use super::deps::{HarnessCell, HostDeps, HostRequestRegistry};
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
}

/// Inputs of [`Children::new`].
pub(crate) struct ChildrenConfig {
    pub(crate) host: Option<Arc<dyn RlmSubagentHost>>,
    pub(crate) parent_session_id: String,
    pub(crate) rlm_depth: u32,
    pub(crate) rlm_max_depth: u32,
    pub(crate) harness: HarnessCell,
    pub(crate) models: Models,
}

impl Children {
    pub(crate) fn new(config: ChildrenConfig) -> Arc<Self> {
        let has_runtime = config.host.is_some();
        let services = Arc::new(ChildrenServices {
            host: config.host.unwrap_or_else(|| Arc::new(NoRlmChildren)),
            parent_session_id: config.parent_session_id,
            rlm_depth: config.rlm_depth,
            rlm_max_depth: config.rlm_max_depth,
        });
        let task = child_task(&services);
        Arc::new(Self {
            services,
            has_runtime,
            task,
            harness: config.harness,
            models: config.models,
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
    })
    .install(&deps.host_requests)
}
