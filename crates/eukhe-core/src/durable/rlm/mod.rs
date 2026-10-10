//! The `eukhe.rlm` extension: the `ipython` tool backed by one Python kernel
//! per conversation, and the kernel host requests the session answers
//! (`rlm_heartbeat.*`, `mcp.*`, `model.info`, `compact.*`, `refine.*`, plus
//! the embedding's extra handlers). `rlm.*` (children) and `goal.*` (goals)
//! register from their own extensions into the same
//! [`HostRequestRegistry`](super::HostRequestRegistry).
//!
//! Every kernel host request reaches its handler with the durable tool
//! call running the requesting cell ([`super::HostCall::call`]).

mod activity;
mod boundary;
mod host;
mod kernels;
pub(crate) mod refine;
mod tool;

#[cfg(test)]
mod tests;

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_chord::json::JsonError;
use eukhe_durable::harness::define::define_extension;
use eukhe_durable::harness::types::{Agent, Extension, ModelRef, ToolExecutionApi};
use eukhe_durable::types::{ConversationId, EntryDraft};
use eukhe_types::pi_ai::UserContent;
use futures::FutureExt;
use serde_json::Value;

pub(crate) use self::kernels::KernelPool;
use super::entries::custom_entry_draft;
use super::{HostDeps, OpenedSession, ServiceStop};

pub use self::activity::{
    kernel_bash_activity, kernel_factory_activity, release_settled_kernel, transfer_kernel,
    BashActivityAction, BashActivityRequest, KernelActivityError,
};
pub use self::boundary::{BoundaryState, PendingRefine, BOUNDARY_DOC};
pub use self::refine::{refine_now, RefineRequest};
pub use self::tool::{ipython_parameters, IPYTHON_TOOL_NAME};

/// The extension name.
pub const RLM_EXTENSION: &str = "eukhe.rlm";

/// A custom message row the RLM side writes (boot notices, refinement
/// rows), stored as an [`super::entries::CUSTOM_ENTRY`].
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct CustomNotice {
    pub(crate) custom_type: String,
    pub(crate) text: String,
    pub(crate) display: bool,
    pub(crate) details: Option<Value>,
    pub(crate) timestamp: u64,
}

impl CustomNotice {
    pub(crate) fn new(
        custom_type: impl Into<String>,
        text: String,
        display: bool,
        details: Option<Value>,
    ) -> Self {
        Self {
            custom_type: custom_type.into(),
            text,
            display,
            details,
            timestamp: now_millis(),
        }
    }

    pub(crate) fn draft(&self) -> Result<EntryDraft, JsonError> {
        custom_entry_draft(
            self.custom_type.clone(),
            UserContent::Text(self.text.clone()),
            self.display,
            self.details.clone(),
            self.timestamp,
        )
    }
}

#[expect(
    clippy::cast_possible_truncation,
    reason = "milliseconds since the epoch fit in u64 for the next 500 million years"
)]
pub(crate) fn now_millis() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_millis() as u64)
        .unwrap_or_default()
}

/// What the RLM extension shares between its tool, hooks, and host
/// handlers. Host handlers hold it weakly: the registry lives in
/// [`HostDeps`], which this holds.
pub(crate) struct RlmRuntime {
    pub(crate) deps: Arc<HostDeps>,
    pub(crate) kernels: Arc<KernelPool>,
}

impl RlmRuntime {
    /// The conversation a host request targets (the requesting cell's
    /// call, else the root) and its resolved agent.
    pub(crate) async fn target(
        &self,
        call: Option<&Arc<dyn ToolExecutionApi>>,
        cx: &Context,
    ) -> anyhow::Result<(ConversationId, Agent)> {
        if let Some(call) = call {
            let agent = call.agent(cx).await?;
            return Ok((call.conversation_id(), (*agent).clone()));
        }
        let root = self
            .deps
            .harness
            .root()
            .ok_or_else(|| anyhow::anyhow!("the session is closed"))?;
        let agent = root.agent(cx).await?;
        Ok((root.id(), agent))
    }

    /// The catalog model of `model`, when the collection knows it.
    pub(crate) fn model(&self, model: &ModelRef) -> Option<eukhe_types::pi_ai::Model> {
        self.deps.models.get_model(&model.provider, &model.model_id)
    }
}

/// The background context host handlers and services run on.
pub(crate) fn background() -> Context {
    eukhe_chord::context::BACKGROUND_CONTEXT.clone()
}

/// The `eukhe.rlm` extension of a session: the `ipython` tool, the
/// run-boundary refinement hook, and the RLM host-request handlers (registered
/// into `deps.host_requests` now). At open it prewarms the main
/// conversation's kernel (the user-facing one: the root unless a fork or
/// tree move made another conversation the main) when the session asks for
/// it or a namespace snapshot exists; at close it disposes every kernel
/// with a final snapshot.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let runtime = Arc::new(RlmRuntime {
        deps: Arc::clone(deps),
        kernels: Arc::new(KernelPool::new(deps)),
    });
    // The daemon's out-of-band kernel lanes reach the pool through the deps
    // (weakly: the runtime owns the pool and holds the deps).
    let _first_extension_wins = deps.rlm_kernels.set(Arc::downgrade(&runtime.kernels));
    host::register(&runtime);
    let refine_allowed = boundary::register(&runtime);
    let service_runtime = Arc::clone(&runtime);
    deps.add_service(Box::new(move |opened: OpenedSession| {
        async move {
            service_runtime.kernels.prewarm(opened.main.id());
            let stop: ServiceStop = Box::new(move || {
                async move { service_runtime.kernels.dispose_all().await }.boxed()
            });
            Ok(Some(stop))
        }
        .boxed()
    }));
    let mut hooks = Vec::new();
    if refine_allowed {
        hooks.push(refine::refine_hook(&runtime));
    }
    define_extension(Extension {
        tools: vec![tool::ipython_tool(&runtime)],
        hooks,
        ..Extension::named(RLM_EXTENSION)
    })
}
