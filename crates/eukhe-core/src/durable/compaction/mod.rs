//! `eukhe.compaction`: the old engine's compaction behaviors on the
//! durable Harness:
//!
//! - `before_compact` supplies eukhe's own summary (the old prompts,
//!   serializer, auxiliary model, update mode, recent-state anchor,
//!   harness-digest block, and `[compaction-summary]` wrapper) and streams
//!   its text deltas to the session's [`SummaryDeltaSink`]; chat-memory
//!   roots decline (`summary`).
//! - The post-commit observer (`observer`) records `compaction_outcome`
//!   rows when `pi.compaction` tasks settle (idempotent per task id),
//!   appends the post-compaction `ipython_state` notice when a kernel
//!   survived, and arms the compact-trigger auto-refine (`autorefine`),
//!   serviced once the conversation goes idle.

mod autorefine;
pub(crate) mod head;
pub use head::summary_body;
mod observer;
mod summary;
#[cfg(test)]
mod tests;

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_durable::harness::define::{define_extension, hook};
use eukhe_durable::harness::types::{CompactionHooks, Extension};
use eukhe_durable::harness::COMPACTION_TASK;

pub(crate) use super::HostDeps;

/// The extension name.
pub const COMPACTION_EXTENSION: &str = "eukhe.compaction";

/// The kind of the durable compaction summary entry (`pi.compaction`).
pub(crate) const COMPACTION_ENTRY_KIND: &str = "pi.compaction";

/// What the `eukhe.compaction` extension shares between its hook and its
/// observer: the session's [`HostDeps`] and the compact-trigger auto-refine
/// state.
pub(crate) struct CompactionRuntime {
    pub(crate) deps: Arc<HostDeps>,
    pub(crate) autorefine: autorefine::AutoRefineState,
}

/// The `eukhe.compaction` extension of a session: the `before_compact`
/// hook over the built-in compaction task and the post-commit observer
/// started at open.
#[must_use]
pub fn extension(deps: &Arc<HostDeps>) -> Arc<Extension> {
    let runtime = Arc::new(CompactionRuntime {
        deps: Arc::clone(deps),
        autorefine: autorefine::AutoRefineState::default(),
    });
    let observer_runtime = Arc::clone(&runtime);
    deps.add_service(Box::new(move |opened| {
        observer::start(observer_runtime, opened)
    }));
    define_extension(Extension {
        hooks: vec![hook(
            &*COMPACTION_TASK,
            CompactionHooks {
                before_compact: Some(summary::before_compact_hook(&runtime)),
            },
        )],
        ..Extension::named(COMPACTION_EXTENSION)
    })
}

/// The fresh harness digest render (body plus state fingerprint) of a
/// conversation, when its state renders a non-empty digest.
pub(crate) async fn digest_render_of(
    deps: &HostDeps,
    conversation: &eukhe_durable::harness::Conversation,
    cx: &Context,
) -> eukhe_durable::session::SessionResult<Option<crate::durable::digest::HarnessDigestRender>> {
    let render = super::digest::conversation_digest(deps, conversation, cx)
        .await
        .map_err(eukhe_durable::session::SessionError::other)?;
    Ok((!render.digest.is_empty()).then_some(render))
}

/// Whether `conversation` is a chat-memory root (the compaction surfaces
/// decline or skip for it).
/// # Errors
///
/// The conversation record cannot be read.
pub async fn chat_memory_root(
    deps: &HostDeps,
    conversation: eukhe_durable::types::ConversationId,
    cx: &Context,
) -> eukhe_durable::session::SessionResult<bool> {
    summary::chat_memory_root_of(deps, conversation, cx).await
}
