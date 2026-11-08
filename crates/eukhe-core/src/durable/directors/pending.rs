//! The `PendingWork` Director's fact for the run loop's stop Directors
//! (`bend/stop.bend`): at a candidate stop, the generation asks its
//! `pending_work` hooks whether the conversation owns running work whose
//! end wakes it ([`pending_work`]). A stop while it does is a pause.

use std::sync::{Arc, Weak};

use eukhe_chord::context::Context;
use eukhe_durable::harness::define::hook;
use eukhe_durable::harness::types::{GenerationHooks, HookApi, HookRegistration};
use eukhe_durable::harness::GENERATION_TASK;
use futures::FutureExt;

use crate::durable::pending::{pending_work, PendingWorkError};
use crate::durable::HostDeps;

/// The `pending_work` hook of `pi.generation` over the session's deps
/// (held weakly: the deps hold the Harness that holds this hook). A closed
/// session owns no work; a read that fails fails the generation.
pub(crate) fn pending_work_hook(deps: &Arc<HostDeps>) -> HookRegistration {
    let deps: Weak<HostDeps> = Arc::downgrade(deps);
    hook(
        &*GENERATION_TASK,
        GenerationHooks {
            pending_work: Some(Arc::new(move |api: &HookApi, cx: &Context| {
                let (deps, conversation_id, cx) = (deps.clone(), api.conversation_id(), cx.clone());
                async move {
                    let Some(deps) = deps.upgrade() else {
                        return Ok(false);
                    };
                    let harness = deps.harness.require()?;
                    match pending_work(&deps, &harness, conversation_id, &cx).await {
                        Ok(work) => Ok(!work.is_none()),
                        Err(PendingWorkError::Read(error)) => Err(error),
                    }
                }
                .boxed()
            })),
            ..GenerationHooks::default()
        },
    )
}
