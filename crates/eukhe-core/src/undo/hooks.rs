//! The `eukhe.undo` extension of a top-level session: the first request
//! preparation of a run of the main conversation starts that turn's
//! snapshot in the background, recording the root run it starts (the
//! number the `eukhe.effects` ledger gives that run: the current one when
//! the ledger numbered it already, else the next), so the request is not
//! held; the run's later rounds are the same turn. Every model-issued tool
//! call waits for it, so no tool of the turn runs before its snapshot. Its
//! install also removes the snapshots of sessions older than
//! `undo.keepDays`, on the blocking pool.

use std::sync::Arc;
use std::time::SystemTime;

use eukhe_chord::context::Context;
use eukhe_durable::harness::define::{define_extension, hook};
use eukhe_durable::harness::effects::EFFECTS_DOC;
use eukhe_durable::harness::types::{Extension, GenerationHooks, HookApi, ToolHooks};
use eukhe_durable::harness::{GENERATION_TASK, LIVE_DOC, TOOL_TASK};
use eukhe_durable::session::SessionResult;
use futures::FutureExt;

use super::{prune_snapshots, snapshots_dir, TurnKey, TurnSnapshots};
use crate::durable::autonomous::read_doc;
use crate::durable::ran_effects::run_key;
use crate::durable::{main_conversation_id, HostDeps};

/// The extension's name.
pub const UNDO_EXTENSION: &str = "eukhe.undo";

/// The undo extension of a session that keeps snapshots.
pub(crate) fn extension(deps: &Arc<HostDeps>, snapshots: &Arc<TurnSnapshots>) -> Arc<Extension> {
    prune_in_background(deps);
    let (begin, ready) = (Arc::clone(snapshots), Arc::clone(snapshots));
    define_extension(Extension {
        name: UNDO_EXTENSION.to_owned(),
        hooks: vec![
            hook(
                &*GENERATION_TASK,
                GenerationHooks {
                    before_prepare: Some(Arc::new(move |api, cx| {
                        let (begin, api, cx) = (Arc::clone(&begin), api.clone(), cx.clone());
                        async move {
                            if let Some((turn, run)) = turn_of(&api, &cx).await? {
                                begin.begin(turn, run);
                            }
                            Ok(None)
                        }
                        .boxed()
                    })),
                    ..GenerationHooks::default()
                },
            ),
            hook(
                &*TOOL_TASK,
                ToolHooks {
                    // A nested call runs inside a call that already waited.
                    before_tool: Some(Arc::new(move |call, _, _| {
                        let (ready, nested) = (Arc::clone(&ready), call.parent.is_some());
                        async move {
                            if !nested {
                                ready.ready().await;
                            }
                            Ok(None)
                        }
                        .boxed()
                    })),
                    after_tool: None,
                },
            ),
        ],
        ..Extension::default()
    })
}

/// The turn of the request `api` prepares (the run of the session's main
/// conversation it belongs to) and the root run it starts; `None` for
/// another conversation's request.
async fn turn_of(api: &HookApi, cx: &Context) -> SessionResult<Option<(TurnKey, u64)>> {
    let conversation = api.conversation_id();
    if main_conversation_id(api, cx).await? != conversation {
        return Ok(None);
    }
    let live = read_doc(api, &LIVE_DOC, conversation, cx)
        .await?
        .unwrap_or_default();
    let first = live
        .run
        .as_ref()
        .and_then(|run| run.inputs.first().copied());
    let ledger = read_doc(api, &EFFECTS_DOC, conversation, cx)
        .await?
        .unwrap_or_default();
    // The ledger numbers a run once, keyed by its first input, possibly
    // after this request is prepared; an effect of a run it has not
    // numbered goes to the next number as well.
    let run = match (run_key(&live), ledger.run_key) {
        (Some(key), Some(numbered)) if key == numbered => ledger.run,
        (Some(_) | None, Some(_) | None) => ledger.run + 1,
    };
    Ok(Some((
        first.map_or_else(|| TurnKey::Task(api.task_id()), TurnKey::Run),
        run,
    )))
}

fn prune_in_background(deps: &HostDeps) {
    let Some(dir) = snapshots_dir(&deps.agent_dir) else {
        return;
    };
    let Ok(runtime) = tokio::runtime::Handle::try_current() else {
        return;
    };
    let keep_days = deps.settings.manager().get_undo_keep_days();
    let session = deps.session_id.clone();
    runtime.spawn_blocking(move || {
        match prune_snapshots(&dir, keep_days, SystemTime::now(), &session) {
            Ok(removed) if removed.is_empty() => {}
            Ok(removed) => tracing::info!(?removed, "removed old workspace snapshots"),
            Err(error) => tracing::warn!(%error, "removing old workspace snapshots failed"),
        }
    });
}
