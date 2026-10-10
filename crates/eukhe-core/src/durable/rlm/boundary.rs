//! The run-boundary host requests: `compact.status`/`compact.run` and
//! `refine.status`/`refine.run` (port of the old engine's
//! `TurnBoundaryRequests`). Both `*.run` requests only schedule work for the
//! requesting conversation:
//!
//! - `compact.run` admits a manual durable compaction
//!   (`Conversation::compact`): it summarizes while the run keeps working
//!   and places its summary at the next boundary.
//! - `refine.run` records the request in the conversation's
//!   [`BOUNDARY_DOC`]; the generation's `after_tools` hook runs it once the
//!   requesting tool round ends (see `refine.rs`), so a crash before then
//!   keeps the request.

use std::sync::{Arc, Weak};

use eukhe_chord::context::Context;
use eukhe_chord::json::{from_json, to_json, JsonValue};
use eukhe_durable::documents::{ConversationDoc, DocDefinition};
use eukhe_durable::entries::COMPACTION_ENTRY;
use eukhe_durable::harness::agent::resolve_settings;
use eukhe_durable::harness::compaction::{estimate_context, select_cut};
use eukhe_durable::harness::types::{CompactionReason, ContextView, ToolExecutionApiExt};
use eukhe_durable::harness::{Conversation, LiveState, LIVE_DOC};
use eukhe_durable::session::SessionResult;
use eukhe_durable::types::{ConversationId, DocumentReaderExt, LatestFork};
use eukhe_pi_ai::utils::estimate::calculate_context_tokens;
use eukhe_types::pi_ai::Message;
use futures::future::BoxFuture;
use futures::FutureExt;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use super::super::{HostCall, HostCallHandler};
use super::{background, RlmRuntime};

const SESSION_ENDED: &str = "the session ended before the request could be served";
const NO_TURN_COMPACT: &str =
    "no active turn; compaction can only be requested while a turn is running";
const NO_TURN_REFINE: &str = "no active turn; refine can only be requested while a turn is running";

/// A scheduled refinement (kernel `refine.run`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PendingRefine {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub instructions: Option<String>,
    pub global: bool,
}

/// Run-boundary requests of one conversation that wait for the end of the
/// requesting tool round.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct BoundaryState {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub refine: Option<PendingRefine>,
}

/// The `eukhe.rlm.boundary` conversation document.
pub static BOUNDARY_DOC: ConversationDoc<BoundaryState> = match ConversationDoc::define(
    DocDefinition {
        kind: "eukhe.rlm.boundary",
        version: 1,
        initial: BoundaryState::default,
        migrate: None,
        checkpoint_when: Some(|_, _, _| true),
    },
    LatestFork::Initial,
) {
    Ok(token) => token,
    Err(_) => panic!("eukhe.rlm.boundary has a valid version"),
};

/// Register the boundary requests the session's settings allow; returns
/// whether `refine.*` registered (the refine hook installs with it).
pub(super) fn register(runtime: &Arc<RlmRuntime>) -> bool {
    let deps = &runtime.deps;
    // TS `_includeCompactSkill`: the compaction `agentCallable` setting.
    let agent_callable = deps
        .settings
        .manager()
        .settings()
        .compaction
        .as_ref()
        .and_then(|compaction| compaction.agent_callable)
        .unwrap_or(true);
    if agent_callable {
        let weak = Arc::downgrade(runtime);
        deps.host_requests
            .register("compact.status", handler(&weak, compact_status));
        deps.host_requests
            .register("compact.run", handler(&weak, compact_run));
    }
    // TS `_autoRefineAllowedForSession`: a top-level session with a local
    // harness state directory (under its durable storage).
    let refine_allowed = deps.role.is_root() && refine_harness_dir(runtime).is_some();
    if refine_allowed {
        let weak = Arc::downgrade(runtime);
        deps.host_requests
            .register("refine.status", handler(&weak, refine_status));
        deps.host_requests
            .register("refine.run", handler(&weak, refine_run));
    }
    refine_allowed
}

/// The session's local harness state directory.
pub(super) fn refine_harness_dir(runtime: &RlmRuntime) -> Option<std::path::PathBuf> {
    crate::refinement::get_local_harness_state_dir(runtime.deps.storage_dir.as_deref())
}

type Handle = fn(Arc<RlmRuntime>, HostCall) -> BoxFuture<'static, anyhow::Result<Value>>;

fn handler(weak: &Weak<RlmRuntime>, handle: Handle) -> HostCallHandler {
    let weak = weak.clone();
    Arc::new(move |call: HostCall| match weak.upgrade() {
        Some(runtime) => handle(runtime, call),
        None => futures::future::ready(Err(anyhow::anyhow!(SESSION_ENDED))).boxed(),
    })
}

/// An optional string field with the exact TS validation message on a
/// non-string value; `None` for absent/null.
fn string_field(data: &Value, key: &str, error: &'static str) -> anyhow::Result<Option<String>> {
    match data.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(value)) => Ok(Some(value.clone())),
        Some(_) => anyhow::bail!("{error}"),
    }
}

fn no_active_turn(reason: &'static str) -> Value {
    json!({ "scheduled": false, "reason": reason })
}

async fn conversation(
    runtime: &RlmRuntime,
    id: ConversationId,
    cx: &Context,
) -> anyhow::Result<Conversation> {
    let harness = runtime.deps.harness.require()?;
    harness
        .conversation(id, cx)
        .await?
        .ok_or_else(|| anyhow::anyhow!("conversation {id} does not exist"))
}

async fn live(runtime: &RlmRuntime, id: ConversationId, cx: &Context) -> anyhow::Result<LiveState> {
    let harness = runtime.deps.harness.require()?;
    Ok(match harness.snapshot(&LIVE_DOC, id, cx).await? {
        Some(value) => from_json(&JsonValue::Object(value))?,
        None => LiveState::default(),
    })
}

/// The conversation's estimated context size (TS `getContextUsage`): the
/// last measured response plus estimates of what follows; `None` right
/// after a compaction, before a response measured the compacted context.
fn context_tokens(view: &ContextView) -> Option<u64> {
    let compacted = view
        .head
        .as_ref()
        .is_some_and(|head| COMPACTION_ENTRY.is(Some(head)));
    if compacted {
        let measured_after = view.contributions.iter().skip(1).flatten().any(|message| {
            matches!(message, Message::Assistant(assistant)
                    if calculate_context_tokens(&assistant.usage) > 0)
        });
        if !measured_after {
            return None;
        }
    }
    Some(estimate_context(view, &[]))
}

fn compact_status(
    runtime: Arc<RlmRuntime>,
    call: HostCall,
) -> BoxFuture<'static, anyhow::Result<Value>> {
    async move {
        let cx = background();
        let (id, agent) = runtime.target(call.call.as_ref(), &cx).await?;
        let window = agent
            .model
            .as_ref()
            .and_then(|model| runtime.model(model))
            .map(|model| model.context_window)
            .filter(|window| *window > 0);
        let (tokens, window_value, percent) = match window {
            Some(window) => {
                let view = conversation(&runtime, id, &cx)
                    .await?
                    .context(
                        &cx,
                        eukhe_durable::harness::types::ContextOptions::default(),
                    )
                    .await?;
                let tokens = context_tokens(&view);
                #[expect(
                    clippy::cast_precision_loss,
                    reason = "token counts are JS numbers, far below 2^53"
                )]
                let percent = tokens.map(|tokens| tokens as f64 / window as f64 * 100.0);
                (
                    tokens.map_or(Value::Null, Value::from),
                    Value::from(window),
                    percent.map_or(Value::Null, Value::from),
                )
            }
            None => (Value::Null, Value::Null, Value::Null),
        };
        let scheduled = live(&runtime, id, &cx)
            .await?
            .compactions
            .is_some_and(|compactions| {
                compactions
                    .iter()
                    .any(|status| status.reason == CompactionReason::Manual)
            });
        Ok(json!({
            "tokens": tokens,
            "context_window": window_value,
            "percent": percent,
            "scheduled": scheduled,
        }))
    }
    .boxed()
}

fn compact_run(
    runtime: Arc<RlmRuntime>,
    call: HostCall,
) -> BoxFuture<'static, anyhow::Result<Value>> {
    async move {
        let instructions = string_field(
            &call.data,
            "instructions",
            "compact.run instructions must be a string when provided",
        )?;
        let cx = background();
        let (id, _) = runtime.target(call.call.as_ref(), &cx).await?;
        if live(&runtime, id, &cx).await?.run.is_none() {
            return Ok(no_active_turn(NO_TURN_COMPACT));
        }
        let conversation = conversation(&runtime, id, &cx).await?;
        let view = conversation.context(&cx, eukhe_durable::harness::types::ContextOptions::default()).await?;
        // TS `prepareCompaction`: only schedule a compaction that has
        // history to summarize.
        let keep_recent = resolve_settings(Some(&runtime.deps.settings.harness()))
            .compaction
            .keep_recent_tokens;
        let compacted_tail = view.entries.len() == usize::from(view.head.is_some())
            && view
                .head
                .as_ref()
                .is_some_and(|head| COMPACTION_ENTRY.is(Some(head)));
        if compacted_tail {
            return Ok(json!({ "scheduled": false, "reason": "already compacted" }));
        }
        if select_cut(&view, keep_recent).is_none() {
            return Ok(json!({ "scheduled": false, "reason": "session is too short to compact" }));
        }
        conversation.compact(instructions, &cx).await?;
        Ok(json!({
            "scheduled": true,
            "note": "Compaction runs when the current turn ends; you resume automatically afterwards. Continue working normally.",
        }))
    }
    .boxed()
}

/// The conversation's boundary document.
pub(super) async fn boundary_state<R>(
    reader: &R,
    id: ConversationId,
    cx: &Context,
) -> SessionResult<BoundaryState>
where
    R: DocumentReaderExt + ?Sized,
{
    Ok(match reader.snapshot(&BOUNDARY_DOC, id, cx).await? {
        Some(value) => from_json(&JsonValue::Object(value))?,
        None => BoundaryState::default(),
    })
}

fn refine_status(
    runtime: Arc<RlmRuntime>,
    call: HostCall,
) -> BoxFuture<'static, anyhow::Result<Value>> {
    async move {
        let cx = background();
        let (id, _) = runtime.target(call.call.as_ref(), &cx).await?;
        let harness = runtime.deps.harness.require()?;
        let pending = boundary_state(&harness, id, &cx).await?.refine.is_some();
        // Refinement runs inside the generation between tool rounds, so a
        // cell never observes one in flight.
        Ok(json!({ "pending": pending, "in_flight": false }))
    }
    .boxed()
}

fn refine_run(
    runtime: Arc<RlmRuntime>,
    call: HostCall,
) -> BoxFuture<'static, anyhow::Result<Value>> {
    async move {
        let instructions = string_field(
            &call.data,
            "instructions",
            "refine.run instructions must be a string when provided",
        )?;
        let global = match call.data.get("global") {
            None | Some(Value::Null) => None,
            Some(Value::Bool(value)) => Some(*value),
            Some(_) => anyhow::bail!("refine.run global must be a boolean when provided"),
        };
        let cx = background();
        let (id, _) = runtime.target(call.call.as_ref(), &cx).await?;
        if live(&runtime, id, &cx).await?.run.is_none() {
            return Ok(no_active_turn(NO_TURN_REFINE));
        }
        let schedule = move |tx: eukhe_durable::session::Tx| async move {
            let draft = tx.doc(&BOUNDARY_DOC, id).await?;
            let current: Option<PendingRefine> = match draft.get("refine")? {
                Some(item) => Some(from_json(&item.to_value()?)?),
                None => None,
            };
            // An absent field keeps the pending request's value.
            let merged = match current {
                Some(current) => PendingRefine {
                    instructions: instructions.or(current.instructions),
                    global: global.unwrap_or(current.global),
                },
                None => PendingRefine {
                    instructions,
                    global: global.unwrap_or(false),
                },
            };
            draft.set("refine", to_json(&merged)?)?;
            Ok(())
        };
        match &call.call {
            Some(api) => api.commit(schedule, &cx).await?,
            None => conversation(&runtime, id, &cx).await?.commit(schedule, &cx).await?,
        }
        Ok(json!({
            "scheduled": true,
            "note": "Refinement runs when the current turn ends; applied edits are appended to your context as a refinement notice and you resume automatically. Continue working normally.",
        }))
    }
    .boxed()
}
