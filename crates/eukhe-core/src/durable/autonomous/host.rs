//! What the autonomous extension's hooks and host requests share, and the
//! `directors.push` kernel host request.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_durable::harness::Conversation;
use eukhe_durable::session::{SessionError, SessionResult};
use eukhe_durable::types::ConversationId;
use futures::FutureExt;
use serde_json::Value;

use super::ops::conversation_of;
use crate::durable::budget::BudgetGate;
use crate::durable::children::WorkLedger;
use crate::durable::directors::{push_director, DirectorLimits, Layer};
use crate::durable::{HarnessCell, HostCall, HostRequestRegistry};

/// The services of the autonomous extension: the session's Harness and
/// budget gate (what the session's budget admits at a step), the Director
/// stack's limits (read at each step: the settings can change), and the
/// work of each conversation the run's progress check counts (a cache of
/// what the transcript shows: a new process reads the transcript again).
#[derive(Clone)]
pub(crate) struct AutonomousHost {
    pub(crate) harness: HarnessCell,
    pub(crate) budget: Arc<BudgetGate>,
    pub(crate) limits: Arc<dyn Fn() -> DirectorLimits + Send + Sync>,
    pub(crate) work: Arc<Mutex<HashMap<ConversationId, WorkLedger>>>,
}

impl AutonomousHost {
    /// The conversation `conversation_id` of the open Harness.
    pub(crate) async fn conversation(
        &self,
        conversation_id: ConversationId,
        cx: &Context,
    ) -> SessionResult<Conversation> {
        conversation_of(&self.harness.require()?, conversation_id, cx).await
    }

    /// The conversation a host request targets: the executing tool call's
    /// conversation, else the root.
    fn target(&self, call: &HostCall) -> SessionResult<ConversationId> {
        match &call.call {
            Some(api) => Ok(api.conversation_id()),
            None => self
                .harness
                .root()
                .map(|root| root.id())
                .ok_or_else(|| SessionError::error("Harness is closed")),
        }
    }

    /// `directors.push`: put the asked layer on top of the stack.
    #[tracing::instrument(skip_all)]
    async fn push(&self, call: HostCall) -> anyhow::Result<Value> {
        let cx = BACKGROUND_CONTEXT.clone();
        let conversation_id = self.target(&call)?;
        Ok(serde_json::to_value(
            push_director(
                &self.harness.require()?,
                conversation_id,
                pushed_layer(&call.data)?,
                (self.limits)(),
                &cx,
            )
            .await?,
        )?)
    }
}

/// The layer a `directors.push` request asks for: `{"layer": "reminder",
/// "text": ...}`, or `{"layer": "forceTool", "tool": ..., "tries": ...}`
/// (`tries`, the retries per forced run, defaults to 1).
fn pushed_layer(data: &Value) -> anyhow::Result<Layer> {
    let text = |field: &str| {
        data.get(field)
            .and_then(Value::as_str)
            .filter(|value| !value.trim().is_empty())
            .map(str::to_owned)
            .ok_or_else(|| anyhow::anyhow!("directors.push {field} must be a non-empty string"))
    };
    match data.get("layer").and_then(Value::as_str) {
        Some("reminder") => Ok(Layer::reminder(text("text")?)),
        Some("forceTool") => {
            let tries = match data.get("tries") {
                None | Some(Value::Null) => 1,
                Some(value) => value
                    .as_u64()
                    .and_then(|tries| u32::try_from(tries).ok())
                    .ok_or_else(|| {
                        anyhow::anyhow!("directors.push tries must be a small non-negative integer")
                    })?,
            };
            Ok(Layer::force_tool(text("tool")?, tries))
        }
        _ => anyhow::bail!("directors.push layer must be \"reminder\" or \"forceTool\""),
    }
}

/// Register `directors.push`.
pub(crate) fn register_host_requests(host: &AutonomousHost, registry: &HostRequestRegistry) {
    let host = host.clone();
    registry.register(
        "directors.push",
        Arc::new(move |call: HostCall| {
            let host = host.clone();
            async move { host.push(call).await }.boxed()
        }),
    );
}
