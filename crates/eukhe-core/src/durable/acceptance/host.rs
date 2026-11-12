//! The kernel's `acceptance.get` and `acceptance.set` host requests: what
//! the worker may do with its own acceptance. It may read the checks it
//! has to pass; its attempt to set them goes to the compiled core as the
//! worker's act, which the core refuses (`verify_assign_needs_owner`).

use std::path::PathBuf;
use std::sync::Arc;

use eukhe_bend::rules::verify::Actor;
use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_durable::session::SessionError;
use eukhe_durable::types::ConversationId;
use eukhe_types::acceptance::CheckSpec;
use futures::FutureExt;
use serde_json::Value;

use super::ops::{acceptance_state, assign};
use crate::durable::{HarnessCell, HostCall, HostRequestRegistry};

#[derive(Clone)]
struct AcceptanceHost {
    harness: HarnessCell,
    cwd: PathBuf,
}

#[derive(Clone, Copy)]
enum Request {
    Get,
    Set,
}

impl AcceptanceHost {
    /// The conversation a host request targets: the executing tool call's
    /// conversation, else the root.
    fn target(&self, call: &HostCall) -> anyhow::Result<ConversationId> {
        match &call.call {
            Some(api) => Ok(api.conversation_id()),
            None => self
                .harness
                .root()
                .map(|root| root.id())
                .ok_or_else(|| SessionError::error("Harness is closed").into()),
        }
    }

    async fn handle(&self, request: Request, call: HostCall) -> anyhow::Result<Value> {
        let cx = BACKGROUND_CONTEXT.clone();
        let harness = self.harness.require()?;
        let conversation_id = self.target(&call)?;
        let state = match request {
            Request::Get => acceptance_state(&harness, conversation_id, &cx).await?,
            Request::Set => {
                let checks = call.data.get("checks").cloned().unwrap_or(Value::Null);
                let specs: Vec<CheckSpec> = serde_json::from_value(checks).map_err(|error| {
                    anyhow::anyhow!("acceptance.set checks must be a list of checks: {error}")
                })?;
                assign(
                    &harness,
                    conversation_id,
                    Actor::Worker,
                    specs,
                    None,
                    &self.cwd,
                    &cx,
                )
                .await?
            }
        };
        Ok(serde_json::to_value(state)?)
    }
}

/// Register `acceptance.get` and `acceptance.set`.
pub(crate) fn register_host_requests(
    harness: &HarnessCell,
    cwd: PathBuf,
    registry: &HostRequestRegistry,
) {
    let host = AcceptanceHost {
        harness: harness.clone(),
        cwd,
    };
    for (request_type, request) in [
        ("acceptance.get", Request::Get),
        ("acceptance.set", Request::Set),
    ] {
        let host = host.clone();
        registry.register(
            request_type,
            Arc::new(move |call: HostCall| {
                let host = host.clone();
                async move { host.handle(request, call).await }.boxed()
            }),
        );
    }
}
