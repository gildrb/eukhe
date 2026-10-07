//! The RLM host requests that do not touch the turn boundary: the
//! session-internal heartbeats (`rlm_heartbeat.*`), the kernel's generic MCP
//! bridge (`mcp.*`), and `model.info`. Ported from the old engine's
//! `SessionRuntime::register_host_handlers` (heartbeat half),
//! `McpManager::register_host_handlers`, and `TurnBoundaryRequests::
//! register_model_info_handler`.

use std::sync::{Arc, Weak};

use futures::FutureExt;
use serde_json::{json, Value};

use super::super::{HostCall, HostCallHandler, HostDeps};
use super::{background, RlmRuntime};
use crate::cron::store::AgentCronJobStore;
use crate::kernel::shared::{HostRequestHandlers, HostRequestPayload};
use crate::session_engine::host_requests::{handle_rlm_heartbeat_host_request, SessionBinding};

/// The heartbeat request types.
const RLM_HEARTBEAT_REQUESTS: [&str; 4] = [
    "rlm_heartbeat.list",
    "rlm_heartbeat.create",
    "rlm_heartbeat.update",
    "rlm_heartbeat.delete",
];

pub(super) fn register(runtime: &Arc<RlmRuntime>) {
    let deps = &runtime.deps;
    register_heartbeats(deps);
    let mut mcp = HostRequestHandlers::new();
    crate::mcp::McpManager::register_host_handlers(&deps.mcp, &mut mcp);
    register_payload_handlers(deps, &mcp);
    register_model_info(runtime);
}

/// Adapt handlers written against the kernel's payload shape into the
/// session registry (they take no call context).
fn register_payload_handlers(deps: &HostDeps, handlers: &HostRequestHandlers) {
    for (request_type, handler) in handlers.iter() {
        let handler = Arc::clone(handler);
        let adapted: HostCallHandler = Arc::new(move |call: HostCall| {
            handler(HostRequestPayload {
                data: call.data,
                cell_source_code: None,
            })
        });
        deps.host_requests.register(request_type, adapted);
    }
}

/// `rlm_heartbeat.*`: the embedding's scheduled-jobs store and session
/// identity when wired (the daemon worker), else the private
/// `<agent_dir>/cron-jobs.json` store bound to this session.
fn register_heartbeats(deps: &HostDeps) {
    let (store, active_session_id, binding, mutation_hook) = match &deps.cron {
        Some(wiring) => {
            let (active, binding) = match &wiring.binding {
                Some(binding) => (
                    binding.active_session_id.clone(),
                    SessionBinding {
                        session_id: binding.session_id.clone(),
                        session_file: binding.session_file.clone(),
                        cwd: binding.cwd.clone(),
                    },
                ),
                None => (deps.session_id.clone(), fallback_binding(deps)),
            };
            (
                Arc::clone(&wiring.store),
                active,
                binding,
                wiring.mutation_hook.clone(),
            )
        }
        None => (
            Arc::new(AgentCronJobStore::new(
                deps.agent_dir.join("cron-jobs.json"),
            )),
            deps.session_id.clone(),
            fallback_binding(deps),
            None,
        ),
    };
    for request_type in RLM_HEARTBEAT_REQUESTS {
        let store = Arc::clone(&store);
        let active_session_id = active_session_id.clone();
        let binding = SessionBinding {
            session_id: binding.session_id.clone(),
            session_file: binding.session_file.clone(),
            cwd: binding.cwd.clone(),
        };
        let mutation_hook = mutation_hook.clone();
        let handler: HostCallHandler = Arc::new(move |call: HostCall| {
            let store = Arc::clone(&store);
            let active_session_id = active_session_id.clone();
            let binding = SessionBinding {
                session_id: binding.session_id.clone(),
                session_file: binding.session_file.clone(),
                cwd: binding.cwd.clone(),
            };
            let mutation_hook = mutation_hook.clone();
            async move {
                let outcome = handle_rlm_heartbeat_host_request(
                    request_type,
                    &call.data,
                    &store,
                    &active_session_id,
                    &binding,
                )?;
                // The embedding withdraws the queued fire and re-arms its
                // scheduler (TS daemon-mode's heartbeat controllers).
                if let (Some(mutation), Some(hook)) = (outcome.mutation, &mutation_hook) {
                    hook(mutation).await;
                }
                Ok(outcome.response)
            }
            .boxed()
        });
        deps.host_requests.register(request_type, handler);
    }
}

/// The session identity kernel-created heartbeats bind to without an
/// embedding binding: the durable session id, its storage directory (the
/// durable session has no single file), and its cwd.
fn fallback_binding(deps: &HostDeps) -> SessionBinding {
    SessionBinding {
        session_id: deps.session_id.clone(),
        session_file: deps
            .storage_dir
            .as_ref()
            .map(|dir| dir.display().to_string())
            .unwrap_or_default(),
        cwd: deps.cwd.display().to_string(),
    }
}

/// `model.info`: the model the requesting conversation runs now (`id`,
/// `provider`, input modalities); nulls and no inputs when it has none.
fn register_model_info(runtime: &Arc<RlmRuntime>) {
    let weak: Weak<RlmRuntime> = Arc::downgrade(runtime);
    let handler: HostCallHandler = Arc::new(move |call: HostCall| {
        let weak = weak.clone();
        async move {
            let runtime = weak.upgrade().ok_or_else(|| {
                anyhow::anyhow!("the session ended before the request could be served")
            })?;
            let cx = background();
            let (_, agent) = runtime.target(call.call.as_ref(), &cx).await?;
            Ok(model_info(&runtime, agent.model.as_ref()))
        }
        .boxed()
    });
    runtime.deps.host_requests.register("model.info", handler);
}

fn model_info(
    runtime: &RlmRuntime,
    model: Option<&eukhe_durable::harness::types::ModelRef>,
) -> Value {
    let Some(model) = model else {
        return json!({ "id": Value::Null, "provider": Value::Null, "input": [] });
    };
    let input: Vec<&'static str> = runtime
        .model(model)
        .map(|catalog| {
            catalog
                .input
                .iter()
                .map(|modality| modality.as_str())
                .collect()
        })
        .unwrap_or_default();
    json!({
        "id": model.model_id,
        "provider": model.provider,
        "input": input,
    })
}
