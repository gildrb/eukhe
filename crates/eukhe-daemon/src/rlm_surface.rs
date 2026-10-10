//! The RLM child-management surface: the worker arms for
//! `get_rlm_children`, `cancel_rlm_child`, `delete_rlm_subagent`,
//! `set_rlm_max_depth`, and `get_rlm_max_depth_status` (TS daemon-mode
//! cases). The roster is the main conversation's durable children document
//! (`eukhe.rlm.children`, kept by the `eukhe.rlm.child` tasks); the runtime
//! depth bound is its `eukhe.rlm.max-depth` document. Each handler answers
//! the exact TS wire shape.

use std::sync::Arc;

use crate::rlm_children::{ParentIdentity, RlmChildIdentity, SupervisorChildSessions};
use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_core::durable::children::{
    cancel_child, delete_inactive_child, list_children, read_max_depth_override,
    set_max_depth_override, DeleteChildOutcome, NoRlmChildren, RlmChildRecord, RlmSubagentHost,
};
use serde_json::{json, Value};

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::{HostedSession, Worker};

fn cx() -> &'static Context {
    &BACKGROUND_CONTEXT
}

/// The `get_rlm_children` snapshot of one child (TS `RlmChildAgentSnapshot`:
/// its `status` is the raw run status, `done` where the kernel roster row
/// reads `completed`).
fn child_snapshot(record: &RlmChildRecord, parent_id: Option<&str>) -> Value {
    let entry = &record.entry;
    let mut snapshot = json!({
        "id": entry.rlm_child_id,
        "activeSessionId": entry.active_session_id,
        "sessionName": entry.session_name,
        "label": entry.label,
        "status": record.run_status,
        "durationMs": entry.duration_ms,
        "sessionDir": entry.session_dir,
    });
    if let Some(model) = &record.model {
        snapshot["model"] = json!(model);
    }
    if let Some(answer) = &entry.answer_preview {
        snapshot["answerPreview"] = json!(answer);
    }
    // The parent's own RLM node id (TS `_rlmParentNodeId`; absent for
    // top-level sessions, where TS serializes the field out).
    if let Some(parent_id) = parent_id {
        snapshot["parentId"] = json!(parent_id);
    }
    snapshot
}

/// The children of the hosted session's main conversation as roster
/// snapshots (the `get_rlm_children` children and the context tree's).
///
/// # Errors
///
/// The main conversation or the children document cannot be read.
pub(crate) async fn rlm_child_snapshots(
    hosted: &HostedSession,
    parent_id: Option<&str>,
) -> anyhow::Result<Vec<Value>> {
    let main = hosted.main()?;
    let records = list_children(hosted.harness(), main.id(), cx()).await?;
    Ok(records
        .iter()
        .map(|record| child_snapshot(record, parent_id))
        .collect())
}

/// The hosted session's durable children as family identities: a child is
/// addressable once it has a session (its live id, else its durable
/// session id); a queued child without one is not.
async fn durable_child_identities(hosted: &HostedSession) -> anyhow::Result<Vec<RlmChildIdentity>> {
    let main = hosted.main()?;
    let records = list_children(hosted.harness(), main.id(), cx()).await?;
    Ok(records
        .into_iter()
        .filter_map(|record| {
            let entry = record.entry;
            let active_session_id = entry
                .active_session_id
                .or_else(|| entry.session_id.clone())?;
            Some(RlmChildIdentity {
                rlm_child_id: entry.rlm_child_id,
                active_session_id,
                session_id: entry.session_id,
                session_name: entry.session_name,
            })
        })
        .collect())
}

impl Worker {
    /// The supervisor-backed RLM child host sessions of this worker spawn
    /// children through (`SessionConfig::children`), built once and rebound
    /// to `identity` (the session being opened). A spawn without a model
    /// inherits the parent's current model, read from the shown main
    /// conversation's agent at spawn time. `None` for a worker without a
    /// supervisor (standalone), whose sessions have no children.
    pub(crate) fn rlm_subagent_host(
        &self,
        identity: ParentIdentity,
    ) -> Option<Arc<dyn RlmSubagentHost>> {
        if self.config.supervisor_socket_path.as_os_str().is_empty() {
            return None;
        }
        let host = self.rlm_children.get_or_init(|| {
            let host = Arc::new(SupervisorChildSessions::new(
                Arc::new(crate::supervisor_link::SupervisorLink::new(
                    self.config.supervisor_socket_path.clone(),
                )),
                self.config.agent_dir.clone(),
                self.config.active_session_id.clone(),
                Arc::clone(&self.model_refusal_telemetry),
            ));
            let session = self.session.clone();
            host.set_parent_model_source(Arc::new(move || {
                let hosted = session.get();
                Box::pin(async move {
                    let agent = hosted?.main().ok()?.agent(cx()).await.ok()?;
                    agent
                        .model
                        .map(|model| format!("{}/{}", model.provider, model.model_id))
                })
            }));
            let core = Arc::clone(&self.core);
            host.set_parent_name_source(Arc::new(move || {
                core.lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .session_name
                    .clone()
                    .filter(|name| !name.is_empty())
            }));
            // The family view's durable children: the main conversation's
            // children document (a restarted parent's passivated children
            // included), which the durable path keeps instead of the
            // registry.
            let session = self.session.clone();
            host.set_durable_children_source(Arc::new(move || {
                let hosted = session.get();
                Box::pin(async move {
                    match hosted {
                        Some(hosted) => durable_child_identities(&hosted).await,
                        None => Ok(Vec::new()),
                    }
                })
            }));
            let context_tree = Arc::clone(&self.context_tree);
            host.set_delete_notifier(Arc::new(move |child_id| {
                context_tree.invalidate_child(child_id);
            }));
            // Every child admission, settle, cancel, and delete surfaces as
            // a `rlm_child_update` session event (the ACP adapter maps it to
            // the namespaced `_meta.subagents` update), stamped with this
            // session's own RLM node id as the parent.
            let core = Arc::clone(&self.core);
            let events = Arc::clone(&self.events);
            host.set_child_update_sink(Arc::new(move |mut child| {
                let parent_id = core
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .rlm_child_id
                    .clone();
                if let Some(parent_id) = parent_id {
                    child["parentId"] = json!(parent_id);
                }
                crate::worker::emit_worker_event_with(
                    &core,
                    &events,
                    json!({ "type": "rlm_child_update", "child": child }),
                );
            }));
            host
        });
        host.set_identity(identity);
        Some(Arc::clone(host) as Arc<dyn RlmSubagentHost>)
    }

    /// `get_rlm_children`: the authoritative child roster plus the session's
    /// event sequence captured before the read (TS
    /// `buildRlmChildSnapshotsWithPassiveRlmSubagents` freshness contract).
    pub(crate) async fn handle_get_rlm_children(&self) -> DaemonResponse {
        let hosted = match self.hosted("get_rlm_children") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let (event_sequence, parent_id) = {
            let core = self.core.lock().unwrap();
            (core.last_event_sequence, core.rlm_child_id.clone())
        };
        match rlm_child_snapshots(&hosted, parent_id.as_deref()).await {
            Ok(children) => response_success(
                None,
                "get_rlm_children",
                Some(json!({ "children": children, "eventSequence": event_sequence })),
            ),
            Err(error) => response_failure(None, "get_rlm_children", &format!("{error:#}"), None),
        }
    }

    /// `cancel_rlm_child`: cancel one live child run by id. The TS wire
    /// contract is `{ cancelled: boolean }` - an unknown or already-settled
    /// child id answers `false`, never an error.
    pub(crate) async fn handle_cancel_rlm_child(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted("cancel_rlm_child") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(child_id) = payload.get("childId").and_then(Value::as_str) else {
            return response_failure(
                None,
                "cancel_rlm_child",
                "cancel_rlm_child requires a childId",
                None,
            );
        };
        let cancelled = async {
            let main = hosted.main()?;
            cancel_child(hosted.harness(), main.id(), child_id, cx()).await
        }
        .await;
        match cancelled {
            Ok(cancelled) => response_success(
                None,
                "cancel_rlm_child",
                Some(json!({ "cancelled": cancelled.is_some() })),
            ),
            Err(error) => response_failure(None, "cancel_rlm_child", &format!("{error:#}"), None),
        }
    }

    /// `delete_rlm_subagent`: delete one inactive child by id. The TS wire
    /// contract is `{ deleted: boolean }`, plus `reason: "running"` when a
    /// live child refused the delete; a teardown failure surfaces as the
    /// command failure.
    pub(crate) async fn handle_delete_rlm_subagent(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted("delete_rlm_subagent") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(child_id) = payload.get("childId").and_then(Value::as_str) else {
            return response_failure(
                None,
                "delete_rlm_subagent",
                "delete_rlm_subagent requires a childId",
                None,
            );
        };
        let host: Arc<dyn RlmSubagentHost> = hosted
            .deps()
            .children
            .clone()
            .unwrap_or_else(|| Arc::new(NoRlmChildren));
        let outcome = async {
            let main = hosted.main()?;
            delete_inactive_child(hosted.harness(), host.as_ref(), main.id(), child_id, cx()).await
        }
        .await;
        match outcome {
            Ok(DeleteChildOutcome::Deleted(entry)) => {
                self.context_tree.invalidate_child(&entry.rlm_child_id);
                response_success(
                    None,
                    "delete_rlm_subagent",
                    Some(json!({ "deleted": true })),
                )
            }
            Ok(DeleteChildOutcome::Running) => response_success(
                None,
                "delete_rlm_subagent",
                Some(json!({ "deleted": false, "reason": "running" })),
            ),
            Ok(DeleteChildOutcome::NotFound) => response_success(
                None,
                "delete_rlm_subagent",
                Some(json!({ "deleted": false })),
            ),
            Err(error) => {
                response_failure(None, "delete_rlm_subagent", &format!("{error:#}"), None)
            }
        }
    }

    /// `set_rlm_max_depth`: set the session's recursion bound (durable, so a
    /// resumed session keeps it), optionally persisting it as the global
    /// settings default. The response is the TS `SetRlmMaxDepthResult`
    /// (`{ maxDepth, source, globalSaved }` plus `globalError` when the
    /// global write failed).
    pub(crate) async fn handle_set_rlm_max_depth(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted("set_rlm_max_depth") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(max_depth) = payload
            .get("maxDepth")
            .and_then(Value::as_u64)
            .and_then(|depth| u32::try_from(depth).ok())
        else {
            return response_failure(
                None,
                "set_rlm_max_depth",
                "RLM max depth must be a non-negative integer.",
                None,
            );
        };
        let global = payload.get("global").and_then(Value::as_bool) == Some(true);
        let persisted = async {
            let main = hosted.main()?;
            set_max_depth_override(hosted.harness(), main.id(), Some(max_depth), cx()).await
        }
        .await;
        if let Err(error) = persisted {
            return response_failure(None, "set_rlm_max_depth", &error.to_string(), None);
        }
        let mut result = json!({ "maxDepth": max_depth, "source": "chat", "globalSaved": false });
        if global {
            let deps = hosted.deps();
            let mut settings =
                eukhe_core::settings::SettingsManager::create(&deps.cwd, &deps.agent_dir);
            match settings.set_rlm_max_depth(u64::from(max_depth)) {
                Ok(()) => result["globalSaved"] = json!(true),
                Err(error) => result["globalError"] = json!(format!("{error:#}")),
            }
        }
        response_success(None, "set_rlm_max_depth", Some(result))
    }

    /// `get_rlm_max_depth_status` (TS `getRlmMaxDepthStatus`): the runtime
    /// bound set in this session (`source: "chat"`), else the session's
    /// configured bound (`source: "default"`).
    pub(crate) async fn handle_get_rlm_max_depth_status(&self) -> DaemonResponse {
        let hosted = match self.hosted("get_rlm_max_depth_status") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let status = async {
            let main = hosted.main()?;
            read_max_depth_override(hosted.harness(), main.id(), cx()).await
        }
        .await;
        match status {
            Ok(Some(max_depth)) => response_success(
                None,
                "get_rlm_max_depth_status",
                Some(json!({ "maxDepth": max_depth, "source": "chat" })),
            ),
            Ok(None) => response_success(
                None,
                "get_rlm_max_depth_status",
                Some(json!({
                    "maxDepth": hosted.deps().role.rlm_max_depth,
                    "source": "default",
                })),
            ),
            Err(error) => {
                response_failure(None, "get_rlm_max_depth_status", &error.to_string(), None)
            }
        }
    }
}

#[cfg(test)]
mod tests;
