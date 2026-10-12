//! The kernel's `rlm_heartbeat.*` host requests (the bundled rlm-heartbeat
//! skill's `snake_case` bridge; port of handleRlmHeartbeatHostRequest and
//! rlmHeartbeatHostResponse in agent-session.ts) and the embedding's cron
//! wiring those requests bind to.

use crate::cron::JobSource;
use std::future::Future;
use std::pin::Pin;

use serde_json::{json, Value};

use crate::cron::store::{
    AgentCronJobStore, CreateAgentCronJobInput, RlmHeartbeatStatusUpdate, RlmHeartbeatUpdate,
};
use crate::cron::{AgentCronJob, DeliveryMode, JobStatus};

/// The embedding's cron wiring for the kernel's `rlm_heartbeat.*` host
/// requests (TS daemon-mode wires its `AgentCronJobStore.forSessionArtifacts()`
/// into the session runtime): the shared store plus the durable session
/// identity the kernel-created jobs bind to.
#[derive(Clone)]
pub struct KernelCronWiring {
    /// The daemon worker's scheduled-jobs store.
    pub store: std::sync::Arc<crate::cron::store::AgentCronJobStore>,
    /// The session identity kernel-created jobs bind to; `None` until the
    /// embedding knows it (the engine falls back to the in-memory
    /// manager's identity).
    pub binding: Option<KernelCronBinding>,
    /// The post-mutation seam for kernel `rlm_heartbeat.*` requests (TS
    /// daemon-mode's `removeQueuedHeartbeatFollowUp` +
    /// `cronScheduler.wake()` inside its rlm heartbeat controllers):
    /// the daemon worker's hook; `None` leaves mutations unannounced
    /// (the embedded/standalone default).
    pub mutation_hook: Option<RlmHeartbeatMutationHook>,
}

/// The live/durable session identity for kernel-created rlm heartbeats.
#[derive(Clone, Debug)]
pub struct KernelCronBinding {
    /// The live active session id the daemon routes commands by (TS
    /// `options.activeSessionId`): the supervisor's `heartbeat_manage`
    /// resolves it.
    pub active_session_id: String,
    /// The durable session id the store partitions by.
    pub session_id: String,
    /// The durable session file the rebind pass moves jobs through.
    pub session_file: String,
    /// The session working directory.
    pub cwd: String,
}

// Opaque like the store it carries: the store handle has no meaningful
// debug form, and config structs embedding the wiring derive `Debug`.
impl std::fmt::Debug for KernelCronWiring {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KernelCronWiring")
            .field("binding", &self.binding)
            // The store + the hook are deliberately opaque (the type has no
            // meaningful debug form): `..` documents the omission.
            .finish_non_exhaustive()
    }
}

/// The `snake_case` heartbeat payload returned to the rlm-heartbeat skill.
pub fn rlm_heartbeat_host_response(job: &AgentCronJob) -> Value {
    json!({
        "id": job.id,
        "status": status_name(job.status),
        "label": nullable_string(job.label.clone()),
        "delivery_mode": job.delivery_mode.map_or("steer", delivery_mode_name),
        "instruction": job.prompt,
        "schedule": serde_json::to_value(&job.schedule).unwrap_or(Value::Null),
        "created_at": job.created_at,
        "updated_at": job.updated_at,
        "next_run_at": nullable_string(job.next_run_at.clone()),
        "last_run_at": nullable_string(job.last_run_at.clone()),
        "last_error": nullable_string(job.last_error.clone()),
        "run_count": job.run_count,
    })
}

fn status_name(status: JobStatus) -> &'static str {
    match status {
        JobStatus::Active => "active",
        JobStatus::Paused => "paused",
        JobStatus::Completed => "completed",
        JobStatus::Cancelled => "cancelled",
    }
}

fn delivery_mode_name(mode: DeliveryMode) -> &'static str {
    match mode {
        DeliveryMode::Steer => "steer",
        DeliveryMode::FollowUp => "follow_up",
    }
}

fn nullable_string(value: Option<String>) -> Value {
    match value {
        Some(text) => Value::String(text),
        None => Value::Null,
    }
}

/// One kernel `rlm_heartbeat.*` mutation: the changed job plus the
/// daemon-side post-mutation work it owes (TS daemon-mode runs
/// `removeQueuedHeartbeatFollowUp` and `cronScheduler.wake()` inside its
/// `createRlmHeartbeatForState` / `updateRlmHeartbeatForState` /
/// `deleteRlmHeartbeatForState` controllers).
///
/// `drop_queued` is the TS update condition: instruction/interval/pause/
/// delivery updates withdraw the queued fire, a label-only or resume-only
/// update does not, and every delete does.
#[derive(Debug, Clone)]
pub struct RlmHeartbeatMutation {
    pub job: AgentCronJob,
    pub drop_queued: bool,
}

/// The embedding's seam for kernel rlm heartbeat mutations: invoked by the
/// `rlm_heartbeat.*` host handlers after the store mutation, before the
/// response returns. The daemon worker installs the hook that withdraws
/// the queued fire and re-arms the scheduler.
pub type RlmHeartbeatMutationHook = std::sync::Arc<
    dyn Fn(RlmHeartbeatMutation) -> Pin<Box<dyn Future<Output = ()> + Send>> + Send + Sync,
>;

/// One handled `rlm_heartbeat.*` request: the wire response plus the
/// mutation the request made (catalog reads carry none).
#[derive(Debug)]
pub struct RlmHeartbeatHostOutcome {
    pub response: Value,
    pub mutation: Option<RlmHeartbeatMutation>,
}

/// Handle an `rlm_heartbeat.*` host request from the bundled rlm-heartbeat
/// skill. These heartbeats are internal to the active session and never read
/// or mutate the user-level /heartbeat.
///
/// # Errors
///
/// Returns an error when the request payload's fields are invalid, the
/// schedule text cannot be parsed, or the request type is unknown.
pub fn handle_rlm_heartbeat_host_request(
    request_type: &str,
    payload: &Value,
    store: &AgentCronJobStore,
    active_session_id: &str,
    binding: &SessionBinding,
) -> anyhow::Result<RlmHeartbeatHostOutcome> {
    let record = payload.as_object().cloned().unwrap_or_default();
    let string_field = |name: &str| -> anyhow::Result<Option<String>> {
        match record.get(name) {
            None | Some(Value::Null) => Ok(None),
            Some(value) => value
                .as_str()
                .map(|text| Some(text.to_string()))
                .ok_or_else(|| {
                    anyhow::anyhow!(
                        "rlm_heartbeat.{request_type} {name} must be a string when provided"
                    )
                }),
        }
    };
    let delivery_mode = match record.get("delivery_mode") {
        None | Some(Value::Null) => None,
        Some(value) => match value.as_str() {
            Some("steer") => Some(DeliveryMode::Steer),
            Some("follow_up") => Some(DeliveryMode::FollowUp),
            _ => anyhow::bail!(
                "rlm_heartbeat.{request_type} delivery_mode must be \"steer\" or \"follow_up\" when provided"
            ),
        },
    };
    let now = store_now();
    let mut create_input = CreateAgentCronJobInput {
        active_session_id: active_session_id.to_string(),
        session_id: binding.session_id.clone(),
        session_file: binding.session_file.clone(),
        cwd: binding.cwd.clone(),
        source: Some(JobSource::RlmHeartbeat),
        now: Some(now),
        ..Default::default()
    };
    match request_type {
        "rlm_heartbeat.list" => {
            let include_inactive =
                matches!(record.get("include_inactive"), Some(Value::Bool(true)));
            let heartbeats = store.list_rlm_heartbeats(active_session_id, include_inactive);
            Ok(RlmHeartbeatHostOutcome {
                response: json!({
                    "heartbeats": heartbeats
                        .iter()
                        .map(rlm_heartbeat_host_response)
                        .collect::<Vec<_>>(),
                }),
                // A catalog read mutates nothing: no post-mutation work.
                mutation: None,
            })
        }
        "rlm_heartbeat.create" => {
            let Some(instruction) = record.get("instruction").and_then(Value::as_str) else {
                anyhow::bail!("rlm_heartbeat.create instruction must be a string");
            };
            let interval = string_field("interval")?;
            let label = string_field("label")?;
            create_input.prompt = instruction.to_string();
            create_input.label = label;
            create_input.schedule_text = interval.unwrap_or_else(|| "every 5m".to_string());
            create_input.delivery_mode = delivery_mode;
            let heartbeat = store.create_rlm_heartbeat(&create_input)?;
            let response = json!({ "heartbeat": rlm_heartbeat_host_response(&heartbeat) });
            // TS `createRlmHeartbeatForState` never withdraws a queued
            // fire; it only wakes the scheduler.
            Ok(RlmHeartbeatHostOutcome {
                response,
                mutation: Some(RlmHeartbeatMutation {
                    job: heartbeat,
                    drop_queued: false,
                }),
            })
        }
        "rlm_heartbeat.update" => {
            let Some(id) = record.get("id").and_then(Value::as_str) else {
                anyhow::bail!("rlm_heartbeat.update id must be a string");
            };
            let instruction = string_field("instruction")?;
            let interval = string_field("interval")?;
            let label = string_field("label")?;
            let status = match record.get("status") {
                None | Some(Value::Null) => None,
                Some(Value::String(status)) => match status.as_str() {
                    "pause" => Some(RlmHeartbeatStatusUpdate::Pause),
                    "resume" => Some(RlmHeartbeatStatusUpdate::Resume),
                    _ => anyhow::bail!(
                        "rlm_heartbeat.update status must be \"pause\" or \"resume\" when provided"
                    ),
                },
                _ => anyhow::bail!(
                    "rlm_heartbeat.update status must be \"pause\" or \"resume\" when provided"
                ),
            };
            if instruction.is_none()
                && interval.is_none()
                && label.is_none()
                && status.is_none()
                && delivery_mode.is_none()
            {
                anyhow::bail!("rlm_heartbeat.update requires at least one field to update");
            }
            // TS `updateRlmHeartbeatForState`: instruction/interval/pause/
            // delivery updates withdraw the queued fire; label-only and
            // resume-only updates do not.
            let drop_queued = instruction.is_some()
                || interval.is_some()
                || status == Some(RlmHeartbeatStatusUpdate::Pause)
                || delivery_mode.is_some();
            let heartbeat = store.update_rlm_heartbeat(
                active_session_id,
                id,
                &RlmHeartbeatUpdate {
                    label,
                    prompt: instruction,
                    schedule_text: interval,
                    status,
                    delivery_mode,
                    now: Some(now),
                },
            )?;
            Ok(RlmHeartbeatHostOutcome {
                response: json!({
                    "heartbeat": heartbeat
                        .as_ref()
                        .map_or(Value::Null, rlm_heartbeat_host_response),
                }),
                // TS wakes only when the update found the job.
                mutation: heartbeat.map(|job| RlmHeartbeatMutation { job, drop_queued }),
            })
        }
        "rlm_heartbeat.delete" => {
            let Some(id) = record.get("id").and_then(Value::as_str) else {
                anyhow::bail!("rlm_heartbeat.delete id must be a string");
            };
            let heartbeat = store.delete_rlm_heartbeat(active_session_id, id, now)?;
            Ok(RlmHeartbeatHostOutcome {
                response: json!({
                    "heartbeat": heartbeat
                        .as_ref()
                        .map_or(Value::Null, rlm_heartbeat_host_response),
                }),
                // TS `deleteRlmHeartbeatForState` always withdraws the
                // queued fire of the deleted job.
                mutation: heartbeat.map(|job| RlmHeartbeatMutation {
                    job,
                    drop_queued: true,
                }),
            })
        }
        _ => anyhow::bail!("unknown RLM heartbeat request type \"{request_type}\""),
    }
}

/// The session identity fields heartbeat creation needs.
pub struct SessionBinding {
    pub session_id: String,
    pub session_file: String,
    pub cwd: String,
}

fn store_now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|duration| duration.as_millis() as u64)
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn binding() -> SessionBinding {
        SessionBinding {
            session_id: "session-1".to_string(),
            session_file: "/w/session.jsonl".to_string(),
            cwd: "/w".to_string(),
        }
    }

    fn heartbeat_store() -> AgentCronJobStore {
        let dir = tempfile::TempDir::new().unwrap();
        AgentCronJobStore::new(dir.path().join("jobs.json"))
    }

    #[test]
    fn rlm_heartbeat_host_requests() {
        let store = heartbeat_store();
        let bind = binding();
        // Create.
        let created = handle_rlm_heartbeat_host_request(
            "rlm_heartbeat.create",
            &json!({ "instruction": "watch pods", "interval": "every 10m", "label": "podwatch" }),
            &store,
            "live-1",
            &bind,
        )
        .unwrap();
        let heartbeat = created.response.get("heartbeat").cloned().unwrap();
        assert_eq!(heartbeat["status"], "active");
        assert_eq!(heartbeat["instruction"], "watch pods");
        assert_eq!(heartbeat["label"], "podwatch");
        assert_eq!(heartbeat["delivery_mode"], "steer");
        assert!(heartbeat["schedule"]["kind"].is_string());
        // Create carries the mutation (TS `createRlmHeartbeatForState`
        // wakes; it never withdraws a queued fire).
        let mutation = created.mutation.expect("create mutation");
        assert_eq!(mutation.job.id, heartbeat["id"].as_str().unwrap());
        assert_eq!(mutation.job.source, JobSource::RlmHeartbeat);
        assert_eq!(mutation.job.active_session_id, "live-1");
        assert!(!mutation.drop_queued);
        let id = heartbeat["id"].as_str().unwrap().to_string();
        // List.
        let listed = handle_rlm_heartbeat_host_request(
            "rlm_heartbeat.list",
            &json!({ "include_inactive": true }),
            &store,
            "live-1",
            &bind,
        )
        .unwrap();
        assert_eq!(listed.response["heartbeats"].as_array().unwrap().len(), 1);
        assert!(listed.mutation.is_none(), "a catalog read mutates nothing");
        // Update with pause.
        let paused = handle_rlm_heartbeat_host_request(
            "rlm_heartbeat.update",
            &json!({ "id": id, "status": "pause" }),
            &store,
            "live-1",
            &bind,
        )
        .unwrap();
        assert_eq!(paused.response["heartbeat"]["status"], "paused");
        // A pause withdraws the queued fire (TS `updateRlmHeartbeatForState`).
        let mutation = paused.mutation.expect("pause mutation");
        assert!(mutation.drop_queued);
        // Update requires a field.
        let error = handle_rlm_heartbeat_host_request(
            "rlm_heartbeat.update",
            &json!({ "id": id }),
            &store,
            "live-1",
            &bind,
        )
        .unwrap_err();
        assert!(error.to_string().contains("at least one field"));
        // Resume does not withdraw the queued fire (TS: resume-only keeps it).
        let resumed = handle_rlm_heartbeat_host_request(
            "rlm_heartbeat.update",
            &json!({ "id": id, "status": "resume" }),
            &store,
            "live-1",
            &bind,
        )
        .unwrap();
        assert_eq!(resumed.response["heartbeat"]["status"], "active");
        assert!(!resumed.mutation.expect("resume mutation").drop_queued);
        // Delete.
        let deleted = handle_rlm_heartbeat_host_request(
            "rlm_heartbeat.delete",
            &json!({ "id": id }),
            &store,
            "live-1",
            &bind,
        )
        .unwrap();
        assert_eq!(deleted.response["heartbeat"]["status"], "cancelled");
        assert!(deleted.mutation.expect("delete mutation").drop_queued);
        // Deleting again re-cancels (the TS delete does not check status).
        let again = handle_rlm_heartbeat_host_request(
            "rlm_heartbeat.delete",
            &json!({ "id": id }),
            &store,
            "live-1",
            &bind,
        )
        .unwrap();
        assert_eq!(again.response["heartbeat"]["status"], "cancelled");
        // Unknown type.
        let error = handle_rlm_heartbeat_host_request(
            "rlm_heartbeat.nope",
            &json!({}),
            &store,
            "live-1",
            &bind,
        )
        .unwrap_err();
        assert!(error
            .to_string()
            .contains("unknown RLM heartbeat request type"));
    }
}
