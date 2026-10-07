//! The `factory_activity` worker arm: the `/factory` view's daemon lane.

//! One session-addressed command reaches the main conversation's kernel
//! factory executor (`eukhe_core::durable::rlm::kernel_factory_activity`):
//! the payload's `action` rides the out-of-band kernel frame, and the
//! kernel's reply returns verbatim (the run registry stays kernel-owned).
//! The `run` action's model preflight (the allowlist pin, request auth)
//! happens before the frame — a doomed run fails before any child spawns.

use std::path::Path;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::rlm::kernel_factory_activity;
use eukhe_core::session_engine::factory_host::FactoryActivityRequest;
use serde_json::Value;

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::Worker;

/// The `factory_activity` capability's advertisement gate: the factory is
/// opt-in (`factory.enabled` in the shared settings file, default off),
/// so a disabled factory never surfaces its lane — no capability, no
/// dock group, no page. Both hello surfaces (the supervisor's and the
/// worker's) advertise the lane only while the setting reads enabled.
pub(crate) fn factory_lane_enabled(agent_dir: &Path) -> bool {
    eukhe_core::settings::SettingsManager::create(
        std::env::current_dir().unwrap_or_default(),
        agent_dir,
    )
    .get_factory_enabled()
}

/// The capabilities a hello advertises: the default set, minus the
/// `factory_activity` lane while the factory stays disabled (the opt-in
/// gate; the settings read is fresh per connection, so a `/factory on`
/// toggle surfaces on the next client start).
pub(crate) fn advertised_server_capabilities(agent_dir: &Path) -> Vec<String> {
    let mut capabilities = crate::protocol::default_server_capabilities();
    if !factory_lane_enabled(agent_dir) {
        capabilities.retain(|capability| capability != "factory_activity");
    }
    capabilities
}

impl Worker {
    /// `factory_activity`: one factory action over the main conversation's
    /// kernel (never booting one: "Kernel is not running" otherwise). A
    /// `run` is model-preflighted first (the allowlist pin, request auth).
    pub(crate) async fn handle_factory_activity(&self, payload: &Value) -> DaemonResponse {
        let hosted = match self.hosted("factory_activity") {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let action = payload
            .get("action")
            .and_then(Value::as_str)
            .unwrap_or_default();
        if action.is_empty() {
            return response_failure(None, "factory_activity", "action is required", None);
        }
        let request = match FactoryActivityRequest::parse(
            action,
            payload.get("runId").and_then(Value::as_str),
            payload.get("specId").and_then(Value::as_str),
            payload.get("timeoutMs").and_then(Value::as_u64),
        ) {
            Ok(request) => request,
            Err(error) => {
                return response_failure(None, "factory_activity", &format!("{error:#}"), None)
            }
        };
        let main = match hosted.main() {
            Ok(main) => main,
            Err(error) => {
                return response_failure(None, "factory_activity", &error.to_string(), None)
            }
        };
        match kernel_factory_activity(hosted.deps(), &main, request, &BACKGROUND_CONTEXT).await {
            Ok(result) => response_success(None, "factory_activity", Some(result)),
            Err(error) => response_failure(None, "factory_activity", &error.to_string(), None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The opt-in default: no settings file, no factory lane.
    #[test]
    fn the_factory_lane_stays_unadvertised_until_enabled() {
        let dir = tempfile::TempDir::new().expect("temp dir");
        let agent_dir = dir.path().join("agent");
        std::fs::create_dir_all(&agent_dir).expect("agent dir");

        let disabled = advertised_server_capabilities(&agent_dir);
        assert!(
            !disabled
                .iter()
                .any(|capability| capability == "factory_activity"),
            "the default factory gate stays off: {disabled:?}"
        );

        // `/factory on` persists `factory.enabled` in the settings file —
        // the exact shared key the lane advertisement reads.
        let settings = serde_json::json!({ "factory": { "enabled": true } });
        std::fs::write(
            agent_dir.join("settings.json"),
            serde_json::to_string(&settings).expect("serialize"),
        )
        .expect("write settings");
        let enabled = advertised_server_capabilities(&agent_dir);
        assert!(
            enabled
                .iter()
                .any(|capability| capability == "factory_activity"),
            "the enabled factory advertises its lane: {enabled:?}"
        );

        // `/factory off` re-reads as disabled: the lane leaves the
        // advertisement again.
        let off = serde_json::json!({ "factory": { "enabled": false } });
        std::fs::write(
            agent_dir.join("settings.json"),
            serde_json::to_string(&off).expect("serialize"),
        )
        .expect("write settings");
        let disabled_again = advertised_server_capabilities(&agent_dir);
        assert!(
            !disabled_again
                .iter()
                .any(|capability| capability == "factory_activity"),
            "the disabled factory lane leaves the advertisement: {disabled_again:?}"
        );
    }

    /// The lane validates the request, then answers the definitive
    /// refusal while the session's kernel never booted.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn factory_activity_validates_and_never_boots_a_kernel() {
        let (_dir, worker) = crate::durable_test_support::created_worker(
            "factory-session",
            serde_json::json!(["ack"]),
        )
        .await;
        let session = serde_json::json!({ "activeSessionId": "factory-session" });
        let missing = worker.dispatch("factory_activity", &session).await;
        assert_eq!(missing.error.as_deref(), Some("action is required"));
        let unknown = worker
            .dispatch(
                "factory_activity",
                &serde_json::json!({ "activeSessionId": "factory-session", "action": "nope" }),
            )
            .await;
        assert_eq!(
            unknown.error.as_deref(),
            Some("unknown factory activity action")
        );
        let graph = worker
            .dispatch(
                "factory_activity",
                &serde_json::json!({ "activeSessionId": "factory-session", "action": "graph" }),
            )
            .await;
        assert_eq!(graph.error.as_deref(), Some("Kernel is not running"));
    }
}
