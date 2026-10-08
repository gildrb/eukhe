//! The model/setting switches (protocol breadth wave b3): the worker arms
//! for the daemon commands that flip live session settings — `cycle_model`,
//! `set_scoped_models`, `cycle_thinking_level`, `set_service_tier`,
//! `set_transport`, `set_steering_mode`, `set_follow_up_mode`,
//! `set_auto_compaction`, `set_auto_retry`, `abort_retry` (TS daemon-mode
//! cases). The wire contracts are TS-verbatim. Model and thinking switches
//! configure the main conversation (`model_switch`); everything else is a
//! settings write the Harness reads per use (`EukheSettings` reloads on
//! change), and the connection state reads the same settings back.

use std::path::Path;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::settings::{QueueModeSetting, SettingsManager, TransportSetting};
use eukhe_durable::harness::types::ConversationAbortOptions;
use eukhe_pi_ai::auth::AuthOperationOptions;
use eukhe_pi_ai::models::get_supported_thinking_levels;
use eukhe_types::ai::{ServiceTier, Transport};
use eukhe_types::pi_ai::{Model, ModelThinkingLevel};
use serde_json::{json, Value};

use crate::model_switch::{apply_model, THINKING_LEVELS};
use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::durable_host::suspended::WithdrawnInput;
use crate::worker::{model_metadata, Worker};

/// The queue-mode wire vocabulary (TS `AgentConnectionQueueMode`).
const QUEUE_MODES: &[&str] = &["all", "one-at-a-time"];

/// TS `supportsServiceTier` over the shown model's wire metadata
/// (provider, api, id) against the shared eukhe-types eligibility fields.
/// A session without a resolved catalog model supports only the `default`
/// tier, exactly like the TS `model == null` arm.
pub(crate) fn model_supports_service_tier(model: Option<&Value>, tier: ServiceTier) -> bool {
    model
        .and_then(|model| {
            Some(eukhe_types::ai::supports_service_tier_fields(
                model.get("provider")?.as_str()?,
                model.get("api")?.as_str()?,
                model.get("id")?.as_str()?,
                tier,
            ))
        })
        // TS `supportsServiceTier` answers the default tier true for any
        // model, including none.
        .unwrap_or(tier == ServiceTier::Default)
}

/// The wire name of a service tier (the serde lowercase form).
pub(crate) fn service_tier_wire_name(tier: ServiceTier) -> &'static str {
    match tier {
        ServiceTier::Auto => "auto",
        ServiceTier::Default => "default",
        ServiceTier::Flex => "flex",
        ServiceTier::Scale => "scale",
        ServiceTier::Priority => "priority",
    }
}

/// TS `_getEffectiveServiceTier` (#2144's `clampServiceTier`): a tier the
/// model does not support degrades to `default`. An unset (`null`)
/// preference passes through; `None` on the wire reads as `auto` (see
/// [`service_tier_wire_name`]).
pub(crate) fn effective_service_tier(
    tier: Option<ServiceTier>,
    model: Option<&Value>,
) -> Option<ServiceTier> {
    match tier {
        None | Some(ServiceTier::Default) => tier,
        Some(tier) => model_supports_service_tier(model, tier)
            .then_some(tier)
            .or(Some(ServiceTier::Default)),
    }
}

/// The `cycle_model` candidates: the scoped entries that are available,
/// each with its pinned level, else the whole available catalog (TS
/// `_cycleScopedModel` / `_cycleAvailableModel`).
fn cycle_candidates(
    scoped: &[Value],
    available: Vec<Model>,
) -> Vec<(Option<ModelThinkingLevel>, Model)> {
    if scoped.is_empty() {
        return available.into_iter().map(|model| (None, model)).collect();
    }
    scoped
        .iter()
        .filter_map(|entry| {
            let model = entry.get("model")?;
            let provider = model.get("provider")?.as_str()?;
            let id = model.get("id")?.as_str()?;
            let candidate = available
                .iter()
                .find(|candidate| candidate.provider == provider && candidate.id == id)?;
            let level = entry
                .get("thinkingLevel")
                .and_then(Value::as_str)
                .and_then(ModelThinkingLevel::parse);
            Some((level, candidate.clone()))
        })
        .collect()
}

impl Worker {
    /// `cycle_model { direction? }` (TS `session.cycleModel`): cycle within
    /// the scoped model list when one is set (each entry clamped to the
    /// available catalog), else within the available catalog. Fewer than
    /// two candidates answer success with `null` data, like TS.
    pub(crate) async fn handle_cycle_model(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "cycle_model";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        // Same serialization as `set_model`: the cycle's switch and tier
        // re-clamp run under the replacement gate.
        let _replacement_gate = self.replacement_gate.lock().await;
        let backward = payload.get("direction").and_then(Value::as_str) == Some("backward");
        let scoped = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .scoped_models
            .clone();
        let current = match hosted.main() {
            Ok(main) => match main.agent(&BACKGROUND_CONTEXT).await {
                Ok(agent) => agent.model,
                Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
            },
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        let available = match hosted
            .deps()
            .models
            .get_available(None, AuthOperationOptions::default())
            .await
        {
            Ok(available) => available,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        let is_scoped = !scoped.is_empty();
        let candidates = cycle_candidates(&scoped, available);
        if candidates.len() <= 1 {
            // TS `result ?? null`: no cycle happened.
            return response_success(None, COMMAND, Some(Value::Null));
        }
        let current_index = current
            .and_then(|current| {
                candidates.iter().position(|(_, model)| {
                    model.provider == current.provider && model.id == current.model_id
                })
            })
            .unwrap_or(0);
        let len = candidates.len();
        let next_index = if backward {
            (current_index + len - 1) % len
        } else {
            (current_index + 1) % len
        };
        let (scoped_thinking, next_model) = &candidates[next_index];
        // The daemon model allowlist gate, before the switch: an off-list
        // candidate answers the cycle with the loud refusal.
        if let Some(refusal) = self.model_allowlist_refusal(COMMAND, next_model) {
            return refusal;
        }
        // A scoped entry may pin the level for the switched-to model (TS
        // `_getThinkingLevelForModelSwitch(next.thinkingLevel)`).
        let thinking_level = match apply_model(&hosted, next_model, *scoped_thinking).await {
            Ok(level) => level,
            Err(error) => return response_failure(None, COMMAND, &error, None),
        };
        // The clamp runs BEFORE the roster flush so the published snapshot
        // carries the clamped tier with the switched-to model.
        self.clamp_service_tier_for_model();
        self.push_roster_delta();
        let service_tier = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .active_service_tier
            .unwrap_or(ServiceTier::Auto);
        response_success(
            None,
            COMMAND,
            Some(json!({
                "model": next_model,
                "thinkingLevel": thinking_level.as_str(),
                "serviceTier": service_tier_wire_name(service_tier),
                "isScoped": is_scoped,
            })),
        )
    }

    /// Re-clamp the active service tier for the shown model (TS
    /// `_clampServiceTierForModel` on a model switch, #2144's
    /// `clampServiceTier`): a preference the model does not support
    /// degrades to `default`; the `service_tier_changed` event fires only
    /// when the ACTIVE tier moves. The stored preference keeps the
    /// requested tier, so switching back to (or resuming on) a capable
    /// model re-applies it.
    pub(crate) fn clamp_service_tier_for_model(&self) {
        let (changed, clamped) = {
            let mut core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let model = model_metadata(&core, &self.session);
            let clamped = effective_service_tier(core.service_tier, model.as_ref());
            let previous_active = core.active_service_tier;
            core.active_service_tier = clamped;
            (clamped != previous_active, clamped)
        };
        if changed {
            self.emit_worker_event(json!({
                "type": "service_tier_changed",
                "serviceTier": service_tier_wire_name(clamped.unwrap_or(ServiceTier::Auto)),
            }));
        }
    }

    /// The replacement sessions (`new_session` / `switch_session` /
    /// `import_jsonl` / `fork`) re-seed the service tier like a create: the
    /// settings default preference, then the active tier re-clamps against
    /// the restored model (the clamp's event contract).
    pub(crate) fn reseed_service_tier_for_replacement(&self) {
        let cwd = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .cwd
            .clone();
        let default_tier =
            SettingsManager::create(&cwd, &self.config.agent_dir).get_default_service_tier();
        self.core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .service_tier = Some(default_tier);
        self.clamp_service_tier_for_model();
    }

    /// `set_scoped_models { scopedModels }` (TS
    /// `session.setScopedModels`): store the scoped model list the cycler
    /// and the connection state surface.
    pub(crate) fn handle_set_scoped_models(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_scoped_models";
        if let Err(response) = self.require_created(COMMAND) {
            return response;
        }
        let Some(scoped) = payload.get("scopedModels").and_then(Value::as_array) else {
            return response_failure(
                None,
                COMMAND,
                "set_scoped_models requires a scopedModels array",
                None,
            );
        };
        for entry in scoped {
            let model = entry
                .get("model")
                .and_then(Value::as_object)
                .filter(|model| {
                    model.get("provider").and_then(Value::as_str).is_some()
                        && model.get("id").and_then(Value::as_str).is_some()
                });
            if model.is_none() {
                return response_failure(
                    None,
                    COMMAND,
                    "set_scoped_models requires scopedModels entries with a model",
                    None,
                );
            }
            if let Some(level) = entry.get("thinkingLevel") {
                if level.as_str().and_then(ModelThinkingLevel::parse).is_none() {
                    return response_failure(
                        None,
                        COMMAND,
                        &format!(
                            "Invalid thinking level: expected one of {}",
                            THINKING_LEVELS.join(", ")
                        ),
                        None,
                    );
                }
            }
        }
        self.core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .scoped_models
            .clone_from(scoped);
        response_success(None, COMMAND, None)
    }

    /// `cycle_thinking_level` (TS `session.cycleThinkingLevel`): models
    /// without reasoning answer success with `null` data; reasoning models
    /// cycle through their supported levels (the `set_thinking_level`
    /// flow).
    pub(crate) async fn handle_cycle_thinking_level(&self) -> DaemonResponse {
        const COMMAND: &str = "cycle_thinking_level";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let agent = match hosted.main() {
            Ok(main) => match main.agent(&BACKGROUND_CONTEXT).await {
                Ok(agent) => agent,
                Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
            },
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        // TS `supportsThinking()`: the model must support reasoning.
        let Some(model) = agent
            .model
            .as_ref()
            .and_then(|model| {
                hosted
                    .deps()
                    .models
                    .get_model(&model.provider, &model.model_id)
            })
            .filter(|model| model.reasoning)
        else {
            return response_success(None, COMMAND, Some(Value::Null));
        };
        let levels = get_supported_thinking_levels(&model);
        let Some(first) = levels.first() else {
            return response_success(None, COMMAND, Some(Value::Null));
        };
        // TS: `indexOf` -1 cycles to the first level.
        let next = levels
            .iter()
            .position(|level| *level == agent.thinking_level)
            .map_or(*first, |index| levels[(index + 1) % levels.len()]);
        let applied = self
            .handle_set_thinking_level(&json!({ "level": next.as_str() }))
            .await;
        if !applied.success {
            return applied;
        }
        response_success(None, COMMAND, Some(json!({ "level": next.as_str() })))
    }

    /// `set_service_tier { serviceTier }` (TS `session.setServiceTier`,
    /// #2144 semantics): the preference keeps the REQUESTED tier (only the
    /// active state clamps), so switching to a capable model re-applies it;
    /// the settings default (which the durable stream reads) persists only
    /// when the model supports the tier; and the `service_tier_changed`
    /// event follows an effective change. An unchanged request answers
    /// success without side effects.
    pub(crate) async fn handle_set_service_tier(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_service_tier";
        if let Err(response) = self.require_created(COMMAND) {
            return response;
        }
        // The tier mutation runs under the replacement gate so a session
        // swap's re-seed never interleaves with it.
        let _replacement_gate = self.replacement_gate.lock().await;
        let Some(tier) = payload
            .get("serviceTier")
            .cloned()
            .filter(|value| !value.is_null())
            .and_then(|value| serde_json::from_value::<ServiceTier>(value).ok())
        else {
            return response_failure(
                None,
                COMMAND,
                "set_service_tier requires a serviceTier",
                None,
            );
        };
        let (preference_changed, effective_changed, supported, effective, cwd) = {
            let mut core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let model = model_metadata(&core, &self.session);
            let effective = effective_service_tier(Some(tier), model.as_ref()).unwrap_or(tier);
            let supported = model_supports_service_tier(model.as_ref(), tier);
            let preference_changed = core.service_tier != Some(tier);
            let effective_changed = core.active_service_tier != Some(effective);
            core.service_tier = Some(tier);
            core.active_service_tier = Some(effective);
            (
                preference_changed,
                effective_changed,
                supported,
                effective,
                core.cwd.clone(),
            )
        };
        if preference_changed && supported {
            // TS persists the default only when the model supports the
            // tier (#2144: `supportsServiceTier(this.model, serviceTier)`).
            let mut settings = SettingsManager::create(&cwd, &self.config.agent_dir);
            if let Err(error) = settings.set_default_service_tier(tier) {
                // The session already switched; the default is best-effort
                // like TS.
                eprintln!(
                    "eukhe-daemon worker: persisting the default service tier failed: {error}"
                );
            }
        }
        if effective_changed {
            self.emit_worker_event(json!({
                "type": "service_tier_changed",
                "serviceTier": service_tier_wire_name(effective),
            }));
        }
        response_success(None, COMMAND, None)
    }

    /// `set_transport { transport }` (TS `settingsManager.setTransport` +
    /// `agent.transport`): persist the transport setting. The live stream
    /// resolves transport per request from settings, so the persisted
    /// default is the whole switch.
    pub(crate) fn handle_set_transport(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_transport";
        if let Err(response) = self.require_created(COMMAND) {
            return response;
        }
        let Some(transport) = payload
            .get("transport")
            .cloned()
            .and_then(|value| serde_json::from_value::<Transport>(value).ok())
        else {
            return response_failure(None, COMMAND, "set_transport requires a transport", None);
        };
        let setting = match transport {
            Transport::Auto => TransportSetting::Auto,
            Transport::Sse => TransportSetting::Sse,
            Transport::Websocket | Transport::WebsocketCached => TransportSetting::WebSocket,
        };
        if let Err(error) = self.settings().set_transport(setting) {
            return response_failure(None, COMMAND, &error.to_string(), None);
        }
        response_success(None, COMMAND, None)
    }

    /// `set_steering_mode` / `set_follow_up_mode { mode }` (TS
    /// `session.setSteeringMode` / `setFollowUpMode`): the queue delivery
    /// mode, persisted to settings; the session's inbox placement and the
    /// connection state read it back.
    pub(crate) fn handle_set_queue_mode(&self, command: &str, payload: &Value) -> DaemonResponse {
        if let Err(response) = self.require_created(command) {
            return response;
        }
        let setting = match payload.get("mode").and_then(Value::as_str) {
            Some(mode) if mode == QUEUE_MODES[0] => QueueModeSetting::All,
            Some(mode) if mode == QUEUE_MODES[1] => QueueModeSetting::OneAtATime,
            _ => {
                return response_failure(
                    None,
                    command,
                    &format!("{command} requires mode \"all\" or \"one-at-a-time\""),
                    None,
                );
            }
        };
        let mut settings = self.settings();
        let persisted = if command == "set_steering_mode" {
            settings.set_steering_mode(setting)
        } else {
            settings.set_follow_up_mode(setting)
        };
        if let Err(error) = persisted {
            return response_failure(None, command, &error.to_string(), None);
        }
        response_success(None, command, None)
    }

    /// `set_auto_retry { enabled }` (TS `session.setAutoRetryEnabled`):
    /// the provider retry policy reads the setting on every request.
    pub(crate) fn handle_set_auto_retry(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_auto_retry";
        if let Err(response) = self.require_created(COMMAND) {
            return response;
        }
        let Some(enabled) = payload.get("enabled").and_then(Value::as_bool) else {
            return response_failure(None, COMMAND, "set_auto_retry requires enabled", None);
        };
        if let Err(error) = self.settings().set_retry_enabled(enabled) {
            return response_failure(None, COMMAND, &error.to_string(), None);
        }
        response_success(None, COMMAND, None)
    }

    /// `set_auto_compaction { enabled }` (TS
    /// `session.setAutoCompactionEnabled` →
    /// `settingsManager.setCompactionEnabled`): the settings value is the
    /// switch — the Harness's compaction policy and the connection state
    /// both read it, so a restarted session keeps it. A failed settings
    /// save fails the command and flips nothing.
    pub(crate) fn handle_set_auto_compaction(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_auto_compaction";
        if let Err(response) = self.require_created(COMMAND) {
            return response;
        }
        let enabled = payload
            .get("enabled")
            .and_then(Value::as_bool)
            .unwrap_or(false);
        if let Err(error) = self.settings().set_compaction_enabled(enabled) {
            return response_failure(None, COMMAND, &error.to_string(), None);
        }
        response_success(None, COMMAND, None)
    }

    /// `abort_retry` (TS `session.abortRetry`): stop an in-flight provider
    /// retry. A retry is part of the main conversation's run, so stopping
    /// it aborts the run; the queued inputs the abort withdraws stay
    /// suspended (shown, resubmitted by `resume_queue`), like `abort`.
    /// Without a retry in progress the command is a success no-op.
    pub(crate) async fn handle_abort_retry(&self) -> DaemonResponse {
        const COMMAND: &str = "abort_retry";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let withdrawn = {
            let core = self
                .core
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            core.view
                .as_ref()
                .filter(|view| view.translator.mirror().retry_attempt.is_some())
                .map(|view| view.inbox.clone())
        };
        let Some(withdrawn) = withdrawn else {
            return response_success(None, COMMAND, None);
        };
        let aborted = match hosted.main() {
            Ok(main) => main
                .abort(ConversationAbortOptions::default(), &BACKGROUND_CONTEXT)
                .await
                .map_err(|error| error.to_string()),
            Err(error) => Err(error.to_string()),
        };
        if let Err(error) = aborted {
            return response_failure(None, COMMAND, &error, None);
        }
        if let Err(error) =
            crate::worker::mutate_withdrawn(&hosted, &self.core, &self.events, move |mut state| {
                state
                    .suspended
                    .extend(withdrawn.iter().map(WithdrawnInput::from));
                (state, ())
            })
            .await
        {
            return response_failure(None, COMMAND, &error, None);
        }
        self.emit_action_update();
        hosted.events_delivered().await;
        response_success(None, COMMAND, None)
    }

    /// The session's settings manager for a write (the session cwd's
    /// project scope over this worker's agent dir).
    fn settings(&self) -> SettingsManager {
        let cwd = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .cwd
            .clone();
        SettingsManager::create(Path::new(&cwd), &self.config.agent_dir)
    }
}

#[cfg(test)]
mod tests;
