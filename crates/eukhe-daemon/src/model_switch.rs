//! The live model/thinking switches: the worker arms for the daemon
//! `set_model` and `set_thinking_level` commands (TS daemon-mode
//! `case "set_model"` / `case "set_thinking_level"`). The hosted session's
//! main conversation owns the switch (`pi.agent` through
//! `Conversation::configure`); this module owns the wire contract:
//! resolution through the session's model collection, the daemon model
//! allowlist, the sign-in refusal, the settings defaults the TS session
//! persists on a switch, and the response data.

use std::path::Path;

use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::thinking_level;
use eukhe_core::models::{ModelAllowlistRefusal, SetModelSelectionError};
use eukhe_core::settings::{SettingsManager, ThinkingLevelSetting};
use eukhe_durable::harness::types::{AgentChange, FieldChange, ModelRef};
use eukhe_pi_ai::auth::AuthOperationOptions;
use eukhe_pi_ai::models::clamp_thinking_level;
use eukhe_types::pi_ai::{Model, ModelThinkingLevel};
use serde_json::Value;

use crate::protocol::{response_failure, response_success, DaemonResponse};
use crate::worker::{HostedSession, Worker};

/// The wire levels a thinking switch accepts (TS `ThinkingLevel`).
pub(crate) const THINKING_LEVELS: &[&str] =
    &["off", "minimal", "low", "medium", "high", "xhigh", "max"];

/// Why a `(provider, modelId)` pair did not resolve to an available model.
#[derive(Debug)]
pub(crate) enum ModelResolutionError {
    /// The TS refusal classes: the provider is not signed in, or no such
    /// model is available.
    Selection(SetModelSelectionError),
    /// The credential store or a provider catalog could not be read.
    Models(String),
}

impl ModelResolutionError {
    /// The command failure for this resolution error: the sign-in refusal
    /// carries the typed `errorInfo` (the client offers the provider's
    /// sign-in flow and retries), every other class is a plain failure.
    pub(crate) fn response(&self, command: &str) -> DaemonResponse {
        match self {
            Self::Selection(refusal) => response_failure(
                None,
                command,
                &refusal.to_string(),
                refusal.unauthenticated_provider().map(|provider| {
                    eukhe_types::daemon::DaemonErrorInfo::ModelProviderUnauthenticated {
                        provider: provider.to_string(),
                    }
                }),
            ),
            Self::Models(message) => response_failure(None, command, message, None),
        }
    }
}

impl Worker {
    /// `set_model { provider, modelId }`: resolve the model in the
    /// session's available catalog, enforce the daemon model allowlist
    /// (settings `allowedModels`: a model outside the allowlist fails
    /// loudly, never a fallback), switch the main conversation (the
    /// thinking level clamps to the new model), and persist the settings
    /// default (TS `session.setModel`). Unknown models fail with the TS
    /// message; a model whose provider is not signed in fails with the
    /// typed sign-in refusal.
    pub(crate) async fn handle_set_model(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_model";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        // Worker commands dispatch concurrently: a model switch (the
        // configure commit and the tier re-clamp) runs under the
        // replacement gate so a session swap can never interleave with it.
        let _replacement_gate = self.replacement_gate.lock().await;
        let Some(provider) = payload.get("provider").and_then(Value::as_str) else {
            return response_failure(None, COMMAND, "set_model requires a provider", None);
        };
        let Some(model_id) = payload.get("modelId").and_then(Value::as_str) else {
            return response_failure(None, COMMAND, "set_model requires a modelId", None);
        };
        let model = match resolve_available_model(&hosted, provider, model_id).await {
            Ok(model) => model,
            Err(error) => return error.response(COMMAND),
        };
        if let Some(refusal) = self.model_allowlist_refusal(COMMAND, &model) {
            return refusal;
        }
        if let Err(error) = apply_model(&hosted, &model, None).await {
            return response_failure(None, COMMAND, &error, None);
        }
        // TS `session.setModel` re-clamps the tier for the switched model
        // (`_clampServiceTierForModel`): a preference the new model does
        // not support degrades to `default` and the `service_tier_changed`
        // event follows the flip.
        self.clamp_service_tier_for_model();
        // The switched model reaches the roster surfaces immediately (the
        // TS handler schedules a roster flush after the switch).
        self.push_roster_delta();
        response_success(
            None,
            COMMAND,
            Some(serde_json::to_value(&model).unwrap_or(Value::Null)),
        )
    }

    /// `set_thinking_level { level }`: clamp the requested level to the
    /// model's supported levels and switch the main conversation only when
    /// the effective level changed (TS `session.setThinkingLevel`). The
    /// settings default follows like the TS session's
    /// `setDefaultThinkingLevel`.
    pub(crate) async fn handle_set_thinking_level(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_thinking_level";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let Some(level) = payload.get("level").and_then(Value::as_str) else {
            return response_failure(
                None,
                COMMAND,
                "Invalid thinking level: expected a string",
                None,
            );
        };
        let Some(requested) = ModelThinkingLevel::parse(level) else {
            return response_failure(
                None,
                COMMAND,
                &format!(
                    "Invalid thinking level \"{level}\". Valid values: {}",
                    THINKING_LEVELS.join(", ")
                ),
                None,
            );
        };
        match apply_thinking_level(&hosted, requested).await {
            Ok(changed) => {
                // The changed level reaches the roster surfaces right
                // away (the TS `thinking_level_changed` roster trigger).
                if changed {
                    self.push_roster_delta();
                }
                response_success(None, COMMAND, None)
            }
            Err(error) => response_failure(None, COMMAND, &error, None),
        }
    }

    /// The daemon model allowlist gate for `model` (settings
    /// `allowedModels`): `None` when allowed, else the loud command
    /// failure. The typed refusal also emits the adoption event (`model
    /// refused`); a fail-closed unreadable-allowlist error is a settings
    /// problem, not an allowlist refusal, and emits nothing.
    pub(crate) fn model_allowlist_refusal(
        &self,
        command: &str,
        model: &Model,
    ) -> Option<DaemonResponse> {
        let selector = format!("{}/{}", model.provider, model.id);
        let cwd = self
            .core
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .cwd
            .clone();
        let cwd = Path::new(&cwd);
        let allowlist = crate::model_allowlist::load(cwd, &self.config.agent_dir);
        let refusal = crate::model_allowlist::assert_allowed(&allowlist, &selector).err()?;
        if refusal.downcast_ref::<ModelAllowlistRefusal>().is_some() {
            self.model_refusal_telemetry
                .note_refused(command, &selector, cwd);
        }
        Some(response_failure(None, command, &refusal.to_string(), None))
    }
}

/// Resolve one `(provider, modelId)` pair against the session's available
/// catalog (models whose providers have credentials, TS
/// `refreshAvailableModels` + `find`). A catalog model whose provider has
/// no credential is the typed sign-in refusal; anything else absent from
/// the available list keeps the TS "Model not found" refusal.
pub(crate) async fn resolve_available_model(
    hosted: &HostedSession,
    provider: &str,
    model_id: &str,
) -> Result<Model, ModelResolutionError> {
    let models = &hosted.deps().models;
    let available = models
        .get_available(Some(provider), AuthOperationOptions::default())
        .await
        .map_err(|error| ModelResolutionError::Models(error.to_string()))?;
    if let Some(model) = available.into_iter().find(|model| model.id == model_id) {
        return Ok(model);
    }
    let not_found = || {
        ModelResolutionError::Selection(SetModelSelectionError::NotFound {
            provider: provider.to_string(),
            model_id: model_id.to_string(),
        })
    };
    if models.get_model(provider, model_id).is_none() {
        return Err(not_found());
    }
    let auth = models
        .check_auth(provider, AuthOperationOptions::default())
        .await
        .map_err(|error| ModelResolutionError::Models(error.to_string()))?;
    match auth {
        None => Err(ModelResolutionError::Selection(
            SetModelSelectionError::ProviderUnauthenticated {
                provider: provider.to_string(),
            },
        )),
        // A signed-in provider whose filter excludes the model (an
        // unauthorized private model): the TS refusal, never a switch.
        Some(_) => Err(not_found()),
    }
}

/// Switch the main conversation to `model` in one `configure` commit: the
/// model and the thinking level, clamped to what the model supports (TS
/// `_getThinkingLevelForModelSwitch`: `thinking` when given; else, leaving
/// a model that cannot think, the settings default level (else `medium`),
/// so switching back restores the level saved while a reasoning model was
/// active; else the current level). Then the settings default model (TS
/// `session.setModel` persists it so the next session starts here).
/// Returns the applied level once the event mirror shows the switch.
pub(crate) async fn apply_model(
    hosted: &HostedSession,
    model: &Model,
    thinking: Option<ModelThinkingLevel>,
) -> Result<ModelThinkingLevel, String> {
    let main = hosted.main().map_err(|error| error.to_string())?;
    let cx = &BACKGROUND_CONTEXT;
    let deps = hosted.deps();
    let current = if let Some(level) = thinking {
        level
    } else {
        let agent = main.agent(cx).await.map_err(|error| error.to_string())?;
        let current_thinks = agent
            .model
            .as_ref()
            .and_then(|current| deps.models.get_model(&current.provider, &current.model_id))
            .is_some_and(|current| current.reasoning);
        if current_thinks {
            agent.thinking_level
        } else {
            SettingsManager::create(&deps.cwd, &deps.agent_dir)
                .get_default_thinking_level()
                .map_or(ModelThinkingLevel::Medium, thinking_level)
        }
    };
    let level = clamp_thinking_level(model, current);
    main.configure(
        AgentChange {
            model: FieldChange::Set(ModelRef {
                provider: model.provider.clone(),
                model_id: model.id.clone(),
            }),
            thinking_level: FieldChange::Set(level),
            ..AgentChange::default()
        },
        cx,
    )
    .await
    .map_err(|error| error.to_string())?;
    // The tier re-clamp and the roster push read the mirror.
    hosted.events_delivered().await;
    let mut settings = SettingsManager::create(&deps.cwd, &deps.agent_dir);
    if let Err(error) = settings.set_default_model_and_provider(&model.provider, &model.id) {
        // The switch itself landed; the default is best-effort like TS.
        eprintln!("eukhe-daemon worker: persisting the default model failed: {error}");
    }
    Ok(level)
}

/// Apply one thinking level to the main conversation, clamped to the
/// current model's supported levels. Only an effective change configures
/// and persists the settings default (when the model can think or the
/// level is a real reasoning request, TS parity; the persisted value is
/// the clamped level). Returns whether the effective level changed.
pub(crate) async fn apply_thinking_level(
    hosted: &HostedSession,
    requested: ModelThinkingLevel,
) -> Result<bool, String> {
    let main = hosted.main().map_err(|error| error.to_string())?;
    let cx = &BACKGROUND_CONTEXT;
    let agent = main.agent(cx).await.map_err(|error| error.to_string())?;
    let deps = hosted.deps();
    let model = agent
        .model
        .as_ref()
        .and_then(|model| deps.models.get_model(&model.provider, &model.model_id));
    let effective = model
        .as_ref()
        .map_or(requested, |model| clamp_thinking_level(model, requested));
    if effective == agent.thinking_level {
        return Ok(false);
    }
    main.configure(
        AgentChange {
            thinking_level: FieldChange::Set(effective),
            ..AgentChange::default()
        },
        cx,
    )
    .await
    .map_err(|error| error.to_string())?;
    hosted.events_delivered().await;
    if model.as_ref().is_some_and(|model| model.reasoning) || effective != ModelThinkingLevel::Off {
        let mut settings = SettingsManager::create(&deps.cwd, &deps.agent_dir);
        if let Err(error) = settings.set_default_thinking_level(thinking_level_setting(effective)) {
            eprintln!("eukhe-daemon worker: persisting the default thinking level failed: {error}");
        }
    }
    Ok(true)
}

/// The settings vocabulary of a thinking level.
fn thinking_level_setting(level: ModelThinkingLevel) -> ThinkingLevelSetting {
    match level {
        ModelThinkingLevel::Off => ThinkingLevelSetting::Off,
        ModelThinkingLevel::Minimal => ThinkingLevelSetting::Minimal,
        ModelThinkingLevel::Low => ThinkingLevelSetting::Low,
        ModelThinkingLevel::Medium => ThinkingLevelSetting::Medium,
        ModelThinkingLevel::High => ThinkingLevelSetting::High,
        ModelThinkingLevel::Xhigh => ThinkingLevelSetting::Xhigh,
        ModelThinkingLevel::Max => ThinkingLevelSetting::Max,
    }
}

#[cfg(test)]
mod tests;
