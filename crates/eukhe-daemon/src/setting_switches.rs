//! The model/setting switches (protocol breadth wave b3): the worker arms
//! for the daemon commands that flip live session settings — `cycle_model`,
//! `set_scoped_models`, `cycle_thinking_level`, `set_service_tier`,
//! `set_transport`, `set_steering_mode`, `set_follow_up_mode`,
//! `set_auto_compaction`, `set_auto_retry`, `abort_retry` (TS daemon-mode
//! cases) — and the cvar commands (`cvar`, `cvar_save`, docs/harness.md
//! S4). The wire contracts are TS-verbatim. Model and thinking switches
//! configure the main conversation (`model_switch`); every other switch is
//! a set of a Local cvar in this session's own layer (the same path as
//! `cvar`, committed with the main conversation), never a settings.json
//! write: another session over the same agent dir keeps its values. The
//! Harness and the connection state read the session's settings
//! (`EukheSettings`).

use eukhe_ai::auth::AuthOperationOptions;
use eukhe_ai::models::get_supported_thinking_levels;
use eukhe_chord::context::BACKGROUND_CONTEXT;
use eukhe_core::durable::cvar_agent::{
    run_cvar_line, save_agent_cfg, CvarLineError, CvarLineScope,
};
use eukhe_core::settings::cvar::{table, CvarError, Decl, Set};
use eukhe_durable::harness::types::ConversationAbortOptions;
use eukhe_types::ai::{ServiceTier, Transport};
use eukhe_types::cvar::{Command, ExpandError};
use eukhe_types::daemon::{CvarFailureData, CvarFailureKind, SessionEvent};
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

/// TS `_getEffectiveServiceTier` (#2144's `clampServiceTier`): a tier the
/// model does not support degrades to `default`. An unset (`null`)
/// preference passes through; `None` on the wire reads as `auto` (see
/// [`ServiceTier::as_str`]).
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
                "serviceTier": service_tier.as_str(),
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
            self.emit_worker_event(SessionEvent::ServiceTierChanged {
                service_tier: clamped.unwrap_or(ServiceTier::Auto),
            });
        }
    }

    /// The replacement sessions (`new_session` / `switch_session` /
    /// `import_jsonl` / `fork`) re-seed the service tier like a create: the
    /// session's default preference, then the active tier re-clamps against
    /// the restored model (the clamp's event contract).
    pub(crate) fn reseed_service_tier_for_replacement(&self) {
        let Some(hosted) = self.session.get() else {
            return;
        };
        let default_tier = hosted.deps().settings.manager().get_default_service_tier();
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
        let (preference_changed, effective_changed, supported, effective) = {
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
            (preference_changed, effective_changed, supported, effective)
        };
        if preference_changed && supported {
            // TS persists the default only when the model supports the
            // tier (#2144: `supportsServiceTier(this.model, serviceTier)`);
            // here the default is this session's own set.
            let saved = self
                .set_session_cvar(COMMAND, &table::DEFAULT_SERVICE_TIER, tier.as_str())
                .await;
            if let Some(error) = saved.error {
                // The session already switched; the default is best-effort
                // like TS.
                eprintln!("eukhe-daemon worker: setting the default service tier failed: {error}");
            }
        }
        if effective_changed {
            self.emit_worker_event(SessionEvent::ServiceTierChanged {
                service_tier: effective,
            });
        }
        response_success(None, COMMAND, None)
    }

    /// `set_transport { transport }` (TS `settingsManager.setTransport` +
    /// `agent.transport`): this session's `transport`. The live stream
    /// resolves transport per request from the session's settings, so the
    /// set is the whole switch.
    #[tracing::instrument(skip(self, payload))]
    pub(crate) async fn handle_set_transport(&self, payload: &Value) -> DaemonResponse {
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
        let value = match transport {
            Transport::Auto => "auto",
            Transport::Sse => "sse",
            Transport::Websocket | Transport::WebsocketCached => "web-socket",
        };
        self.set_session_cvar(COMMAND, &table::TRANSPORT, value)
            .await
    }

    /// `set_steering_mode` / `set_follow_up_mode { mode }` (TS
    /// `session.setSteeringMode` / `setFollowUpMode`): this session's queue
    /// delivery mode; its inbox placement and connection state read it
    /// back.
    #[tracing::instrument(skip(self, payload))]
    pub(crate) async fn handle_set_queue_mode(
        &self,
        command: &str,
        payload: &Value,
    ) -> DaemonResponse {
        if let Err(response) = self.require_created(command) {
            return response;
        }
        let Some(mode) = payload
            .get("mode")
            .and_then(Value::as_str)
            .filter(|mode| QUEUE_MODES.contains(mode))
        else {
            return response_failure(
                None,
                command,
                &format!("{command} requires mode \"all\" or \"one-at-a-time\""),
                None,
            );
        };
        let decl = if command == "set_steering_mode" {
            &table::STEERING_MODE
        } else {
            &table::FOLLOW_UP_MODE
        };
        self.set_session_cvar(command, decl, mode).await
    }

    /// `set_auto_retry { enabled }` (TS `session.setAutoRetryEnabled`):
    /// this session's `retry.enabled`, which the provider retry policy
    /// reads on every request.
    #[tracing::instrument(skip(self, payload))]
    pub(crate) async fn handle_set_auto_retry(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_auto_retry";
        if let Err(response) = self.require_created(COMMAND) {
            return response;
        }
        let Some(enabled) = payload.get("enabled").and_then(Value::as_bool) else {
            return response_failure(None, COMMAND, "set_auto_retry requires enabled", None);
        };
        self.set_session_cvar(COMMAND, &table::RETRY_ENABLED, &enabled.to_string())
            .await
    }

    /// `set_auto_compaction { enabled }` (TS
    /// `session.setAutoCompactionEnabled`): this session's
    /// `compaction.enabled` — the Harness's compaction policy and the
    /// connection state both read it, and the session's agent state keeps
    /// it across a restart. A failed commit fails the command and flips
    /// nothing.
    #[tracing::instrument(skip(self, payload))]
    pub(crate) async fn handle_set_auto_compaction(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "set_auto_compaction";
        if let Err(response) = self.require_created(COMMAND) {
            return response;
        }
        let enabled = payload
            .get("enabled")
            .and_then(Value::as_bool)
            .unwrap_or(false);
        self.set_session_cvar(COMMAND, &table::COMPACTION_ENABLED, &enabled.to_string())
            .await
    }

    /// `cvar { line, global }`: run a cvar command list for this session
    /// (its own sets and aliases), or with `global` write its `set` /
    /// `toggle` commands to the global config.cfg. Answers the replicated
    /// values; a rejected command applies nothing and fails with its typed
    /// `data` ([`CvarFailureData`]).
    #[tracing::instrument(skip(self, payload))]
    pub(crate) async fn handle_cvar(&self, payload: &Value) -> DaemonResponse {
        const COMMAND: &str = "cvar";
        let Some(line) = payload.get("line").and_then(Value::as_str) else {
            return response_failure(None, COMMAND, "cvar requires a line", None);
        };
        let scope = if payload.get("global").and_then(Value::as_bool) == Some(true) {
            CvarLineScope::Global
        } else {
            CvarLineScope::Session
        };
        match self.cvar_line(COMMAND, line, scope).await {
            Ok(values) => response_success(
                None,
                COMMAND,
                Some(json!({ "values": values, "errors": [] })),
            ),
            Err(response) => response,
        }
    }

    /// `cvar_save`: write this session's own sets of persisting cvars to
    /// its `agents/<agent>.cfg`.
    #[tracing::instrument(skip(self))]
    pub(crate) async fn handle_cvar_save(&self) -> DaemonResponse {
        const COMMAND: &str = "cvar_save";
        let hosted = match self.hosted(COMMAND) {
            Ok(hosted) => hosted,
            Err(response) => return response,
        };
        let saved = match hosted.session() {
            Ok(session) => save_agent_cfg(&session).await,
            Err(error) => return response_failure(None, COMMAND, &error.to_string(), None),
        };
        match saved {
            Ok(()) => response_success(None, COMMAND, None),
            Err(error) => cvar_failure(COMMAND, &error),
        }
    }

    /// Set `decl` to `value` in this session's own layer (a switch
    /// command's `set`).
    #[tracing::instrument(skip(self, decl))]
    async fn set_session_cvar(&self, command: &str, decl: &Decl, value: &str) -> DaemonResponse {
        let line = Command::Set {
            id: decl.id.to_string(),
            value: value.to_string(),
        }
        .to_string();
        match self.cvar_line(command, &line, CvarLineScope::Session).await {
            Ok(_) => response_success(None, command, None),
            Err(response) => response,
        }
    }

    /// Run `line` for this session; the failure is `command`'s response.
    #[tracing::instrument(skip(self))]
    #[allow(clippy::result_large_err)] // the error is the wire response itself
    async fn cvar_line(
        &self,
        command: &str,
        line: &str,
        scope: CvarLineScope,
    ) -> Result<Vec<Set>, DaemonResponse> {
        let hosted = self.hosted(command)?;
        let session = hosted
            .session()
            .map_err(|error| response_failure(None, command, &error.to_string(), None))?;
        run_cvar_line(&session, line, scope, &BACKGROUND_CONTEXT)
            .await
            .map_err(|error| cvar_failure(command, &error))
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
}

/// The failure response of `command` for a cvar line that did not apply:
/// the message is the error's text; a rejected command also carries its
/// typed `data` (`{ kind, id?, message }`: the wire line drops `error`
/// when `data` is present).
fn cvar_failure(command: &str, error: &CvarLineError) -> DaemonResponse {
    let message = error.to_string();
    let mut response = response_failure(None, command, &message, None);
    let data = match error {
        CvarLineError::Cvar(error) => {
            let (kind, id) = match error {
                CvarError::Parse(_) => (CvarFailureKind::Parse, None),
                CvarError::Expand(ExpandError::Cycle { alias }) => {
                    (CvarFailureKind::Cycle, Some(alias))
                }
                CvarError::Expand(ExpandError::Unknown { alias }) => {
                    (CvarFailureKind::UnknownAlias, Some(alias))
                }
                CvarError::Undeclared { id } => (CvarFailureKind::Undeclared, Some(id)),
                CvarError::BadValue { id, .. } => (CvarFailureKind::BadValue, Some(id)),
                CvarError::Global { id } => (CvarFailureKind::Global, Some(id)),
                CvarError::NotBool { id } => (CvarFailureKind::NotBool, Some(id)),
                CvarError::Action { id } => (CvarFailureKind::Action, Some(id)),
            };
            Some(CvarFailureData {
                kind,
                id: id.cloned(),
                message,
            })
        }
        CvarLineError::NotGlobal { .. } | CvarLineError::Unnamed | CvarLineError::Io(_) => None,
    };
    response.data = data.and_then(|data| serde_json::to_value(data).ok());
    response
}

#[cfg(test)]
mod tests;
