//! The RPC command surface, part three: the model, thinking-level, and
//! queue-mode switches (TS `session.setModel`/`cycleModel`/
//! `refreshAvailableModels`/`setThinkingLevel`/`cycleThinkingLevel`/
//! `setSteeringMode`/`setFollowUpMode`) over the main conversation's
//! `pi.agent` (`Conversation::configure`) and the settings defaults.

use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_core::durable::EukheSession;
use eukhe_core::settings::{QueueModeSetting, ThinkingLevelSetting};
use eukhe_durable::harness::types::{AgentChange, FieldChange, ModelRef};
use eukhe_pi_ai::auth::AuthOperationOptions;
use eukhe_pi_ai::models::{clamp_thinking_level, get_supported_thinking_levels};
use eukhe_types::pi_ai::{Model, ModelThinkingLevel};
use serde_json::{json, Value};

use super::commands::{settings_for, RpcState};
use super::protocol::ResponseData;
use super::reads::{agent_model, main_agent, rpc_context};

/// The valid thinking-level wire names (TS `ThinkingLevel`).
const THINKING_LEVELS: &[&str] = &["off", "minimal", "low", "medium", "high", "xhigh", "max"];

/// The models whose providers have credentials (TS `getAvailable`).
async fn available_models(session: &EukheSession) -> Result<Vec<Model>, String> {
    session
        .deps()
        .models
        .get_available(None, AuthOperationOptions::default())
        .await
        .map_err(|error| error.to_string())
}

/// `set_model` (TS `session.setModel`): resolve through the available
/// catalog, switch the main conversation's model (clamping the thinking
/// level), and persist the settings default.
pub(crate) async fn set_model(
    state: &Arc<RpcState>,
    payload: &Value,
) -> Result<ResponseData, String> {
    let _ops = state.model_ops.lock().await;
    let provider = payload
        .get("provider")
        .and_then(Value::as_str)
        .ok_or_else(|| "set_model requires a provider".to_string())?;
    let model_id = payload
        .get("modelId")
        .and_then(Value::as_str)
        .ok_or_else(|| "set_model requires a modelId".to_string())?;
    let handle = state.session.handle().await;
    let session = &handle.session;
    let model = available_models(session)
        .await?
        .into_iter()
        .find(|candidate| candidate.provider == provider && candidate.id == model_id)
        .ok_or_else(|| format!("Model not found: {provider}/{model_id}"))?;
    apply_model_selection(session, &model, &rpc_context()).await?;
    Ok(ResponseData::Present(
        serde_json::to_value(&model).map_err(|error| error.to_string())?,
    ))
}

/// Apply one model selection (the shared `set_model`/`cycle_model`
/// tail): the model and the clamped thinking level in one `configure`
/// commit (TS `_getThinkingLevelForModelSwitch`: keep the level when the
/// new model supports it, else clamp), then the settings default.
async fn apply_model_selection(
    session: &EukheSession,
    model: &Model,
    cx: &Context,
) -> Result<(), String> {
    let agent = main_agent(session, cx).await?;
    let level = clamp_thinking_level(model, agent.thinking_level);
    session
        .main()
        .configure(
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
    settings_for(session)
        .set_default_model_and_provider(&model.provider, &model.id)
        .map_err(|error| error.to_string())
}

/// `cycle_model` (TS `session.cycleModel`, forward only on this wire):
/// cycle within the available catalog; fewer than two candidates answer
/// `null` like TS.
pub(crate) async fn cycle_model(state: &Arc<RpcState>) -> Result<ResponseData, String> {
    let _ops = state.model_ops.lock().await;
    let handle = state.session.handle().await;
    let session = &handle.session;
    let cx = rpc_context();
    let available = available_models(session).await?;
    if available.len() <= 1 {
        return Ok(ResponseData::Present(Value::Null));
    }
    let current = main_agent(session, &cx).await?.model;
    // When the current model is absent from the catalog (an auth filter
    // removed it), the cycle lands on the FIRST available model (TS
    // `cycleModel` steps from the current when present, and from the
    // head otherwise).
    let index = current
        .and_then(|current| {
            available.iter().position(|model| {
                model.provider == current.provider && model.id == current.model_id
            })
        })
        .map_or(0, |index| (index + 1) % available.len());
    let next = available[index].clone();
    apply_model_selection(session, &next, &cx).await?;
    let level = main_agent(session, &cx).await?.thinking_level;
    Ok(ResponseData::Present(json!({
        "model": next,
        "thinkingLevel": level.as_str(),
        "isScoped": false,
    })))
}

/// `get_available_models` (TS `refreshAvailableModels`): the available
/// catalog (the session's model collection refreshes its catalogs in the
/// background from open).
pub(crate) async fn get_available_models(state: &Arc<RpcState>) -> Result<ResponseData, String> {
    let session = state.session.session().await;
    let models = available_models(&session).await?;
    Ok(ResponseData::Present(json!({ "models": models })))
}

/// `set_thinking_level` (TS `session.setThinkingLevel`): clamp to what
/// the model supports, switch on a change, and persist the default.
pub(crate) async fn set_thinking_level(
    state: &Arc<RpcState>,
    payload: &Value,
) -> Result<ResponseData, String> {
    let _ops = state.model_ops.lock().await;
    let level = payload
        .get("level")
        .and_then(Value::as_str)
        .ok_or_else(|| "Invalid thinking level: expected a string".to_string())?;
    let Some(parsed) = ModelThinkingLevel::parse(level) else {
        return Err(format!(
            "Invalid thinking level \"{level}\". Valid values: {}",
            THINKING_LEVELS.join(", ")
        ));
    };
    apply_thinking_level(state, parsed).await?;
    Ok(ResponseData::Absent)
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

/// Apply one thinking level (the shared `set`/`cycle` tail): an effective
/// change configures the main conversation, persists the settings
/// default (when the model can think or the level is a real reasoning
/// request, TS parity), and publishes `thinking_level_changed`.
async fn apply_thinking_level(
    state: &Arc<RpcState>,
    level: ModelThinkingLevel,
) -> Result<(), String> {
    let handle = state.session.handle().await;
    let session = &handle.session;
    let cx = rpc_context();
    let agent = main_agent(session, &cx).await?;
    let model = agent_model(session, &agent);
    let clamped = model
        .as_ref()
        .map_or(level, |model| clamp_thinking_level(model, level));
    if clamped == agent.thinking_level {
        return Ok(());
    }
    session
        .main()
        .configure(
            AgentChange {
                thinking_level: FieldChange::Set(clamped),
                ..AgentChange::default()
            },
            &cx,
        )
        .await
        .map_err(|error| error.to_string())?;
    if model.as_ref().is_some_and(|model| model.reasoning) || clamped != ModelThinkingLevel::Off {
        settings_for(session)
            .set_default_thinking_level(thinking_level_setting(clamped))
            .map_err(|error| error.to_string())?;
    }
    state.session.outputs().write(json!({
        "type": "thinking_level_changed",
        "level": clamped.as_str(),
    }));
    Ok(())
}

/// `cycle_thinking_level` (TS `session.cycleThinkingLevel`): cycle the
/// supported levels; a model without reasoning answers `null`.
pub(crate) async fn cycle_thinking_level(state: &Arc<RpcState>) -> Result<ResponseData, String> {
    let _ops = state.model_ops.lock().await;
    let (current, levels) = {
        let session = state.session.session().await;
        let agent = main_agent(&session, &rpc_context()).await?;
        let Some(model) = agent_model(&session, &agent).filter(|model| model.reasoning) else {
            return Ok(ResponseData::Present(Value::Null));
        };
        (agent.thinking_level, get_supported_thinking_levels(&model))
    };
    if levels.is_empty() {
        return Ok(ResponseData::Present(Value::Null));
    }
    let next = match levels.iter().position(|level| *level == current) {
        Some(index) => levels[(index + 1) % levels.len()],
        None => levels[0],
    };
    apply_thinking_level(state, next).await?;
    Ok(ResponseData::Present(json!({ "level": next.as_str() })))
}

/// `set_steering_mode` / `set_follow_up_mode` (TS
/// `session.setSteeringMode`/`setFollowUpMode`): the settings default the
/// session's inbox placement reads.
pub(crate) async fn set_queue_mode(
    state: &Arc<RpcState>,
    payload: &Value,
    name: &str,
) -> Result<ResponseData, String> {
    let mode = payload
        .get("mode")
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{name} requires a mode"))?;
    let setting = match mode {
        "all" => QueueModeSetting::All,
        "one-at-a-time" => QueueModeSetting::OneAtATime,
        other => {
            return Err(format!(
                "Invalid queue mode \"{other}\". Valid values: all, one-at-a-time"
            ));
        }
    };
    let mut settings = settings_for(&*state.session.session().await);
    if name == "set_steering_mode" {
        settings.set_steering_mode(setting)
    } else {
        settings.set_follow_up_mode(setting)
    }
    .map_err(|error| error.to_string())?;
    Ok(ResponseData::Absent)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn thinking_level_settings_share_the_wire_names() {
        for name in THINKING_LEVELS {
            let level = ModelThinkingLevel::parse(name).unwrap();
            assert_eq!(
                serde_json::to_value(thinking_level_setting(level)).unwrap(),
                json!(name)
            );
        }
    }
}
