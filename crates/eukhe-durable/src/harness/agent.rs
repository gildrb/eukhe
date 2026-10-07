//! The `pi.agent` document, settings resolution, and agent resolution
//! (`harness/agent.ts`).

use std::collections::HashSet;
use std::sync::Arc;

use eukhe_chord::delta::{Draft, DraftItem};
use eukhe_chord::json::{copy_json, to_json, JsonValue};
use eukhe_types::pi_ai::{IndexMap, ModelThinkingLevel};
use futures::FutureExt;

use super::types::{
    Agent, AgentChange, AgentState, CompactionPolicy, ConversationRetryPolicy, Extension,
    ExtensionsChange, FieldChange, HarnessSettings, HookHandlers, ProgressPolicy, PromptSection,
    QueueMode, RegistrySnapshot, Settings, ToolExecutionMode, ToolRegistration, ToolsChange,
};
use crate::documents::{DocDefinition, RewindableConversationDoc};
use crate::session::{SessionError, SessionResult, Tx};
use crate::types::{ConversationId, ConversationRecord, RewindableFork};

pub const DEFAULT_RETRY_POLICY: ConversationRetryPolicy = ConversationRetryPolicy {
    enabled: true,
    max_retries: 3,
    base_delay_ms: 2000.0,
    max_agent_delay_ms: Some(60000.0),
};

pub const DEFAULT_COMPACTION_POLICY: CompactionPolicy = CompactionPolicy {
    enabled: true,
    reserve_tokens: 16384.0,
    keep_recent_tokens: 20000.0,
    background_tokens: 32768.0,
};

pub const DEFAULT_PROGRESS_POLICY: ProgressPolicy = ProgressPolicy {
    partial_interval_ms: 100.0,
    output_interval_ms: 100.0,
};

/// The reserved section key of the agent's `instructions`.
pub const INSTRUCTIONS_KEY: &str = "instructions";

/// Built-in agent document; rewindable so forks start from the agent at
/// their fork entry.
pub static AGENT_DOC: RewindableConversationDoc<AgentState> =
    match RewindableConversationDoc::define(
        DocDefinition {
            kind: "pi.agent",
            version: 1,
            initial: AgentState::default,
            migrate: None,
            checkpoint_when: Some(|_, _, _| true),
        },
        RewindableFork::AsOf,
    ) {
        Ok(token) => token,
        Err(_) => panic!("pi.agent has a valid version"),
    };

/// Resolve the host settings: every field over its built-in default, object
/// fields merged.
#[must_use]
pub fn resolve_settings(settings: Option<&HarnessSettings>) -> Settings {
    let retry = settings.and_then(|settings| settings.retry);
    let compaction = settings.and_then(|settings| settings.compaction);
    let progress = settings.and_then(|settings| settings.progress);
    Settings {
        extensions: settings.and_then(|settings| settings.extensions.clone()),
        stream: settings
            .and_then(|settings| settings.stream.clone())
            .unwrap_or_default(),
        retry: ConversationRetryPolicy {
            enabled: retry
                .and_then(|retry| retry.enabled)
                .unwrap_or(DEFAULT_RETRY_POLICY.enabled),
            max_retries: retry
                .and_then(|retry| retry.max_retries)
                .unwrap_or(DEFAULT_RETRY_POLICY.max_retries),
            base_delay_ms: retry
                .and_then(|retry| retry.base_delay_ms)
                .unwrap_or(DEFAULT_RETRY_POLICY.base_delay_ms),
            max_agent_delay_ms: retry
                .and_then(|retry| retry.max_agent_delay_ms)
                .or(DEFAULT_RETRY_POLICY.max_agent_delay_ms),
        },
        compaction: CompactionPolicy {
            enabled: compaction
                .and_then(|compaction| compaction.enabled)
                .unwrap_or(DEFAULT_COMPACTION_POLICY.enabled),
            reserve_tokens: compaction
                .and_then(|compaction| compaction.reserve_tokens)
                .unwrap_or(DEFAULT_COMPACTION_POLICY.reserve_tokens),
            keep_recent_tokens: compaction
                .and_then(|compaction| compaction.keep_recent_tokens)
                .unwrap_or(DEFAULT_COMPACTION_POLICY.keep_recent_tokens),
            background_tokens: compaction
                .and_then(|compaction| compaction.background_tokens)
                .unwrap_or(DEFAULT_COMPACTION_POLICY.background_tokens),
        },
        // Field by field, so an unset interval keeps its default.
        progress: ProgressPolicy {
            partial_interval_ms: progress
                .and_then(|progress| progress.partial_interval_ms)
                .unwrap_or(DEFAULT_PROGRESS_POLICY.partial_interval_ms),
            output_interval_ms: progress
                .and_then(|progress| progress.output_interval_ms)
                .unwrap_or(DEFAULT_PROGRESS_POLICY.output_interval_ms),
        },
        tool_execution: settings
            .and_then(|settings| settings.tool_execution)
            .unwrap_or(ToolExecutionMode::Parallel),
        steering_mode: settings
            .and_then(|settings| settings.steering_mode)
            .unwrap_or(QueueMode::OneAtATime),
        follow_up_mode: settings
            .and_then(|settings| settings.follow_up_mode)
            .unwrap_or(QueueMode::OneAtATime),
    }
}

/// Apply one change to `pi.agent`: a given field replaces the stored one,
/// `Clear` clears it, `Keep` changes nothing.
///
/// # Errors
///
/// Document access or draft failures.
pub async fn configure(
    tx: &Tx,
    conversation_id: ConversationId,
    change: &AgentChange,
) -> SessionResult<()> {
    let state = tx.doc(&AGENT_DOC, conversation_id).await?;
    apply_change(&state, change)
}

/// `add_tools` of a tool round: an array gets each name it lacks appended,
/// `{ remove }` loses the names, and unset tools already offer every tool,
/// so nothing is written.
///
/// # Errors
///
/// Document access or draft failures.
pub async fn add_tools(
    tx: &Tx,
    conversation_id: ConversationId,
    added: &[String],
) -> SessionResult<()> {
    let state = tx.doc(&AGENT_DOC, conversation_id).await?;
    let Some(tools) = state.get("tools")?.and_then(DraftItem::into_draft) else {
        return Ok(());
    };
    if tools.is_array() {
        for name in added {
            if !draft_strings(&tools)?.contains(name) {
                tools.push([JsonValue::from(name.as_str())])?;
            }
        }
        return Ok(());
    }
    let Some(remove) = tools.get("remove")?.and_then(DraftItem::into_draft) else {
        return Ok(());
    };
    let remove = draft_strings(&remove)?;
    if remove.iter().any(|name| added.contains(name)) {
        let kept: Vec<JsonValue> = remove
            .iter()
            .filter(|name| !added.contains(name))
            .map(|name| JsonValue::from(name.as_str()))
            .collect();
        let mut replacement = crate::types::JsonObject::new();
        replacement.insert("remove", JsonValue::from(kept));
        state.set("tools", JsonValue::from(replacement))?;
    }
    Ok(())
}

/// The strings of a draft array.
fn draft_strings(draft: &Draft) -> SessionResult<Vec<String>> {
    let value = draft.value()?;
    Ok(value
        .as_array()
        .unwrap_or_default()
        .iter()
        .filter_map(|item| item.as_str().map(str::to_owned))
        .collect())
}

fn set_field(state: &Draft, key: &str, value: FieldChange<JsonValue>) -> SessionResult<()> {
    match value {
        FieldChange::Keep => {}
        FieldChange::Clear => state.delete(key)?,
        FieldChange::Set(value) => state.set(key, value)?,
    }
    Ok(())
}

fn map_change<T>(
    change: &FieldChange<T>,
    encode: impl FnOnce(&T) -> SessionResult<JsonValue>,
) -> SessionResult<FieldChange<JsonValue>> {
    Ok(match change {
        FieldChange::Keep => FieldChange::Keep,
        FieldChange::Clear => FieldChange::Clear,
        FieldChange::Set(value) => FieldChange::Set(encode(value)?),
    })
}

fn names<'a>(items: impl IntoIterator<Item = &'a str>) -> JsonValue {
    items.into_iter().map(JsonValue::from).collect()
}

fn extension_names(extensions: &[Arc<Extension>]) -> JsonValue {
    names(extensions.iter().map(|extension| extension.name.as_str()))
}

fn tool_names(tools: &[Arc<ToolRegistration>]) -> JsonValue {
    names(tools.iter().map(|tool| tool.name.as_str()))
}

fn apply_change(state: &Draft, change: &AgentChange) -> SessionResult<()> {
    set_field(
        state,
        "model",
        map_change(&change.model, |model| Ok(to_json(model)?))?,
    )?;
    set_field(
        state,
        "thinkingLevel",
        map_change(&change.thinking_level, |level| Ok(to_json(level)?))?,
    )?;
    set_field(
        state,
        "extensions",
        map_change(&change.extensions, |extensions| {
            Ok(match extensions {
                ExtensionsChange::Exactly(extensions) => extension_names(extensions),
                ExtensionsChange::Edit { add, remove } => {
                    let mut edit = crate::types::JsonObject::new();
                    if let Some(add) = add {
                        edit.insert("add", extension_names(add));
                    }
                    if let Some(remove) = remove {
                        edit.insert("remove", extension_names(remove));
                    }
                    JsonValue::from(edit)
                }
            })
        })?,
    )?;
    set_field(
        state,
        "tools",
        map_change(&change.tools, |tools| {
            Ok(match tools {
                ToolsChange::Exactly(tools) => tool_names(tools),
                ToolsChange::Remove(tools) => {
                    let mut edit = crate::types::JsonObject::new();
                    edit.insert("remove", tool_names(tools));
                    JsonValue::from(edit)
                }
            })
        })?,
    )?;
    set_field(
        state,
        "instructions",
        map_change(&change.instructions, |text| {
            Ok(JsonValue::from(text.as_str()))
        })?,
    )?;
    set_field(
        state,
        "cwd",
        map_change(&change.cwd, |cwd| Ok(JsonValue::from(cwd.as_str())))?,
    )
}

/// Built-in part of every Harness commit that creates or forks a
/// conversation, for `pi.agent`: a fork keeps its `asOf` copy; a new
/// task-owned conversation copies the stored agent of its owner task's
/// conversation; a new ownerless one starts empty.
///
/// # Errors
///
/// Document access or draft failures.
pub async fn create_agent(tx: &Tx, conversation: &ConversationRecord) -> SessionResult<()> {
    if conversation.parent.is_some() {
        return Ok(());
    }
    let agent = tx.doc(&AGENT_DOC, conversation.id).await?;
    let Some(owner) = conversation.owner else {
        return Ok(());
    };
    let owner = tx.doc(&AGENT_DOC, owner.conversation_id).await?;
    // `Object.assign(agent, copyJson(owner))`: own keys in order, each set.
    let copied = copy_json(&owner.value()?);
    if let Some(fields) = copied.as_object() {
        for (key, value) in fields.iter() {
            agent.set(key, value.clone())?;
        }
    }
    Ok(())
}

/// Handlers of the selected extensions' hooks for a task name, in extension
/// order.
#[must_use]
pub fn agent_hooks(agent: &Agent, task_name: &str) -> Vec<HookHandlers> {
    agent
        .extensions
        .iter()
        .flat_map(|extension| extension.hooks.iter())
        .filter(|hook| hook.task == task_name)
        .map(|hook| Arc::clone(&hook.handlers))
        .collect()
}

/// Resolve an agent from its stored state (absent: every field unset), a
/// registry snapshot, and resolved settings. A wrapper that fails or renames
/// drops its target and is reported; a wrapper without a target does
/// nothing.
#[must_use]
pub fn resolve_agent(
    state: Option<&AgentState>,
    snapshot: &RegistrySnapshot,
    settings: &Settings,
    report: &dyn Fn(SessionError),
) -> Agent {
    let extensions = select_extensions(
        state.and_then(|state| state.extensions.as_ref()),
        snapshot,
        settings,
    );

    let mut composed: IndexMap<String, Arc<ToolRegistration>> = IndexMap::new();
    for tool in extensions
        .iter()
        .flat_map(|extension| extension.tools.iter())
    {
        composed.insert(tool.name.clone(), Arc::clone(tool));
    }
    let mut sections: IndexMap<String, Arc<PromptSection>> = IndexMap::new();
    for section in extensions
        .iter()
        .flat_map(|extension| extension.sections.iter())
    {
        sections.insert(section.key.clone(), Arc::clone(section));
    }
    for wrap in extensions
        .iter()
        .flat_map(|extension| extension.wraps.iter())
    {
        match wrap {
            super::types::Wrap::Tool { tool, wrap } => {
                apply_wrap(
                    &mut composed,
                    tool,
                    |item| wrap(item),
                    |item| &item.name,
                    report,
                );
            }
            super::types::Wrap::Section { section, wrap } => {
                apply_wrap(
                    &mut sections,
                    section,
                    |item| wrap(item),
                    |item| &item.key,
                    report,
                );
            }
        }
    }

    let tools: Vec<Arc<ToolRegistration>> = match state.and_then(|state| state.tools.as_ref()) {
        None => composed.values().cloned().collect(),
        Some(super::types::ToolFilter::Exactly(filter)) => {
            let mut seen = HashSet::new();
            filter
                .iter()
                .filter(|name| seen.insert(name.as_str()))
                .filter_map(|name| composed.get(name).cloned())
                .collect()
        }
        Some(super::types::ToolFilter::Remove { remove }) => {
            let removed: HashSet<&str> = remove.iter().map(String::as_str).collect();
            composed
                .values()
                .filter(|tool| !removed.contains(tool.name.as_str()))
                .cloned()
                .collect()
        }
    };

    let instructions = state.and_then(|state| state.instructions.clone());
    let mut agent_sections: Vec<Arc<PromptSection>> = sections.into_values().collect();
    if let Some(instructions) = &instructions {
        let text = instructions.clone();
        agent_sections.push(Arc::new(PromptSection {
            key: INSTRUCTIONS_KEY.to_owned(),
            render: Arc::new(move |_, _| futures::future::ready(Ok(Some(text.clone()))).boxed()),
            tag: None,
        }));
    }

    Agent {
        model: state.and_then(|state| state.model.clone()),
        thinking_level: state
            .and_then(|state| state.thinking_level)
            .unwrap_or(ModelThinkingLevel::Off),
        extensions,
        tools,
        sections: agent_sections,
        instructions,
        cwd: state.and_then(|state| state.cwd.clone()),
    }
}

/// Selected installed extensions: the stored array, or the default
/// selection edited by `{ add, remove }`.
fn select_extensions(
    stored: Option<&super::types::ExtensionSelection>,
    snapshot: &RegistrySnapshot,
    settings: &Settings,
) -> Vec<Arc<Extension>> {
    let selected: Vec<&str> = match stored {
        Some(super::types::ExtensionSelection::Exactly(names)) => {
            names.iter().map(String::as_str).collect()
        }
        edit => {
            let base: Vec<&str> = match &settings.extensions {
                Some(extensions) => extensions
                    .iter()
                    .map(|extension| extension.name.as_str())
                    .collect(),
                None => snapshot
                    .installed()
                    .iter()
                    .map(|extension| extension.name.as_str())
                    .collect(),
            };
            let (add, remove) = match edit {
                Some(super::types::ExtensionSelection::Edit { add, remove }) => (
                    add.as_deref().unwrap_or_default(),
                    remove.as_deref().unwrap_or_default(),
                ),
                Some(super::types::ExtensionSelection::Exactly(_)) | None => (&[][..], &[][..]),
            };
            let removed: HashSet<&str> = remove.iter().map(String::as_str).collect();
            base.into_iter()
                .chain(add.iter().map(String::as_str))
                .filter(|name| !removed.contains(name))
                .collect()
        }
    };
    let mut seen = HashSet::new();
    selected
        .into_iter()
        .filter(|name| seen.insert(*name))
        .filter_map(|name| snapshot.extension(name).cloned())
        .collect()
}

fn apply_wrap<T>(
    items: &mut IndexMap<String, Arc<T>>,
    target: &str,
    wrap: impl FnOnce(&Arc<T>) -> SessionResult<Arc<T>>,
    name_of: impl Fn(&T) -> &String,
    report: &dyn Fn(SessionError),
) {
    let Some(item) = items.get(target) else {
        return;
    };
    let wrapped = wrap(item).and_then(|wrapped| {
        let name = name_of(&wrapped);
        if name == target {
            Ok(wrapped)
        } else {
            Err(SessionError::error(format!(
                "Wrapper renamed {target} to {name}"
            )))
        }
    });
    match wrapped {
        Ok(wrapped) => {
            if let Some(slot) = items.get_mut(target) {
                *slot = wrapped;
            }
        }
        Err(error) => {
            // `Map.delete`: later entries keep their order.
            items.shift_remove(target);
            report(error);
        }
    }
}
