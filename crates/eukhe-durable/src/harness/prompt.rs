//! System prompt sections and positional `pi.system` entries. Port of
//! `harness/prompt.ts`.

use std::collections::HashSet;

use eukhe_chord::context::Context;
use eukhe_pi_ai::utils::transcript::{declarations_equal, get_current_tools, to_tool_declaration};
use eukhe_types::pi_ai::{IndexMap, Message, SystemContent, SystemMessage, Tool, ToolReference};

use crate::entries::SYSTEM_ENTRY;
use crate::harness::types::{ContextView, PromptInput, PromptSection};
use crate::session::{SessionError, SessionResult};
use crate::types::{ContextEdit, ContextEditAction, NoData, TypedEntryDraft};

/// Sections in effect after replaying system messages in order: set in
/// place, `None` deletes, re-adding appends.
#[must_use]
pub fn replay_sections(messages: &[Message]) -> IndexMap<String, String> {
    let mut shown = IndexMap::new();
    for message in messages {
        let Message::System(message) = message else {
            continue;
        };
        let Some(sections) = &message.sections else {
            continue;
        };
        for (key, value) in sections {
            match value {
                None => {
                    shown.shift_remove(key);
                }
                Some(value) => {
                    // JS `Map.set` keeps an existing key in place.
                    shown.insert(key.clone(), value.clone());
                }
            }
        }
    }
    shown
}

/// Render the agent's sections in order. `None` omits a section; tagged
/// text is wrapped as `<key>\n...\n</key>`. A section that fails keeps its
/// shown text, if any, and is reported; errors after `cx` is aborted
/// propagate.
///
/// # Errors
/// A section's error once `cx` is aborted.
pub async fn render_sections(
    sections: &[std::sync::Arc<PromptSection>],
    input: &PromptInput,
    shown: &IndexMap<String, String>,
    report: &(dyn Fn(SessionError) -> SessionResult<()> + Send + Sync),
    cx: &Context,
) -> SessionResult<IndexMap<String, String>> {
    let mut desired = IndexMap::new();
    for section in sections {
        let text = match (section.render)(input, cx).await {
            Ok(text) => text,
            Err(error) => {
                if cx.aborted() {
                    return Err(error);
                }
                report(error)?;
                if let Some(kept) = shown.get(&section.key) {
                    desired.insert(section.key.clone(), kept.clone());
                }
                continue;
            }
        };
        let Some(text) = text else {
            continue;
        };
        let value = if section.tag == Some(false) {
            text
        } else {
            let key = &section.key;
            format!("<{key}>\n{text}\n</{key}>")
        };
        desired.insert(section.key.clone(), value);
    }
    Ok(desired)
}

/// A planned `pi.system` entry.
pub type SystemDraft = TypedEntryDraft<NoData>;

struct ToolChanges {
    tools_removed: Vec<ToolReference>,
    tools_added: Vec<Tool>,
}

/// Plan the `pi.system` entries that make the replayed sections and tools
/// of `view` equal `desired` and `tools` in values and order.
///
/// - A head marker with no later `pi.system` entry in context: one complete
///   baseline that omits every retained earlier `pi.system` entry, written
///   even when it restates the replayed values.
/// - Otherwise, when a minimal section patch would leave a different order:
///   remove every shown section, then re-add every desired section in order.
/// - Otherwise the minimal patch of changed values and `None` removals, or
///   nothing.
///
/// Tool changes ride on the last planned entry, or on one entry of their own.
#[must_use]
pub fn plan_system_entries(
    view: &ContextView,
    desired: &IndexMap<String, String>,
    tools: &[Tool],
    timestamp: u64,
) -> Vec<SystemDraft> {
    if let Some(head) = &view.head {
        let later_system = view
            .entries
            .iter()
            .any(|entry| SYSTEM_ENTRY.is(Some(entry)) && entry.id > head.id);
        if !later_system {
            let edits: Vec<ContextEdit> = view
                .entries
                .iter()
                .filter(|entry| SYSTEM_ENTRY.is(Some(entry)))
                .map(|entry| ContextEdit {
                    target: entry.id,
                    action: ContextEditAction::Omit,
                })
                .collect();
            let sections = desired
                .iter()
                .map(|(key, value)| (key.clone(), Some(value.clone())))
                .collect();
            let mut baseline = system_entry(
                Some(sections),
                Some(ToolChanges {
                    tools_removed: Vec::new(),
                    tools_added: tools.iter().map(to_tool_declaration).collect(),
                }),
                timestamp,
            );
            if !edits.is_empty() {
                baseline.edits = Some(edits);
            }
            return vec![baseline];
        }
    }
    let sections = plan_sections(&replay_sections(&view.messages), desired);
    let changes = plan_tools(&get_current_tools(&view.messages), tools);
    if changes.tools_removed.is_empty() && changes.tools_added.is_empty() {
        return sections
            .into_iter()
            .map(|patch| system_entry(Some(patch), None, timestamp))
            .collect();
    }
    if sections.is_empty() {
        return vec![system_entry(None, Some(changes), timestamp)];
    }
    let last = sections.len() - 1;
    let mut changes = Some(changes);
    sections
        .into_iter()
        .enumerate()
        .map(|(index, patch)| {
            let tools = if index == last { changes.take() } else { None };
            system_entry(Some(patch), tools, timestamp)
        })
        .collect()
}

/// Tool changes from `offered` to `desired`. A changed declaration is
/// removed and re-added. Replay keeps retained tools in place and appends
/// additions; when that would not yield the desired order, every offered
/// tool is removed and every desired tool re-added in order.
fn plan_tools(offered: &[Tool], desired: &[Tool]) -> ToolChanges {
    // JS `new Map(entries)`: a later duplicate name wins.
    let mut wanted: IndexMap<&str, &Tool> = IndexMap::new();
    for tool in desired {
        wanted.insert(tool.name.as_str(), tool);
    }
    let kept: Vec<&Tool> = offered
        .iter()
        .filter(|tool| {
            wanted
                .get(tool.name.as_str())
                .is_some_and(|next| declarations_equal(tool, next))
        })
        .collect();
    let kept_names: HashSet<&str> = kept.iter().map(|tool| tool.name.as_str()).collect();
    let added: Vec<&Tool> = desired
        .iter()
        .filter(|tool| !kept_names.contains(tool.name.as_str()))
        .collect();
    let reordered = kept
        .iter()
        .chain(added.iter())
        .enumerate()
        .any(|(index, tool)| desired.get(index).is_none_or(|want| tool.name != want.name));
    if reordered {
        return ToolChanges {
            tools_removed: offered.iter().map(reference).collect(),
            tools_added: desired.iter().map(to_tool_declaration).collect(),
        };
    }
    ToolChanges {
        tools_removed: offered
            .iter()
            .filter(|tool| !kept_names.contains(tool.name.as_str()))
            .map(reference)
            .collect(),
        tools_added: added.into_iter().map(to_tool_declaration).collect(),
    }
}

fn reference(tool: &Tool) -> ToolReference {
    ToolReference {
        name: tool.name.clone(),
    }
}

type SectionPatch = IndexMap<String, Option<String>>;

/// Section patches: none, the minimal patch, or a remove-all/re-add-all
/// pair when the order would differ.
fn plan_sections(
    shown: &IndexMap<String, String>,
    desired: &IndexMap<String, String>,
) -> Vec<SectionPatch> {
    let patched_order = shown
        .keys()
        .filter(|key| desired.contains_key(*key))
        .chain(desired.keys().filter(|key| !shown.contains_key(*key)));
    let differs = patched_order
        .zip(desired.keys())
        .any(|(patched, wanted)| patched != wanted);
    if differs {
        return vec![
            shown.keys().map(|key| (key.clone(), None)).collect(),
            desired
                .iter()
                .map(|(key, value)| (key.clone(), Some(value.clone())))
                .collect(),
        ];
    }
    let mut patch = SectionPatch::new();
    for (key, value) in shown {
        let next = desired.get(key);
        if next != Some(value) {
            patch.insert(key.clone(), next.cloned());
        }
    }
    for (key, value) in desired {
        if !shown.contains_key(key) {
            patch.insert(key.clone(), Some(value.clone()));
        }
    }
    if patch.is_empty() {
        Vec::new()
    } else {
        vec![patch]
    }
}

fn system_entry(
    sections: Option<SectionPatch>,
    tools: Option<ToolChanges>,
    timestamp: u64,
) -> SystemDraft {
    let (tools_removed, tools_added) = match tools {
        None => (None, None),
        Some(tools) => (
            Some(tools.tools_removed).filter(|removed| !removed.is_empty()),
            Some(tools.tools_added).filter(|added| !added.is_empty()),
        ),
    };
    let message = SystemMessage {
        content: SystemContent::Text(String::new()),
        sections,
        tools_added,
        tools_removed,
        timestamp,
    };
    TypedEntryDraft {
        model: Some(vec![Message::System(message)]),
        data: NoData,
        head: None,
        edits: None,
    }
}

#[cfg(test)]
mod tests;
