//! Transcript normalization and system-message replay: the leading system
//! message carries the prompt and tools; later system messages change them.

use eukhe_types::pi_ai::{
    Context, IndexMap, JsonValue, Message, SystemContent, SystemMessage, Tool, ToolReference,
    ToolSchema, TranscriptContext,
};

use super::text::{get_system_message_text, MessageContent, DEFAULT_CONTENT_SEPARATOR};

/// A transcript entry. The replay helpers only read entries that are system
/// messages, so agent transcripts with custom message kinds can implement
/// this and be passed without filtering (TS `TranscriptMessages`).
pub trait TranscriptMessage {
    /// The entry as a system message, when it is one.
    fn as_system_message(&self) -> Option<&SystemMessage>;
}

impl TranscriptMessage for Message {
    fn as_system_message(&self) -> Option<&SystemMessage> {
        self.as_system()
    }
}

/// Build the leading system message for a prompt and tool set. `None` when
/// both are empty, so an empty transcript stays empty.
#[must_use]
pub fn create_initial_system_message(
    system_prompt: Option<String>,
    tools: Option<Vec<Tool>>,
) -> Option<SystemMessage> {
    let has_system_prompt = system_prompt
        .as_ref()
        .is_some_and(|prompt| !prompt.is_empty());
    let has_tools = tools.as_ref().is_some_and(|tools| !tools.is_empty());
    if !has_system_prompt && !has_tools {
        return None;
    }
    Some(SystemMessage {
        content: SystemContent::Text(system_prompt.unwrap_or_default()),
        sections: None,
        tools_added: if has_tools { tools } else { None },
        tools_removed: None,
        timestamp: 0,
    })
}

/// Fold `Context::system_prompt` and `Context::tools` into a leading system
/// message. The only producer of a [`TranscriptContext`]; every
/// provider-facing function expects the result.
#[must_use]
pub fn normalize_context(context: Context) -> TranscriptContext {
    let Context {
        system_prompt,
        messages,
        tools,
    } = context;
    let messages = match create_initial_system_message(system_prompt, tools) {
        Some(initial) => {
            let mut normalized = Vec::with_capacity(messages.len() + 1);
            normalized.push(Message::System(initial));
            normalized.extend(messages);
            normalized
        }
        None => messages,
    };
    TranscriptContext::from_normalized_messages(messages)
}

/// The leading system message, if the transcript starts with one.
#[must_use]
pub fn get_initial_system_message<M: TranscriptMessage>(messages: &[M]) -> Option<&SystemMessage> {
    messages
        .first()
        .and_then(TranscriptMessage::as_system_message)
}

/// Drop the leading system message for APIs that carry the prompt outside the message list.
#[must_use]
pub fn without_initial_system_message(messages: &[Message]) -> &[Message] {
    if get_initial_system_message(messages).is_some() {
        &messages[1..]
    } else {
        messages
    }
}

/// Resolve the tools available after applying every transcript delta in order.
#[must_use]
pub fn get_current_tools<M: TranscriptMessage>(messages: &[M]) -> Vec<Tool> {
    let mut tools: IndexMap<&str, &Tool> = IndexMap::new();
    for message in messages {
        let Some(message) = message.as_system_message() else {
            continue;
        };
        for tool in message.tools_removed.iter().flatten() {
            tools.shift_remove(tool.name.as_str());
        }
        for tool in message.tools_added.iter().flatten() {
            tools.insert(&tool.name, tool);
        }
    }
    tools.into_values().cloned().collect()
}

/// Replay every system message into one leading system message holding the
/// current prompt and tools. Later `content` is appended to the base prompt,
/// `sections` are patched by name, and tools are resolved with
/// [`get_current_tools`].
#[must_use]
pub fn get_current_system_message<M: TranscriptMessage>(messages: &[M]) -> Option<SystemMessage> {
    let mut content: Vec<String> = Vec::new();
    let mut sections: IndexMap<String, String> = IndexMap::new();
    let mut timestamp: Option<u64> = None;
    for message in messages {
        let Some(message) = message.as_system_message() else {
            continue;
        };
        timestamp.get_or_insert(message.timestamp);
        let text = message.content.content_text(DEFAULT_CONTENT_SEPARATOR);
        if !text.is_empty() {
            content.push(text);
        }
        for (name, value) in message.sections.iter().flatten() {
            match value {
                None => {
                    sections.shift_remove(name);
                }
                Some(value) => {
                    sections.insert(name.clone(), value.clone());
                }
            }
        }
    }
    let tools = get_current_tools(messages);
    if timestamp.is_none() && tools.is_empty() {
        return None;
    }
    Some(SystemMessage {
        content: SystemContent::Text(content.join("\n\n")),
        sections: (!sections.is_empty()).then(|| {
            sections
                .into_iter()
                .map(|(name, value)| (name, Some(value)))
                .collect()
        }),
        tools_added: (!tools.is_empty()).then_some(tools),
        tools_removed: None,
        timestamp: timestamp.unwrap_or(0),
    })
}

/// Render the current system prompt text after replaying every system message.
#[must_use]
pub fn get_current_system_prompt<M: TranscriptMessage>(messages: &[M]) -> String {
    get_current_system_message(messages)
        .map_or_else(String::new, |message| get_system_message_text(&message))
}

/// Rebuild the transcript for APIs without mid-conversation system messages:
/// the replayed system message leads, and every later system message is dropped.
#[must_use]
pub fn collapse_system_messages(context: TranscriptContext) -> TranscriptContext {
    let head = get_current_system_message(context.messages());
    let rest = context
        .into_messages()
        .into_iter()
        .filter(|message| !matches!(message, Message::System(_)));
    let messages = match head {
        Some(head) => std::iter::once(Message::System(head)).chain(rest).collect(),
        None => rest.collect(),
    };
    TranscriptContext::from_normalized_messages(messages)
}

/// Keep later system messages in place when the model accepts them; otherwise collapse them.
#[must_use]
pub fn resolve_transcript(
    context: TranscriptContext,
    supports_mid_convo_system_messages: Option<bool>,
) -> TranscriptContext {
    if supports_mid_convo_system_messages == Some(true) {
        context
    } else {
        collapse_system_messages(context)
    }
}

/// Strip executable and display-only fields from a tool before transcript
/// comparison or persistence. The TS round-trips `parameters` through JSON,
/// which drops `TypeBox`'s non-enumerable markers, so only the wire JSON is kept.
#[must_use]
pub fn to_tool_declaration(tool: &Tool) -> Tool {
    Tool {
        name: tool.name.clone(),
        description: tool.description.clone(),
        parameters: ToolSchema::from(tool.parameters.json().clone()),
        constrained_sampling: tool.constrained_sampling.clone(),
    }
}

/// JSON equality that, like comparing `JSON.stringify` output, is sensitive
/// to object key order.
fn json_equal_ordered(left: &JsonValue, right: &JsonValue) -> bool {
    match (left, right) {
        (JsonValue::Object(left), JsonValue::Object(right)) => {
            left.len() == right.len()
                && left.iter().zip(right).all(
                    |((left_key, left_value), (right_key, right_value))| {
                        left_key == right_key && json_equal_ordered(left_value, right_value)
                    },
                )
        }
        (JsonValue::Array(left), JsonValue::Array(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| json_equal_ordered(left, right))
        }
        _ => left == right,
    }
}

/// Whether two tools declare the same interface to the model: equal
/// serialized declarations (key order included).
#[must_use]
pub fn declarations_equal(left: &Tool, right: &Tool) -> bool {
    left.name == right.name
        && left.description == right.description
        && json_equal_ordered(left.parameters.json(), right.parameters.json())
        && left.constrained_sampling == right.constrained_sampling
}

/// Tool changes between two complete tool states.
#[derive(Debug, Clone, PartialEq)]
pub struct ToolStateChanges {
    pub tools_added: Vec<Tool>,
    pub tools_removed: Vec<ToolReference>,
}

/// Compare two complete tool states. A changed definition is a removal followed by an addition.
#[must_use]
pub fn get_tool_state_changes(previous: &[Tool], current: &[Tool]) -> ToolStateChanges {
    let previous_tools: IndexMap<&str, &Tool> = previous
        .iter()
        .map(|tool| (tool.name.as_str(), tool))
        .collect();
    let current_tools: IndexMap<&str, &Tool> = current
        .iter()
        .map(|tool| (tool.name.as_str(), tool))
        .collect();
    ToolStateChanges {
        tools_added: current
            .iter()
            .filter(|tool| {
                previous_tools
                    .get(tool.name.as_str())
                    .is_none_or(|previous_tool| !declarations_equal(previous_tool, tool))
            })
            .map(to_tool_declaration)
            .collect(),
        tools_removed: previous
            .iter()
            .filter(|tool| {
                current_tools
                    .get(tool.name.as_str())
                    .is_none_or(|current_tool| !declarations_equal(tool, current_tool))
            })
            .map(|tool| ToolReference {
                name: tool.name.clone(),
            })
            .collect(),
    }
}

/// Every definition referenced by transcript tool state, in first-declaration order.
#[must_use]
pub fn get_declared_tools<M: TranscriptMessage>(messages: &[M]) -> Vec<Tool> {
    let mut definitions: IndexMap<&str, &Tool> = IndexMap::new();
    for message in messages {
        let Some(message) = message.as_system_message() else {
            continue;
        };
        for tool in message.tools_added.iter().flatten() {
            definitions.insert(&tool.name, tool);
        }
    }
    definitions.into_values().cloned().collect()
}

/// Whether a tool name was declared twice with different definitions.
#[deprecated(
    note = "No built-in transport needs this anymore: Anthropic expresses redefinitions with inline \
            `tool_definition` blocks. Kept for API compatibility."
)]
#[must_use]
pub fn has_tool_redefinitions<M: TranscriptMessage>(messages: &[M]) -> bool {
    let mut declared: IndexMap<&str, &Tool> = IndexMap::new();
    for message in messages {
        let Some(message) = message.as_system_message() else {
            continue;
        };
        for tool in message.tools_added.iter().flatten() {
            if let Some(previous) = declared.get(tool.name.as_str()) {
                if !declarations_equal(previous, tool) {
                    return true;
                }
            }
            declared.insert(&tool.name, tool);
        }
    }
    false
}

/// Whether tool history contains a removal or same-name redeclaration that an
/// addition-only transport cannot replay.
#[must_use]
pub fn has_non_additive_tool_changes<M: TranscriptMessage>(messages: &[M]) -> bool {
    let mut declared: std::collections::HashSet<&str> = std::collections::HashSet::new();
    for message in messages {
        let Some(message) = message.as_system_message() else {
            continue;
        };
        if message
            .tools_removed
            .as_ref()
            .is_some_and(|removed| !removed.is_empty())
        {
            return true;
        }
        for tool in message.tools_added.iter().flatten() {
            if !declared.insert(&tool.name) {
                return true;
            }
        }
    }
    false
}

/// Where a request sends its tool declarations.
#[derive(Debug, Clone, PartialEq)]
pub struct TranscriptTools {
    /// Tools sent in the top-level request field.
    pub request_tools: Vec<Tool>,
    /// Whether later system messages carry their own `tools_added` as in-place
    /// additions. When false, `request_tools` already holds the complete current tool set.
    pub anchors_additions: bool,
}

/// Split tool declarations between the top-level request field and in-place
/// additions. Transports that can anchor additions at a system message keep
/// the initial tools at the top and load later ones where they appear; that
/// only works when no tool was removed or redeclared, so everything else sends
/// the current tool list.
#[must_use]
pub fn resolve_transcript_tools<M: TranscriptMessage>(
    messages: &[M],
    supports_tool_additions: bool,
) -> TranscriptTools {
    let anchors_additions = supports_tool_additions && !has_non_additive_tool_changes(messages);
    TranscriptTools {
        request_tools: if anchors_additions {
            get_initial_system_message(messages)
                .and_then(|message| message.tools_added.clone())
                .unwrap_or_default()
        } else {
            get_current_tools(messages)
        },
        anchors_additions,
    }
}

#[cfg(test)]
mod tests;
