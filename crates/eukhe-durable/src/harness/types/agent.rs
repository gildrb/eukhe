//! A conversation's stored agent choices and their resolution (TS
//! `ModelRef`, `AgentState`, `AgentChange`, `Agent`, `EnvTarget`).

use std::fmt;
use std::sync::Arc;

use eukhe_types::pi_ai::ModelThinkingLevel;
use serde::{Deserialize, Serialize};

use super::extension::{Extension, PromptSection};
use super::tools::ToolRegistration;
use crate::types::{ConversationId, DocumentReader};

/// Provider and model ID resolved through pi-ai `Models`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelRef {
    pub provider: String,
    pub model_id: String,
}

/// Stored extension selection: an array selects exactly these extensions,
/// in order; an object edits the host default selection.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum ExtensionSelection {
    /// `string[]`.
    Exactly(Vec<String>),
    /// `{ add?, remove? }`.
    Edit {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        add: Option<Vec<String>>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        remove: Option<Vec<String>>,
    },
}

/// Stored tool filter: an array selects exactly these names, in order; `{
/// remove }` drops names.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum ToolFilter {
    /// `string[]`.
    Exactly(Vec<String>),
    /// `{ remove }`.
    Remove { remove: Vec<String> },
}

/// Stored choices of one conversation; names, not objects. Unset fields
/// follow the host. The value of the `pi.agent` document.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct AgentState {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model: Option<ModelRef>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub thinking_level: Option<ModelThinkingLevel>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub extensions: Option<ExtensionSelection>,
    /// Filters the selected extensions' tools: the enabled tools. An array
    /// enables exactly these, in order.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tools: Option<ToolFilter>,
    /// Filters the enabled tools the model may call (`callers` includes
    /// `model`): the tools offered to it. An array offers exactly these, in
    /// order. Never widens: other tools can still call the ones it leaves
    /// out.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model_tools: Option<ToolFilter>,
    /// Rendered after every extension section, as the section
    /// `instructions`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub instructions: Option<String>,
    /// Directory within the environment's file system, passed to
    /// `HarnessOptions.env`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cwd: Option<String>,
}

/// One field of an [`AgentChange`]: TS `undefined` changes nothing, `null`
/// clears the stored field, a value replaces it.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum FieldChange<T> {
    /// `undefined`.
    #[default]
    Keep,
    /// `null`.
    Clear,
    /// A value.
    Set(T),
}

/// The `extensions` of an [`AgentChange`]: an array selects exactly these;
/// `{ add?, remove? }` edits the host default. Extensions stand for their
/// names.
#[derive(Debug, Clone)]
pub enum ExtensionsChange {
    Exactly(Vec<Arc<Extension>>),
    Edit {
        add: Option<Vec<Arc<Extension>>>,
        remove: Option<Vec<Arc<Extension>>>,
    },
}

/// The `tools` or `model_tools` of an [`AgentChange`]: an array selects
/// exactly these; `{ remove }` drops them. Tools stand for their names.
#[derive(Debug, Clone)]
pub enum ToolsChange {
    Exactly(Vec<Arc<ToolRegistration>>),
    Remove(Vec<Arc<ToolRegistration>>),
}

/// A change to `pi.agent`: a given field replaces the stored one, `Clear`
/// clears it, `Keep` changes nothing.
#[derive(Debug, Clone, Default)]
pub struct AgentChange {
    pub model: FieldChange<ModelRef>,
    pub thinking_level: FieldChange<ModelThinkingLevel>,
    pub extensions: FieldChange<ExtensionsChange>,
    pub tools: FieldChange<ToolsChange>,
    pub model_tools: FieldChange<ToolsChange>,
    pub instructions: FieldChange<String>,
    pub cwd: FieldChange<String>,
}

/// A conversation's agent resolved against a registry snapshot and the
/// settings.
#[derive(Debug, Clone)]
pub struct Agent {
    pub model: Option<ModelRef>,
    pub thinking_level: ModelThinkingLevel,
    pub extensions: Vec<Arc<Extension>>,
    /// The tools a request offers, in order: enabled, callable by the model,
    /// and selected by `model_tools`.
    pub tools: Vec<Arc<ToolRegistration>>,
    /// The tools nested calls (`execute_tool()`) resolve among, in order:
    /// enabled and callable by tools.
    pub callable: Vec<Arc<ToolRegistration>>,
    /// Extension sections, then `instructions` when set.
    pub sections: Vec<Arc<PromptSection>>,
    pub instructions: Option<String>,
    pub cwd: Option<String>,
}

/// What `HarnessOptions.env` builds an environment for.
#[derive(Clone)]
pub struct EnvTarget {
    pub conversation_id: ConversationId,
    /// The conversation's agent `cwd`.
    pub cwd: Option<String>,
    pub read: Arc<dyn DocumentReader>,
}

impl fmt::Debug for EnvTarget {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("EnvTarget")
            .field("conversation_id", &self.conversation_id)
            .field("cwd", &self.cwd)
            .finish_non_exhaustive()
    }
}
