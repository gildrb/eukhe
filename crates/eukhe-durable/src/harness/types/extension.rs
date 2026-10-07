//! Extensions and what they bundle (TS `Extension`, `PromptSection`,
//! `PromptInput`, `HookRegistration`, `Wrap`).

use std::any::Any;
use std::fmt;
use std::sync::Arc;

use eukhe_chord::context::Context;
use eukhe_types::pi_ai::IndexMap;
use futures::future::BoxFuture;

use super::agent::Agent;
use super::tools::ToolRegistration;
use crate::env::ExecutionEnv;
use crate::session::SessionResult;
use crate::tasks::AnyTask;
use crate::types::{ConversationId, DocumentReader};

/// Input to system prompt section rendering for one request preparation.
#[derive(Clone)]
pub struct PromptInput {
    pub conversation_id: ConversationId,
    /// The request's resolution; `agent.tools` are the tools offered in this
    /// request.
    pub agent: Arc<Agent>,
    /// Built by `HarnessOptions.env` for this preparation; `None` without an
    /// environment.
    pub env: Option<Arc<dyn ExecutionEnv>>,
    /// Sections already in effect after replaying the active transcript.
    pub shown: IndexMap<String, String>,
    /// Committed document reads.
    pub read: Arc<dyn DocumentReader>,
}

impl fmt::Debug for PromptInput {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("PromptInput")
            .field("conversation_id", &self.conversation_id)
            .field("agent", &self.agent)
            .field("env", &self.env.is_some())
            .field("shown", &self.shown)
            .finish_non_exhaustive()
    }
}

/// Renders one section; `None` leaves it out.
pub type SectionRender = Arc<
    dyn Fn(&PromptInput, &Context) -> BoxFuture<'static, SessionResult<Option<String>>>
        + Send
        + Sync,
>;

/// One system prompt section; the agent's sections render in order before
/// each request.
#[derive(Clone)]
pub struct PromptSection {
    pub key: String,
    pub render: SectionRender,
    /// Default true: wrap the text as `<key>\n...\n</key>`.
    pub tag: Option<bool>,
}

impl fmt::Debug for PromptSection {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("PromptSection")
            .field("key", &self.key)
            .field("tag", &self.tag)
            .finish_non_exhaustive()
    }
}

/// One hook handler set of a task: a value of the task's hook type `H`
/// (TS `HooksOf<K>`), such as `ToolHooks`.
pub type HookHandlers = Arc<dyn Any + Send + Sync>;

/// Built by `hook()`; matches tasks by name.
#[derive(Clone)]
pub struct HookRegistration {
    pub task: String,
    pub handlers: HookHandlers,
}

impl fmt::Debug for HookRegistration {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("HookRegistration")
            .field("task", &self.task)
            .finish_non_exhaustive()
    }
}

/// A pure tool wrapper; an error drops the tool and is reported.
pub type ToolWrapper =
    Arc<dyn Fn(&Arc<ToolRegistration>) -> SessionResult<Arc<ToolRegistration>> + Send + Sync>;

/// A pure section wrapper; an error drops the section and is reported.
pub type SectionWrapper =
    Arc<dyn Fn(&Arc<PromptSection>) -> SessionResult<Arc<PromptSection>> + Send + Sync>;

/// Built by `wrap_tool()` and `wrap_section()`; targets a tool name or a
/// section key.
#[derive(Clone)]
pub enum Wrap {
    Tool {
        tool: String,
        wrap: ToolWrapper,
    },
    Section {
        section: String,
        wrap: SectionWrapper,
    },
}

impl fmt::Debug for Wrap {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Tool { tool, .. } => formatter
                .debug_struct("Wrap::Tool")
                .field("tool", tool)
                .finish_non_exhaustive(),
            Self::Section { section, .. } => formatter
                .debug_struct("Wrap::Section")
                .field("section", section)
                .finish_non_exhaustive(),
        }
    }
}

/// Named bundle of code; installed in a registry and selected by
/// conversations by name. Identity is the `Arc<Extension>` that
/// `define_extension()` returns. TS optional arrays are empty when absent.
#[derive(Debug, Clone, Default)]
pub struct Extension {
    pub name: String,
    pub tools: Vec<Arc<ToolRegistration>>,
    pub sections: Vec<Arc<PromptSection>>,
    pub hooks: Vec<HookRegistration>,
    /// Apply where this extension is selected, in order.
    pub wraps: Vec<Wrap>,
    /// Resolved by name for every task, whichever conversations select this
    /// extension.
    pub tasks: Vec<AnyTask>,
}

impl Extension {
    /// An empty extension named `name`.
    #[must_use]
    pub fn named(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            ..Self::default()
        }
    }
}
