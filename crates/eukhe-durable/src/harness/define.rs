//! Constructors of extensions, tools, sections, hooks, and wraps
//! (`harness/define.ts`).

use std::sync::Arc;

use eukhe_chord::context::Context;
use futures::future::BoxFuture;

use super::types::{
    Extension, HookRegistration, PromptInput, PromptSection, ToolRegistration, Wrap,
};
use crate::session::SessionResult;
use crate::tasks::{Task, TaskValue};

/// Share an extension; the returned `Arc` is its identity.
#[must_use]
pub fn define_extension(extension: Extension) -> Arc<Extension> {
    Arc::new(extension)
}

/// Share a tool; the returned `Arc` is its identity.
#[must_use]
pub fn define_tool(tool: ToolRegistration) -> Arc<ToolRegistration> {
    Arc::new(tool)
}

/// A prompt section; tagged unless `tag` is `Some(false)`.
pub fn section<F>(key: impl Into<String>, render: F, tag: Option<bool>) -> Arc<PromptSection>
where
    F: Fn(&PromptInput, &Context) -> BoxFuture<'static, SessionResult<Option<String>>>
        + Send
        + Sync
        + 'static,
{
    Arc::new(PromptSection {
        key: key.into(),
        render: Arc::new(render),
        tag,
    })
}

/// Hook handlers for tasks with `task`'s name. `handlers` is the task's hook
/// set; its unset fields are the TS `Partial`.
#[must_use]
pub fn hook<I, S, R, H>(task: &Task<I, S, R, H>, handlers: H) -> HookRegistration
where
    I: TaskValue,
    S: TaskValue,
    R: TaskValue,
    H: Send + Sync + 'static,
{
    HookRegistration {
        task: task.definition().name().to_owned(),
        handlers: Arc::new(handlers),
    }
}

/// Wrap the tool named like `tool` wherever the wrapping extension is
/// selected.
pub fn wrap_tool<F>(tool: &ToolRegistration, wrapper: F) -> Wrap
where
    F: Fn(&Arc<ToolRegistration>) -> SessionResult<Arc<ToolRegistration>> + Send + Sync + 'static,
{
    Wrap::Tool {
        tool: tool.name.clone(),
        wrap: Arc::new(wrapper),
    }
}

/// Wrap the section `key` wherever the wrapping extension is selected.
pub fn wrap_section<F>(key: impl Into<String>, wrapper: F) -> Wrap
where
    F: Fn(&Arc<PromptSection>) -> SessionResult<Arc<PromptSection>> + Send + Sync + 'static,
{
    Wrap::Section {
        section: key.into(),
        wrap: Arc::new(wrapper),
    }
}
