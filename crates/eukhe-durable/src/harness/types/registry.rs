//! The read side of a registry (TS `RegistryReader`, the entries of
//! `RegistrySnapshot`) and the built-in task set.

use std::sync::Arc;

use super::extension::{Extension, PromptSection};
use super::tools::ToolRegistration;
pub use crate::harness::registry::RegistrySnapshot;
use crate::session::Unsubscribe;
use crate::tasks::AnyTask;

/// One installed tool with its extension.
#[derive(Debug, Clone)]
pub struct InstalledTool {
    pub extension: Arc<Extension>,
    pub tool: Arc<ToolRegistration>,
}

/// One installed section with its extension.
#[derive(Debug, Clone)]
pub struct InstalledSection {
    pub extension: Arc<Extension>,
    pub section: Arc<PromptSection>,
}

/// Built-in task definitions every registry holds (TS `BUILTIN_TASKS`, in
/// this order); they are not an extension and cannot be removed or
/// replaced.
#[derive(Debug, Clone)]
pub(crate) struct BuiltinTasks {
    /// `pi.generation`.
    pub(crate) generation: AnyTask,
    /// `pi.tool`.
    pub(crate) tool: AnyTask,
    /// `pi.compaction`.
    pub(crate) compaction: AnyTask,
}

impl BuiltinTasks {
    /// `GenerationTask`, `ToolTask`, and `CompactionTask`.
    pub(crate) fn new() -> Self {
        Self {
            generation: crate::harness::generation::GENERATION_TASK.erase(),
            tool: crate::harness::tool::TOOL_TASK.erase(),
            compaction: crate::harness::compaction::COMPACTION_TASK.erase(),
        }
    }

    /// The built-ins in registry order.
    pub(crate) fn to_vec(&self) -> Vec<AnyTask> {
        vec![
            self.generation.clone(),
            self.tool.clone(),
            self.compaction.clone(),
        ]
    }
}

/// Read side of a registry consumed by a Harness (TS `RegistryReader`).
///
/// `snapshot()` returns the immutable current state; `subscribe()` registers
/// a listener the implementation calls synchronously after every
/// publication, which wakes the scheduler to reconsider blocked tasks. The
/// returned handle removes the listener.
pub trait RegistryReader: Send + Sync {
    /// Immutable view of the whole current registry.
    fn snapshot(&self) -> RegistrySnapshot;
    /// Call `listener` after every publication.
    fn subscribe(&self, listener: Arc<dyn Fn() + Send + Sync>) -> Unsubscribe;
}
