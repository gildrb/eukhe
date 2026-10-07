//! Task definitions and invocation runtimes (`tasks.ts` and the task types
//! of `types.ts`: `TaskDefinition`, `Task`, `PhaseHandler`, `RunningTask`,
//! `NextTaskState`, `HookRunner`, `TaskRuntime`; the harness `AnyTask` and
//! `SettledTask`).

mod definition;
mod runtime;

pub use definition::{
    define_task, AnyTask, ErasedTaskDefinition, Migrated, PhaseHandler, Task, TaskDefinition,
    TaskInitial, TaskMigrate, TaskValue,
};
pub use runtime::{
    HookRunner, NextTaskState, RunningTask, SettledTask, TaskCommitChange, TaskRuntime,
    TaskRuntimeBackend,
};
