//! The durable agent harness (`harness/`).

pub mod types;

// HarnessContracts modules.
pub mod agent;
pub mod define;
pub mod json;
pub mod provider;
pub mod registry;
#[cfg(test)]
mod tests;
pub mod usage;
pub(crate) mod util;

// HarnessCore modules.
pub(crate) mod context;
#[expect(
    clippy::module_inception,
    reason = "one TS file, one Rust module of the same name"
)]
mod harness;
pub(crate) mod inbox;
pub(crate) mod live;
pub(crate) mod output;
pub(crate) mod prompt;
pub(crate) mod scheduler;
pub(crate) mod submissions;
pub mod tool;

pub use context::order_tool_results;
pub use harness::{Conversation, ConversationEntryQuery, Harness, RootOptions};
pub use inbox::{InboxItem, InboxState, INBOX_DOC};
pub use live::{
    CompactionStatus, LiveDeferred, LiveGeneration, LiveRetry, LiveRun, LiveState, ToolSlot,
    ToolSlotStatus, LIVE_DOC,
};
pub use scheduler::{DefinitionKept, TaskAbortResult};
pub use submissions::{AbortSubmissionResult, SubmissionHandle};
pub use tool::{
    append_tool_result, harness_error, ToolTask, ToolTaskCheckpoint, ToolTaskInput, ToolTaskResult,
    TOOL_TASK,
};

// HarnessObservation modules.
pub mod events;
pub mod task_graph;
pub mod view;

pub use events::{
    watch_events, AgentEvent, AgentEventBatch, AgentEventListener, AgentEventStream, MessageChange,
    PathSegment, QueuedItem, SnapshotEvent, SnapshotRun, ToolOutputUpdate,
};
pub use task_graph::{TaskGraph, TaskGraphNode, TaskGraphState, TaskGraphWatch};
pub use view::{ConversationView, ConversationWatch};

// HarnessCompaction modules.
pub mod compaction;

pub use compaction::{
    CompactionCheckpoint, CompactionTask, RetryRequest, SummaryRequest, COMPACTION_TASK,
};

// HarnessGeneration modules.
pub mod generation;

pub use generation::{
    GenerationCheckpoint, GenerationInput, GenerationResult, GenerationTask, GENERATION_TASK,
};
