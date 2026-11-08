//! The RPC mode's typed failures. Each Display is the exact wire `error`
//! text the TS `rpc-mode.ts` handlers answer; `handle_command` renders a
//! command failure once, into the response frame.

use std::path::PathBuf;

use eukhe_ai::utils::diagnostics::Thrown;
use eukhe_chord::json::JsonError;
use eukhe_core::durable::cvar_agent::CvarLineError;
use eukhe_core::durable::{ForkError, SessionCommandError};
use eukhe_durable::session::SessionError;

use super::session::RpcEngineError;
use crate::compaction::durable::ManualCompactionError;
use crate::error_chain::ErrorChain;

/// The valid thinking-level wire names (TS `ThinkingLevel`).
pub(crate) const THINKING_LEVELS: &[&str] =
    &["off", "minimal", "low", "medium", "high", "xhigh", "max"];

/// The busy refusal of a prompt without a `streamingBehavior` (TS
/// `AgentSession.prompt`).
const PROMPT_WHILE_BUSY: &str =
    "Agent is already processing. Specify streamingBehavior ('steer' or 'followUp') to queue the message.";

/// The text a durable compaction that ended without a result answers.
const COMPACTION_CANCELLED: &str = "Compaction cancelled";

/// The bash gap text: the in-process bash executor is not ported to the
/// Rust session engine yet (TS `AgentSession.executeBash`); the
/// daemon-attached transport serves the command over the worker's bash
/// slot.
const BASH_BACKEND_GAP: &str = "Bash execution requires the session bash executor, which is not linked into the in-process RPC transport yet; the daemon-attached RPC transport serves it";

/// A failed read of the main conversation's live or inbox document.
#[derive(Debug, thiserror::Error)]
pub(crate) enum DocReadError {
    #[error(transparent)]
    Session(#[from] SessionError),
    #[error(transparent)]
    Decode(#[from] JsonError),
}

/// A failed whole-session lifecycle step of the RPC connection (startup,
/// replacement).
#[derive(Debug, thiserror::Error)]
pub enum RpcSessionError {
    /// A signal exit began: every replacement refuses.
    #[error("A signal exit is in progress")]
    SignalExitInProgress,
    /// The composition root could not open the session.
    #[error(transparent)]
    Engine(#[from] RpcEngineError),
    /// The goal read, the settle, or the event pump attach failed.
    #[error(transparent)]
    Session(#[from] SessionError),
}

/// Why the RPC mode could not start serving. Display is the exact text
/// the CLI printed before the typed errors (the start failure's own
/// text; the seed failure's chain, `anyhow`'s `{:#}`).
#[derive(Debug, thiserror::Error)]
pub enum RpcModeError {
    /// The startup session cannot open (before any frame is written).
    #[error("{0}")]
    Start(#[source] RpcSessionError),
    /// The CLI goal or autonomous seed failed.
    #[error("{}", ErrorChain(.0))]
    Seed(#[source] SessionError),
}

/// One failed RPC command; Display is the response's `error` text.
#[derive(Debug, thiserror::Error)]
pub(crate) enum RpcCommandError {
    /// A required payload field is absent or mistyped.
    #[error("{command} requires {field}")]
    MissingField {
        command: String,
        field: &'static str,
    },
    #[error("Invalid thinking level: expected a string")]
    ThinkingLevelNotString,
    #[error("Invalid thinking level \"{level}\". Valid values: {}", THINKING_LEVELS.join(", "))]
    UnknownThinkingLevel { level: String },
    #[error("Invalid queue mode \"{mode}\". Valid values: all, one-at-a-time")]
    UnknownQueueMode { mode: String },
    #[error("Model not found: {provider}/{model_id}")]
    ModelNotFound { provider: String, model_id: String },
    /// A prompt without a `streamingBehavior` reached a busy conversation.
    #[error("{PROMPT_WHILE_BUSY}")]
    PromptWhileBusy {
        #[source]
        source: SessionError,
    },
    /// An admitted session command failed (its failure row is committed).
    #[error(transparent)]
    SessionCommand(#[from] SessionCommandError),
    /// The admitted `/compact` task failed: the durable task's recorded
    /// error message.
    #[error("{message}")]
    CompactionFailed { message: String },
    /// The admitted `/compact` task was aborted: its recorded reason.
    #[error("{}", reason.as_deref().unwrap_or(COMPACTION_CANCELLED))]
    CompactionAborted { reason: Option<String> },
    /// The admitted `/compact` task was orphaned: its recorded reason.
    #[error("{reason}")]
    CompactionOrphaned { reason: String },
    #[error(transparent)]
    Compaction(#[from] ManualCompactionError),
    #[error("{source:#}")]
    Refine {
        #[source]
        source: anyhow::Error,
    },
    /// A settings default write failed or a higher layer shadows it.
    #[error("{source:#}")]
    Settings {
        #[source]
        source: anyhow::Error,
    },
    #[error("{source:#}")]
    Export {
        #[source]
        source: anyhow::Error,
    },
    #[error("Cron jobs require daemon mode")]
    CronRequiresDaemon,
    #[error("Heartbeats require daemon mode")]
    HeartbeatsRequireDaemon,
    #[error("Agent messaging requires daemon mode")]
    AgentMessagingRequiresDaemon,
    #[error("{BASH_BACKEND_GAP}")]
    BashBackendGap,
    #[error("Unknown active session: {id}")]
    UnknownActiveSession { id: String },
    #[error("Unknown command: {command}")]
    UnknownCommand { command: String },
    /// The fork entry is not a user message of the session (TS
    /// `runtimeHost.fork`).
    #[error("Invalid entry ID for forking")]
    InvalidForkEntry,
    #[error("Cannot clone session: no current entry selected")]
    CloneWithoutEntries,
    #[error("Session storage {} has no parent", dir.display())]
    StorageWithoutParent { dir: PathBuf },
    #[error("Session name cannot be empty")]
    EmptySessionName,
    #[error("Cannot export an in-memory session")]
    ExportInMemory,
    #[error(transparent)]
    Models(Thrown),
    #[error(transparent)]
    Cvar(#[from] CvarLineError),
    #[error(transparent)]
    Fork(#[from] ForkError),
    #[error(transparent)]
    Serialize(#[from] serde_json::Error),
    #[error(transparent)]
    DocRead(#[from] DocReadError),
    #[error(transparent)]
    Lifecycle(#[from] RpcSessionError),
    #[error(transparent)]
    Session(#[from] SessionError),
}

impl RpcCommandError {
    /// A required payload field of `command` is absent or mistyped.
    pub(crate) fn missing(command: &str, field: &'static str) -> Self {
        Self::MissingField {
            command: command.to_string(),
            field,
        }
    }
}
