//! The eukhe agent on the durable Harness (`eukhe-durable`): session open,
//! model collection, settings source, execution environments, and the eukhe
//! extensions (`eukhe.prompt`, `eukhe.rlm`, `eukhe.optchat`, `eukhe.goals`,
//! `eukhe.children`). Each extension module exposes
//! `extension(deps: &Arc<HostDeps>) -> Arc<Extension>`; `registry` installs
//! them in order.

pub mod children;
pub mod compaction;
mod deps;
mod digest;
mod discovery;
mod entries;
mod env;
mod fork;
pub mod goals;
mod import;
mod main_conversation;
mod models;
pub mod observe;
mod open;
pub mod optchat;
mod prompt;
mod registry;
pub mod rlm;
mod session_commands;
mod settings;

pub use deps::{
    HarnessCell, HostCall, HostCallHandler, HostDeps, HostRequestRegistry, LateAgentMessageSink,
    ModelRequest, OpenedSession, ParentLink, PromptConfig, ServiceStart, ServiceStop,
    SessionConfig, SessionRole, SessionStorage, SummaryDeltaSink, TurnWait, TurnWaitSink,
};
pub use discovery::{
    list_sessions, most_recent_session_for_cwd, read_main_transcript, read_session_cwd,
    read_session_document, resolve_session, DiscoveryError, MainTranscript, ResolvedListing,
    SessionListing, SessionLocation,
};
pub use entries::{
    bash_entry_draft, bash_entry_text, custom_entry_content, custom_entry_draft, input_row_draft,
    is_display_only_custom_type, BashEntryData, BranchSummaryData, CustomEntryData,
    CustomStateData, BASH_ENTRY, BRANCH_SUMMARY_ENTRY, COMPACTION_SUMMARY_ENTRY, CUSTOM_ENTRY,
    CUSTOM_STATE_ENTRY,
};
pub use env::env_factory;
pub use fork::{fork_main_conversation, fork_session, ForkError, ForkPoint, ForkedSession};
pub use import::{import_legacy_session, ImportError, ImportReport};
pub use main_conversation::{
    main_conversation, main_conversation_id, set_main_conversation, SessionState, SESSION_DOC,
};
pub use models::provider::{ProviderRuntime, ProviderWireEvent};
pub use models::{create_models, resolve_session_model, ModelsError, ResolvedModel};
pub use open::{open_session, EukheSession, OpenError};
pub use prompt::{section_keys, PROMPT_EXTENSION};
pub use registry::create_eukhe_registry;
pub use session_commands::{
    classify_session_command, execute_session_command, SessionCommand, SessionCommandName,
    SessionCommandOutcome,
};
pub use settings::{harness_settings, thinking_level, EukheSettings};
