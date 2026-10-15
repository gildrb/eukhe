//! The eukhe agent on the durable Harness (`eukhe-durable`): session open,
//! model collection, settings source, execution environments, and the eukhe
//! extensions (`eukhe.prompt`, `eukhe.rlm`, `eukhe.optchat`, `eukhe.goals`,
//! `eukhe.children`). Each extension module exposes
//! `extension(deps: &Arc<HostDeps>) -> Arc<Extension>`; `registry` installs
//! them in order.

mod admission_gate;
pub mod bounded_output;
pub mod branch_summary;
pub mod children;
mod codemode;
pub mod compaction;
mod deps;
mod digest;
mod discovery;
pub mod documents;
mod entries;
mod env;
mod export;
mod fork;
pub mod goals;
mod import;
mod main_conversation;
pub mod messages;
mod models;
pub mod observe;
mod open;
pub mod optchat;
mod prompt;
mod registry;
mod retry_outcome;
pub mod rlm;
pub(crate) mod session_commands;
mod settings;
mod staging;
mod tool_contract;

pub use admission_gate::AdmissionStateSink;
pub use deps::{
    HarnessCell, HostCall, HostCallHandler, HostDeps, HostRequestRegistry, JobSettledSink,
    LateAgentMessageSink, McpLogin, ModelRequest, OpenedSession, ParentLink, PromptConfig,
    ServiceStart, ServiceStop, SessionConfig, SessionRole, SessionStorage, SummaryDeltaSink,
    TurnWait, TurnWaitSink,
};
pub use discovery::{
    list_sessions, most_recent_session_for_cwd, read_main_transcript, read_session_cwd,
    read_session_document, resolve_session, DiscoveryError, MainTranscript, ResolvedListing,
    SessionListing, SessionLocation,
};
pub use entries::{
    bash_entry_draft, bash_entry_text, custom_entry_content, custom_entry_draft, input_entry,
    is_display_only_custom_type, is_input_entry, BashEntryData, BranchSummaryData, CustomEntryData,
    CustomStateData, BASH_ENTRY, BRANCH_SUMMARY_ENTRY, COMPACTION_SUMMARY_ENTRY, CUSTOM_ENTRY,
    CUSTOM_STATE_ENTRY,
};
pub use env::env_factory;
pub(crate) use export::read_export_data;
pub use export::{export_header, export_rows, ExportRows};
pub use fork::{
    fork_main_conversation, fork_session, fork_session_conversation, ForkError, ForkPoint,
    ForkedSession,
};
pub use import::{import_legacy_session, ImportError, ImportReport};
pub use main_conversation::{
    main_conversation, main_conversation_id, set_main_conversation, SessionState, SESSION_DOC,
};
pub use models::provider::{ProviderRuntime, ProviderWireEvent};
pub use models::{
    compose_models_json, create_models, resolve_session_model, ModelsError, ResolvedModel,
};
pub use open::{open_session, session_artifact_dir_for_log, EukheSession, OpenError};
pub use prompt::{section_keys, PROMPT_EXTENSION};
pub use registry::create_eukhe_registry;
pub use session_commands::{
    classify_session_command, commit_session_command_echo, commit_session_command_failure,
    execute_session_command, SessionCommand, SessionCommandName, SessionCommandOutcome,
};
pub use settings::{harness_settings, thinking_level, EukheSettings};
pub use staging::{sweep_stale_staging_dirs, StagingSweep};
